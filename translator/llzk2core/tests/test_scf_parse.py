import pytest
from llzk_dialects.scf import SCFYield, SCFCondition, SCFIf, SCFFor, SCFWhile, _contains_function_call
from llzk_dialects.core import SSAVar, GlobalVariable, Type, TranslationContext, LoopIndexedName
from llzk_dialects.felt import FeltConst, FeltBinary
from llzk_dialects.bool import BoolCmp
from llzk_dialects.constrain import ConstrainEq
from llzk_dialects.function import FunctionCall


class TestSCF:

    # ── SCFYield ──────────────────────────────────────────────────────────────

    def test_yield_empty(self):
        op = SCFYield.parse("scf.yield")
        assert op.operands == []
        assert op.types == []

    def test_yield_with_values(self):
        op = SCFYield.parse("scf.yield %a, %b : !felt.type, !felt.type")
        assert op.operands == [SSAVar("%a"), SSAVar("%b")]
        assert op.types == [Type("!felt.type"), Type("!felt.type")]

    def test_yield_single(self):
        op = SCFYield.parse("  scf.yield %r : index  ")
        assert op.operands == [SSAVar("%r")]

    def test_yield_match(self):
        assert SCFYield.match("scf.yield") is True
        assert SCFYield.match("scf.condition(%c)") is False

    # ── SCFCondition ──────────────────────────────────────────────────────────

    def test_condition_no_args(self):
        op = SCFCondition.parse("scf.condition(%cond)")
        assert op.condition == SSAVar("%cond")
        assert op.args == []

    def test_condition_with_args(self):
        op = SCFCondition.parse(
            "scf.condition(%ok) %a, %b : !felt.type, !felt.type"
        )
        assert op.condition == SSAVar("%ok")
        assert op.args == [SSAVar("%a"), SSAVar("%b")]

    def test_condition_match(self):
        assert SCFCondition.match("scf.condition(%c)") is True
        assert SCFCondition.match("scf.yield") is False

    # ── SCFIf (BlockOperation) ────────────────────────────────────────────────

    def _simple_parse_fn(self, start, end):
        ops = []
        for i in range(start, end):
            line = self.lines[i].strip()
            if not line or line in ("}", "} else {", "else {"):
                continue
            if SCFYield.match(line):
                ops.append(SCFYield.parse(line))
            elif FeltConst.match(line):
                ops.append(FeltConst.parse(line))
            elif ConstrainEq.match(line):
                ops.append(ConstrainEq.parse(line))
        return ops

    def test_if_no_else(self):
        self.lines = [
            "scf.if %cond {",
            "constrain.eq %a, %b",
            "}",
        ]
        op, next_cur = SCFIf.parse(self.lines, 0, self._simple_parse_fn)
        assert op.condition == SSAVar("%cond")
        assert len(op.then_body) == 1
        assert op.else_body is None
        assert next_cur == 3

    def test_if_with_else(self):
        self.lines = [
            "scf.if %cond {",
            "constrain.eq %a, %b",
            "} else {",
            "constrain.eq %c, %d",
            "}",
        ]
        op, next_cur = SCFIf.parse(self.lines, 0, self._simple_parse_fn)
        assert len(op.then_body) == 1
        assert op.else_body is not None
        assert len(op.else_body) == 1

    def test_if_with_results(self):
        self.lines = [
            "%r = scf.if %cond : !felt.type {",
            "scf.yield %a : !felt.type",
            "} else {",
            "scf.yield %b : !felt.type",
            "}",
        ]
        op, _ = SCFIf.parse(self.lines, 0, self._simple_parse_fn)
        assert op.results == [SSAVar("%r")]

    def test_if_match(self):
        assert SCFIf.match("scf.if %c {") is True
        assert SCFIf.match("scf.for %iv = %lb to %ub step %s {") is False

    # ── SCFFor (BlockOperation) ───────────────────────────────────────────────

    def test_for_basic(self):
        self.lines = [
            "scf.for %iv = %lb to %ub step %s {",
            "scf.yield",
            "}",
        ]
        op, next_cur = SCFFor.parse(self.lines, 0, self._simple_parse_fn)
        assert op.iv == SSAVar("%iv")
        assert op.lb == SSAVar("%lb")
        assert op.ub == SSAVar("%ub")
        assert op.step == SSAVar("%s")
        assert op.iter_args == []
        assert next_cur == 3

    def test_for_iter_args(self):
        self.lines = [
            "scf.for %iv = %lb to %ub step %s iter_args(%acc = %init) {",
            "scf.yield %acc : !felt.type",
            "}",
        ]
        op, _ = SCFFor.parse(self.lines, 0, self._simple_parse_fn)
        assert len(op.iter_args) == 1
        assert op.iter_args[0][0] == SSAVar("%acc")
        assert op.iter_args[0][1] == SSAVar("%init")

    def test_for_match(self):
        assert SCFFor.match("scf.for %iv = %lb to %ub step %s {") is True
        assert SCFFor.match("scf.while (%a = %b) {") is False

    def test_for_to_core_repeat(self):
        # Verify that scf.for translates to a bounded "repeat" block: the
        # induction variable is initialised once before the loop and advanced
        # by 'step' at the end of the (single, not unrolled) body.
        lines = [
            "scf.for %iv = %c0 to %c2 step %c1 {",
            "%x = felt.add %iv, %arg0 : !felt.type, !felt.type",
            "}",
        ]

        def parse_fn(start, end):
            ops = []
            for i in range(start, end):
                line = lines[i].strip()
                if not line or line == "}":
                    continue
                if FeltBinary.match(line):
                    ops.append(FeltBinary.parse(line))
            return ops

        op, _ = SCFFor.parse(lines, 0, parse_fn)
        ctx = TranslationContext()
        ctx.var2const["%c0"] = 0
        ctx.var2const["%c2"] = 3
        ctx.var2const["%c1"] = 1

        out = list(op.to_core(ctx))
        assert out == [
            "%iv = 0",
            "repeat 3 {",
            "%x = felt.add %iv %arg0",
            "%iv = felt.add %iv 1",
            "}",
        ]
        # Induction variable is not in var2const after the loop.
        assert "%iv" not in ctx.var2const

    def test_for_to_core_unrolls_when_body_has_call(self):
        # A body containing a function.call is unrolled into one literal
        # copy per iteration instead of a single generic "repeat" block —
        # so a subcomponent instantiated inside the loop can be named
        # per-iteration (LoopIndexedName, resolved via ctx.unroll_index)
        # instead of sharing one bare name across every iteration.
        call = FunctionCall([SSAVar("%r")], GlobalVariable("@Sub"), [SSAVar("%iv")], None)
        call._member_hint = LoopIndexedName("last")
        op = SCFFor([], SSAVar("%iv"), SSAVar("%c0"), SSAVar("%c2"), SSAVar("%c1"), [], [call])

        ctx = TranslationContext()
        ctx.var2const["%c0"] = 0
        ctx.var2const["%c2"] = 2
        ctx.var2const["%c1"] = 1
        ctx.llzk_func2core["@Sub"] = "Sub"
        ctx.core_func2args["Sub"] = ([], [("@out", Type("!felt.type"))])

        out = list(op.to_core(ctx))
        assert out == [
            "%iv = 0",
            "call Sub(%iv) to last#0.out",
            "%iv = 1",
            "call Sub(%iv) to last#1.out",
        ]
        assert not any("repeat" in line for line in out)
        assert "%iv" not in ctx.var2const
        # ctx.unroll_index is restored after the loop.
        assert ctx.unroll_index is None

    def test_for_to_core_missing_bound_raises(self):
        lines = [
            "scf.for %iv = %c0 to %c2 step %c1 {",
            "scf.yield",
            "}",
        ]
        op, _ = SCFFor.parse(lines, 0, lambda s, e: [])
        ctx = TranslationContext()
        ctx.var2const["%c0"] = 0
        # %c2 deliberately missing — must raise
        with pytest.raises(AssertionError):
            list(op.to_core(ctx))

    # ── SCFWhile (BlockOperation) ─────────────────────────────────────────────

    def _while_parse_fn(self, start, end):
        ops = []
        for i in range(start, end):
            line = self.lines[i].strip()
            if not line or line in ("}", "do {"):
                continue
            if SCFYield.match(line):
                ops.append(SCFYield.parse(line))
            elif SCFCondition.match(line):
                ops.append(SCFCondition.parse(line))
        return ops

    def test_while_basic(self):
        self.lines = [
            "scf.while (%arg = %init) : (index) -> (index) {",
            "scf.condition(%cond) %arg",
            "}",
            "do {",
            "scf.yield %arg : index",
            "}",
        ]
        op, next_cur = SCFWhile.parse(self.lines, 0, self._while_parse_fn)
        assert op.init_args == [(SSAVar("%arg"), SSAVar("%init"))]
        assert len(op.before_body) == 1
        assert len(op.after_body) == 1
        assert next_cur == 6

    def test_while_with_after_block_args(self):
        self.lines = [
            'scf.while (%arg0: !felt.type<"bn128"> = %v0, %arg1: !felt.type<"bn128"> = %v1)'
            ' : (!felt.type<"bn128">, !felt.type<"bn128">) -> (!felt.type<"bn128">, !felt.type<"bn128">) {',
            '^bb0(%arg0: !felt.type<"bn128">, %arg1: !felt.type<"bn128">):',
            'scf.condition(%cond) %arg0, %arg1',
            '} do {',
            '^bb0(%arg2: !felt.type<"bn128">, %arg3: !felt.type<"bn128">):',
            'scf.yield %arg2, %arg3 : !felt.type<"bn128">, !felt.type<"bn128">',
            '}',
        ]
        op, next_cur = SCFWhile.parse(self.lines, 0, self._while_parse_fn)
        assert len(op.after_args) == 2
        assert op.after_args[0] == (SSAVar('%arg2'), Type('!felt.type<"bn128">'))
        assert op.after_args[1] == (SSAVar('%arg3'), Type('!felt.type<"bn128">'))
        assert len(op.before_body) == 1
        assert len(op.after_body) == 1
        assert next_cur == 7

    def test_while_no_after_block_args(self):
        self.lines = [
            "scf.while (%arg = %init) : (index) -> (index) {",
            "scf.condition(%cond) %arg",
            "} do {",
            "scf.yield %arg : index",
            "}",
        ]
        op, next_cur = SCFWhile.parse(self.lines, 0, self._while_parse_fn)
        assert op.after_args == []

    def test_while_match(self):
        assert SCFWhile.match("scf.while (%a = %b) {") is True
        assert SCFWhile.match("scf.if %c {") is False

    def _counting_while(self, call=None):
        """
        A minimal 2-iteration counting while loop (mirrors
        ternary_concrete.mlir's Num2Bits_16_325-instantiating loop, stripped
        to just the counter): %arg1 starts at 0, increments by 1 each pass,
        stops once %arg1 >= 2. `call`, if given, is spliced into after_body
        so _contains_function_call detects it.
        """
        after_body = [FeltConst(SSAVar("%c1"), 1)]
        if call is not None:
            after_body.append(call)
        after_body += [
            FeltBinary(SSAVar("%next"), "felt.add", SSAVar("%arg1"), SSAVar("%c1"), []),
            SCFYield([SSAVar("%next")], [Type("index")]),
        ]
        before_body = [
            FeltConst(SSAVar("%c2"), 2),
            BoolCmp(SSAVar("%cond"), "lt", SSAVar("%arg1"), SSAVar("%c2")),
            SCFCondition(SSAVar("%cond"), [SSAVar("%arg1")], [Type("index")]),
        ]
        return SCFWhile(
            [], [(SSAVar("%arg1"), SSAVar("%c0"))], [[Type("index")], [Type("index")]],
            before_body, [(SSAVar("%arg1"), Type("index"))], after_body,
        )

    def test_while_to_core_repeat_when_no_call(self):
        # No function.call in the body: translated once, wrapped in a Core
        # "repeat" block (today's behavior, unaffected by unrolling).
        op = self._counting_while()
        ctx = TranslationContext()
        ctx.var2const["%c0"] = 0

        out = list(op.to_core(ctx))
        assert out == [
            "%arg1 = %c0",
            "repeat 2 {",
            "%c1 = 1",
            "%next = felt.add %arg1 %c1",
            "%arg1 = %next",
            "%c2 = 2",
            "%cond = bool.lt %c2 %arg1",
            "}",
        ]
        assert ctx.unroll_index is None

    def test_while_to_core_unrolls_when_body_has_call(self):
        # A call inside the after-body: unrolled into one literal copy per
        # iteration (no "repeat" wrapper), each with its own resolved
        # LoopIndexedName — mirrors ternary_concrete.mlir's
        # Num2Bits_16_325, instantiated once per while-loop iteration.
        call = FunctionCall([SSAVar("%r")], GlobalVariable("@Sub"), [SSAVar("%arg1")], None)
        call._member_hint = LoopIndexedName("last")
        op = self._counting_while(call=call)

        ctx = TranslationContext()
        ctx.var2const["%c0"] = 0
        ctx.llzk_func2core["@Sub"] = "Sub"
        ctx.core_func2args["Sub"] = ([], [("@out", Type("!felt.type"))])

        out = list(op.to_core(ctx))
        assert out == [
            "%arg1 = %c0",
            "%c1 = 1",
            "call Sub(%arg1) to last#0.out",
            "%next = felt.add %arg1 %c1",
            "%arg1 = %next",
            "%c2 = 2",
            "%cond = bool.lt %c2 %arg1",
            "%c1 = 1",
            "call Sub(%arg1) to last#1.out",
            "%next = felt.add %arg1 %c1",
            "%arg1 = %next",
            "%c2 = 2",
            "%cond = bool.lt %c2 %arg1",
        ]
        assert not any("repeat" in line for line in out)
        assert ctx.unroll_index is None

    # ── _contains_function_call ──────────────────────────────────────────────

    def test_contains_call_flat(self):
        call = FunctionCall([], GlobalVariable("@f"), [], None)
        assert _contains_function_call([call]) is True

    def test_contains_call_absent(self):
        assert _contains_function_call([FeltConst(SSAVar("%c"), 1)]) is False

    def test_contains_call_nested_in_if(self):
        call = FunctionCall([], GlobalVariable("@f"), [], None)
        inner_if = SCFIf([], SSAVar("%cond"), [], [call], None)
        assert _contains_function_call([inner_if]) is True

    def test_contains_call_nested_in_for(self):
        call = FunctionCall([], GlobalVariable("@f"), [], None)
        loop = SCFFor([], SSAVar("%iv"), SSAVar("%lb"), SSAVar("%ub"), SSAVar("%step"), [], [call])
        assert _contains_function_call([loop]) is True

    def test_contains_call_nested_in_while_after_body(self):
        call = FunctionCall([], GlobalVariable("@f"), [], None)
        while_op = SCFWhile([], [], [[], []], [SCFCondition(SSAVar("%c"), [], [])], [], [call])
        assert _contains_function_call([while_op]) is True

    def test_contains_call_sibling_branch_without_call_is_false(self):
        # A call in one sibling branch must not make an unrelated, call-free
        # branch report True.
        other_if = SCFIf([], SSAVar("%cond"), [], [FeltConst(SSAVar("%c"), 1)], None)
        assert _contains_function_call([other_if]) is False
