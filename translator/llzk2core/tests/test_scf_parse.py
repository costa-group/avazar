import pytest
from llzk_dialects.scf import (
    SCFYield, SCFCondition, SCFIf, SCFExecuteRegion, SCFFor, SCFWhile,
    _contains_function_call,
)
from llzk_dialects.core import SSAVar, GlobalVariable, Type, TranslationContext, LoopIndexedName
from llzk_dialects.felt import FeltConst, FeltBinary
from llzk_dialects.bool import BoolCmp, BoolBinary
from llzk_dialects.constrain import ConstrainEq
from llzk_dialects.function import FunctionCall
from llzk_dialects.pod import PodRead, PodNew
from llzk_dialects.core_utils import translate_assignment_core_with_ctx


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

    # ── SCFCondition.to_core ──────────────────────────────────────────────────

    def test_condition_to_core_felt(self):
        op = SCFCondition(SSAVar("%cond"), [SSAVar("%v")], [Type("!felt.type")])
        ctx = TranslationContext()
        ctx.scf_result = [SSAVar("%result")]
        lines = list(op.to_core(ctx))
        assert lines == ["%result = %v"]

    def test_condition_to_core_pod_and_felt_args(self):
        # Regression: SCFCondition.to_core used to compute type_.to_core()
        # and assert it wasn't None before calling
        # translate_assignment_core_with_ctx -- which already dispatches on
        # pod/struct/array types on its own, independent of Type.to_core()
        # (which only recognizes a felt scalar or a felt array). A
        # scf.while whose condition carries a pod-typed loop-carried value
        # (e.g. combining pods inside pods, as in
        # poseidon3_test_concrete.mlir) crashed on that dead check even
        # though the actual translation call worked fine.
        ctx = TranslationContext()
        ctx.ssa2pod_var["%pod_src"] = {"@x": ("%pod_src_@x", Type("!felt.type"))}
        op = SCFCondition(
            SSAVar("%cond"),
            [SSAVar("%pod_src"), SSAVar("%v")],
            [Type("!pod.type<[@x: !felt.type]>"), Type("!felt.type")],
        )
        ctx.scf_result = [SSAVar("%pod_result"), SSAVar("%felt_result")]
        lines = list(op.to_core(ctx))  # previously: AssertionError
        assert lines == ["%pod_result_@x = %pod_src_@x", "%felt_result = %v"]
        assert ctx.ssa2pod_var["%pod_result"]["@x"][0] == "%pod_result_@x"

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

    def test_if_to_core_yields_pod_value(self):
        # Regression: SCFYield.to_core must dispatch through
        # translate_assignment_core_with_ctx (not the plain, type-agnostic
        # helper) so a pod-typed yield — as scf.execute_region's real usage
        # requires — is handled the same way it already is for felt/array.
        self.lines = [
            "%r = scf.if %cond : !pod.type<[@x: !felt.type]> {",
            "scf.yield %a : !pod.type<[@x: !felt.type]>",
            "} else {",
            "scf.yield %b : !pod.type<[@x: !felt.type]>",
            "}",
        ]
        op, _ = SCFIf.parse(self.lines, 0, self._simple_parse_fn)
        ctx = TranslationContext()
        ctx.ssa2pod_var["%a"] = {"@x": ("%a_@x", Type("!felt.type"))}
        ctx.ssa2pod_var["%b"] = {"@x": ("%b_@x", Type("!felt.type"))}
        out = list(op.to_core(ctx))
        assert out == [
            "if (%cond == 1) {",
            "%r_@x = %a_@x",
            "}\n",
            "else {",
            "%r_@x = %b_@x",
            "}",
        ]
        assert ctx.ssa2pod_var["%r"] == {"@x": ("%r_@x", Type("!felt.type"))}

    # ── Branch-scoping regressions (poseidon3_test_concrete.mlir) ────────────
    #
    # SCFIf.to_core unconditionally translates BOTH branches (Core needs both
    # as real runtime code -- the condition is never resolved statically), so
    # a raw LLZK SSA name reused across two mutually-exclusive branches
    # (valid under SSA scoping, since only one branch executes at runtime)
    # would otherwise silently clobber ctx.ssa_to_name/ctx.ssa2pod_var/
    # ctx.var2const, which are flat, whole-translation dicts with no
    # per-branch scoping of their own. See _translate_branch's
    # scoped_branch_registrations wrapper.

    def test_if_sibling_branches_do_not_leak_ssa_to_name(self):
        # Two mutually-exclusive branches each register a PodRead's semantic
        # alias into the SAME raw SSA name ("%755", mirroring the real
        # poseidon3_test_concrete.mlir crash trace). This if declares no
        # results, so neither branch's alias should survive past it.
        then_read = PodRead(SSAVar("%755"), SSAVar("%podA"), GlobalVariable("@x"), {}, None)
        else_read = PodRead(SSAVar("%755"), SSAVar("%podB"), GlobalVariable("@y"), {}, None)
        op = SCFIf([], SSAVar("%cond"), [], [then_read], [else_read])

        ctx = TranslationContext()
        ctx.ssa2pod_var["%podA"] = {"@x": ("compA.x", Type("!felt.type"))}
        ctx.ssa2pod_var["%podB"] = {"@y": ("compB.y", Type("!felt.type"))}

        list(op.to_core(ctx))  # previously: "%755" left aliased to "compB.y"
        assert "%755" not in ctx.ssa_to_name

    def test_if_escape_hatch_preserves_declared_result_not_branch_local_temp(self):
        # The if's own declared result (%r) is computed via a branch-local
        # PodNew temporary (%tmp) in the then-branch. %r must be correctly
        # registered after the if closes; %tmp -- never referenced by
        # anything outside its own branch under valid SSA scoping -- must
        # not survive.
        then_body = [
            PodNew(SSAVar("%tmp"), {}, {"@x": Type("!felt.type")}),
            SCFYield([SSAVar("%tmp")], [Type("!pod.type<[@x: !felt.type]>")]),
        ]
        else_body = [
            SCFYield([SSAVar("%other")], [Type("!pod.type<[@x: !felt.type]>")]),
        ]
        op = SCFIf([SSAVar("%r")], SSAVar("%cond"), [Type("!pod.type<[@x: !felt.type]>")],
                   then_body, else_body)
        ctx = TranslationContext()
        ctx.ssa2pod_var["%other"] = {"@x": ("%other_@x", Type("!felt.type"))}

        list(op.to_core(ctx))

        assert ctx.ssa2pod_var["%r"] == {"@x": ("%r_@x", Type("!felt.type"))}
        assert "%tmp" not in ctx.ssa2pod_var

    def test_if_sibling_branches_do_not_leak_ssa2pod_var(self):
        # Same sibling-branch collision as above, but directly on
        # ctx.ssa2pod_var: both branches define a pod under the SAME raw
        # name ("%p") with DIFFERENT field shapes. This if declares no
        # results, so "%p" must not survive past it at all.
        then_body = [PodNew(SSAVar("%p"), {}, {"@a": Type("!felt.type")})]
        else_body = [PodNew(SSAVar("%p"), {}, {"@b": Type("!felt.type")})]
        op = SCFIf([], SSAVar("%cond"), [], then_body, else_body)
        ctx = TranslationContext()

        list(op.to_core(ctx))  # previously: "%p" left as {'@b': (...)}
        assert "%p" not in ctx.ssa2pod_var

    # ── SCFExecuteRegion (BlockOperation) ─────────────────────────────────────

    def test_execute_region_no_results(self):
        self.lines = [
            "scf.execute_region {",
            "constrain.eq %a, %b",
            "scf.yield",
            "}",
        ]
        op, next_cur = SCFExecuteRegion.parse(self.lines, 0, self._simple_parse_fn)
        assert op.results == []
        assert op.result_types == []
        assert len(op.body) == 2
        assert next_cur == 4

    def test_execute_region_single_scalar_result(self):
        self.lines = [
            "%x = scf.execute_region -> !felt.type<\"bn128\"> {",
            "scf.yield %v : !felt.type<\"bn128\">",
            "}",
        ]
        op, next_cur = SCFExecuteRegion.parse(self.lines, 0, self._simple_parse_fn)
        assert op.results == [SSAVar("%x")]
        assert op.result_types == [Type("!felt.type<\"bn128\">")]
        assert next_cur == 3

    def test_execute_region_multi_pod_result(self):
        self.lines = [
            "%34:2 = scf.execute_region -> (!pod.type<[@a: index]>, !pod.type<[@b: index]>) {",
            "scf.yield %x, %y : !pod.type<[@a: index]>, !pod.type<[@b: index]>",
            "}",
        ]
        op, next_cur = SCFExecuteRegion.parse(self.lines, 0, self._simple_parse_fn)
        assert op.results == [SSAVar("%34", 2)]
        assert op.result_types == [Type("!pod.type<[@a: index]>"), Type("!pod.type<[@b: index]>")]
        assert next_cur == 3

    def test_execute_region_match(self):
        assert SCFExecuteRegion.match("scf.execute_region {") is True
        assert SCFExecuteRegion.match("%x = scf.execute_region -> !felt.type<\"bn128\"> {") is True
        assert SCFExecuteRegion.match("scf.if %c {") is False

    def test_execute_region_to_core_no_results(self):
        self.lines = [
            "scf.execute_region {",
            "%c = felt.const 1 : !felt.type",
            "scf.yield",
            "}",
        ]
        op, _ = SCFExecuteRegion.parse(self.lines, 0, self._simple_parse_fn)
        ctx = TranslationContext()
        # No wrapper syntax at all: just the inlined body statement(s).
        assert list(op.to_core(ctx)) == ["%c = 1"]

    def test_execute_region_to_core_scalar_result(self):
        self.lines = [
            "%x = scf.execute_region -> !felt.type<\"bn128\"> {",
            "scf.yield %v : !felt.type<\"bn128\">",
            "}",
        ]
        op, _ = SCFExecuteRegion.parse(self.lines, 0, self._simple_parse_fn)
        ctx = TranslationContext()
        assert list(op.to_core(ctx)) == ["%x = %v"]

    def test_execute_region_to_core_pod_result_propagates_ssa2pod_var(self):
        self.lines = [
            "%34 = scf.execute_region -> !pod.type<[@x: !felt.type]> {",
            "scf.yield %36 : !pod.type<[@x: !felt.type]>",
            "}",
        ]
        op, _ = SCFExecuteRegion.parse(self.lines, 0, self._simple_parse_fn)
        ctx = TranslationContext()
        ctx.ssa2pod_var["%36"] = {"@x": ("%36_@x", Type("!felt.type"))}
        out = list(op.to_core(ctx))
        assert out == ["%34_@x = %36_@x"]
        assert ctx.ssa2pod_var["%34"] == {"@x": ("%34_@x", Type("!felt.type"))}

    # ── SCFFor (BlockOperation) ───────────────────────────────────────────────

    def test_for_basic(self):
        self.lines = [
            "scf.for %iv = %lb to %ub step %s {",
            "scf.yield",
            "}",
        ]
        op, next_cur = SCFFor.parse(self.lines, 0, self._simple_parse_fn)
        # %iv is cursor-tagged (SCFFor.parse's own block-arg rename) since it's
        # used as a literal ctx dict key, just like scf.while's own block args.
        assert op.iv == SSAVar("%iv_f0")
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
        assert op.iter_args[0][0] == SSAVar("%acc_f0")
        # init (the incoming value from the enclosing scope) is untouched.
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
        # %iv and %x (a body-computed result) are both cursor-tagged by
        # SCFFor.parse's own rename (mirroring SCFWhile's), since they're
        # used as literal ctx dict keys elsewhere; %arg0 is an external,
        # unbound reference and stays untouched.
        assert out == [
            "%iv_f0 = 0",
            "repeat 3 {",
            "%x_f0 = felt.add %iv_f0 %arg0",
            "%iv_f0 = felt.add %iv_f0 1",
            "}",
        ]
        # Induction variable is not in var2const after the loop.
        assert "%iv_f0" not in ctx.var2const

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
        # %arg (the while's own block arg) is cursor-tagged since it's used
        # as a literal ctx dict key; %init (the incoming value) is untouched.
        assert op.init_args == [(SSAVar("%arg_w0"), SSAVar("%init"))]
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
        # after_args' own block-arg names ("%arg2"/"%arg3" here, distinct
        # from init_args' "%arg0"/"%arg1" in this synthetic example) are also
        # cursor-tagged -- independently of init_args', since they're a
        # different raw name in this test.
        assert len(op.after_args) == 2
        assert op.after_args[0] == (SSAVar('%arg2_w0'), Type('!felt.type<"bn128">'))
        assert op.after_args[1] == (SSAVar('%arg3_w0'), Type('!felt.type<"bn128">'))
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

    def test_while_to_core_reassigned_array_loop_carried_value_uses_array_copy(self):
        # Regression test (ternary_modified_concrete.mlir): an array-typed
        # loop-carried value that is genuinely reassigned each iteration
        # (yielded back under a *different* SSA name than its own block-arg
        # name, unlike every other loop-carried value seen so far, which are
        # yielded back unchanged) must translate to array.copy, not a plain
        # "=" assignment.
        #
        # The yield-reassignment step's per-arg type must come from
        # in_types (positionally aligned with init_args, the same list
        # already used correctly for the initial assignment below) —
        # init_args' own second tuple element is the *initial-value SSAVar*,
        # not a Type. Using it as one silently mistranslated any array into
        # a scalar copy, since "array" in <ssa-name-string> almost never
        # holds true by coincidence.
        arr_type = Type("!array.type<2 x !felt.type>")
        after_body = [
            FeltConst(SSAVar("%c1"), 1),
            FeltBinary(SSAVar("%next"), "felt.add", SSAVar("%arg1"), SSAVar("%c1"), []),
            SCFYield([SSAVar("%next"), SSAVar("%newarr")], [Type("index"), arr_type]),
        ]
        before_body = [
            FeltConst(SSAVar("%c2"), 2),
            BoolCmp(SSAVar("%cond"), "lt", SSAVar("%arg1"), SSAVar("%c2")),
            SCFCondition(SSAVar("%cond"), [SSAVar("%arg1"), SSAVar("%arg2")], [Type("index"), arr_type]),
        ]
        op = SCFWhile(
            [], [(SSAVar("%arg1"), SSAVar("%c0")), (SSAVar("%arg2"), SSAVar("%init_arr"))],
            [[Type("index"), arr_type], [Type("index"), arr_type]],
            before_body, [(SSAVar("%arg1"), Type("index")), (SSAVar("%arg2"), arr_type)],
            after_body,
        )
        ctx = TranslationContext()
        ctx.var2const["%c0"] = 0

        out = list(op.to_core(ctx))
        assert "array.copy %init_arr %arg2" in out  # initial assignment (was already correct)
        assert "array.copy %newarr %arg2" in out    # per-iteration reassignment (the bug)
        assert "%arg2 = %newarr" not in out

    def _external_bound_while(self, predicate="lt", cursor=None, bound_ops=None, bound_name="%bound"):
        """
        A counting while (same +1 recurrence as _counting_while) whose
        condition is checked against `bound_name`, a variable that isn't
        defined anywhere inside the while itself -- standing in for an
        enclosing function's own parameter (mirrors
        escalarmulw4table_concrete.mlir's "arg3 < k*4"). `bound_ops`, if
        given, are extra operations prepended to before_body to compute
        `bound_name` from some other unresolved free variable (e.g. a
        felt.mul), rather than bound_name itself being the free variable.
        """
        before_body = list(bound_ops or []) + [
            BoolCmp(SSAVar("%cond"), predicate, SSAVar("%arg1"), SSAVar(bound_name)),
            SCFCondition(SSAVar("%cond"), [SSAVar("%arg1")], [Type("index")]),
        ]
        after_body = [
            FeltConst(SSAVar("%c1"), 1),
            FeltBinary(SSAVar("%next"), "felt.add", SSAVar("%arg1"), SSAVar("%c1"), []),
            SCFYield([SSAVar("%next")], [Type("index")]),
        ]
        return SCFWhile(
            [], [(SSAVar("%arg1"), SSAVar("%c0"))], [[Type("index")], [Type("index")]],
            before_body, [(SSAVar("%arg1"), Type("index"))], after_body, cursor,
        )

    def test_while_to_core_symbolic_steps_lt(self):
        # The bound ("%extern") can't be resolved via ctx.var2const: the
        # iteration count is instead computed symbolically in Core, assigned
        # to a fresh variable, and used directly as repeat's operand.
        op = self._external_bound_while(predicate="lt", cursor=7, bound_name="%extern")
        ctx = TranslationContext()
        ctx.var2const["%c0"] = 0

        out = list(op.to_core(ctx))
        assert out == [
            "%arg1 = %c0",
            "%steps_7 = felt.sub %extern 0",
            "repeat %steps_7 {",
            "%c1 = 1",
            "%next = felt.add %arg1 %c1",
            "%arg1 = %next",
            "%cond = bool.lt %extern %arg1",
            "}",
        ]

    def test_while_to_core_symbolic_steps_le(self):
        op = self._external_bound_while(predicate="le", cursor=8, bound_name="%extern")
        ctx = TranslationContext()
        ctx.var2const["%c0"] = 0

        out = list(op.to_core(ctx))
        assert out == [
            "%arg1 = %c0",
            "%steps_8_pre = felt.sub %extern 0",
            "%steps_8 = felt.add %steps_8_pre 1",
            "repeat %steps_8 {",
            "%c1 = 1",
            "%next = felt.add %arg1 %c1",
            "%arg1 = %next",
            "%cond = bool.ge %extern %arg1",  # "le" -> "bool.ge" with swapped operands
            "}",
        ]

    def test_while_to_core_symbolic_steps_setup_ops_for_expression_bound(self):
        # Mirrors escalarmulw4table_concrete.mlir's "arg1 < k*4": the bound
        # ("%bound") is itself computed from an unresolved free variable
        # ("%extern") via a felt.mul -- the operations needed to compute it
        # are translated once, before the repeat, in dependency order.
        bound_ops = [
            FeltConst(SSAVar("%four"), 4),
            FeltBinary(SSAVar("%bound"), "felt.mul", SSAVar("%extern"), SSAVar("%four"), []),
        ]
        op = self._external_bound_while(predicate="lt", cursor=9, bound_ops=bound_ops)
        ctx = TranslationContext()
        ctx.var2const["%c0"] = 0

        out = list(op.to_core(ctx))
        assert out == [
            "%arg1 = %c0",
            "%four = 4",
            "%bound = felt.mul %extern %four",
            "%steps_9 = felt.sub %bound 0",
            "repeat %steps_9 {",
            "%c1 = 1",
            "%next = felt.add %arg1 %c1",
            "%arg1 = %next",
            "%four = 4",
            "%bound = felt.mul %extern %four",
            "%cond = bool.lt %bound %arg1",
            "}",
        ]

    def test_while_to_core_bound_resolved_via_var2const_stays_concrete(self):
        # Regression coverage for the babypbk_test-style case: an external
        # free variable IS known via ctx.var2const, so the iteration count
        # is still a concrete int and a plain "repeat N {" is emitted --
        # the symbolic path is only a fallback for when it can't be.
        op = self._external_bound_while(predicate="lt", bound_name="%bound")
        ctx = TranslationContext()
        ctx.var2const["%c0"] = 0
        ctx.var2const["%bound"] = 4

        out = list(op.to_core(ctx))
        assert out[1] == "repeat 4 {"
        assert not any("steps" in line for line in out)

    def test_while_to_core_symbolic_steps_raises_when_body_has_call(self):
        # A symbolic count can't drive a Python "for i in range(steps)"
        # unroll -- exactly the wall escalarmulw4table_concrete.mlir's while
        # (whose body calls pointAdd_1) hits.
        call = FunctionCall([SSAVar("%r")], GlobalVariable("@Sub"), [SSAVar("%arg1")], None)
        call._member_hint = LoopIndexedName("last")
        before_body = [
            BoolCmp(SSAVar("%cond"), "lt", SSAVar("%arg1"), SSAVar("%extern")),
            SCFCondition(SSAVar("%cond"), [SSAVar("%arg1")], [Type("index")]),
        ]
        after_body = [
            FeltConst(SSAVar("%c1"), 1),
            call,
            FeltBinary(SSAVar("%next"), "felt.add", SSAVar("%arg1"), SSAVar("%c1"), []),
            SCFYield([SSAVar("%next")], [Type("index")]),
        ]
        op = SCFWhile(
            [], [(SSAVar("%arg1"), SSAVar("%c0"))], [[Type("index")], [Type("index")]],
            before_body, [(SSAVar("%arg1"), Type("index"))], after_body,
        )
        ctx = TranslationContext()
        ctx.var2const["%c0"] = 0
        ctx.llzk_func2core["@Sub"] = "Sub"
        ctx.core_func2args["Sub"] = ([], [("@out", Type("!felt.type"))])

        with pytest.raises(NotImplementedError):
            list(op.to_core(ctx))

    def test_while_to_core_bool_and_condition_takes_min(self):
        # A condition of the form bool.and(arg1 < 5, arg1 < 3): the loop
        # stops as soon as either half first goes false, so the smaller
        # bound (3) wins -- not touching scf.py at all, since the existing
        # backward-walk in _process_while_variables is already generic over
        # BoolBinary.operands, same as any other operation.
        before_body = [
            FeltConst(SSAVar("%b1"), 5),
            BoolCmp(SSAVar("%c1cond"), "lt", SSAVar("%arg1"), SSAVar("%b1")),
            FeltConst(SSAVar("%b2"), 3),
            BoolCmp(SSAVar("%c2cond"), "lt", SSAVar("%arg1"), SSAVar("%b2")),
            BoolBinary(SSAVar("%cond"), "bool.and", SSAVar("%c1cond"), SSAVar("%c2cond")),
            SCFCondition(SSAVar("%cond"), [SSAVar("%arg1")], [Type("index")]),
        ]
        after_body = [
            FeltConst(SSAVar("%c1"), 1),
            FeltBinary(SSAVar("%next"), "felt.add", SSAVar("%arg1"), SSAVar("%c1"), []),
            SCFYield([SSAVar("%next")], [Type("index")]),
        ]
        op = SCFWhile(
            [], [(SSAVar("%arg1"), SSAVar("%c0"))], [[Type("index")], [Type("index")]],
            before_body, [(SSAVar("%arg1"), Type("index"))], after_body,
        )
        ctx = TranslationContext()
        ctx.var2const["%c0"] = 0

        out = list(op.to_core(ctx))
        assert out[1] == "repeat 3 {"

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

    # ── Block-arg name collisions across sibling/nested while/for occurrences ─
    #
    # Regression coverage for poseidon3_test_concrete.mlir's KeyError: '@count'
    # (see PROGRESS.md): scf.while's/scf.for's own block-arg (init_args'/
    # after_args'/iter_args') and induction-variable names were never
    # cursor-tagged the way body-computed result names already are
    # (before_rename/after_rename), so two sibling or nested loop occurrences
    # reusing the same raw LLZK block-arg text (very common -- block-arg
    # numbering isn't globally unique) silently clobbered each other's
    # ctx.ssa2pod_var/ctx.var2const/ctx.ssa_to_name registration.

    def _pod_while_parse_fn(self, start, end):
        ops = []
        for i in range(start, end):
            line = self.lines[i].strip()
            if not line or line in ("}", "do {"):
                continue
            if PodRead.match(line):
                ops.append(PodRead.parse(line))
            elif SCFYield.match(line):
                ops.append(SCFYield.parse(line))
            elif SCFCondition.match(line):
                ops.append(SCFCondition.parse(line))
        return ops

    def test_while_parse_sibling_reuse_of_block_arg_name_gets_distinct_suffix(self):
        self.lines = [
            'scf.while (%arg8 = %p_a) : (!pod.type<[@x: !felt.type]>) -> (!pod.type<[@x: !felt.type]>) {',
            'scf.condition(%cond1) %arg8 : !pod.type<[@x: !felt.type]>',
            '}',
            'do {',
            'scf.yield %arg8 : !pod.type<[@x: !felt.type]>',
            '}',
            'scf.while (%arg8 = %p_b) : (!pod.type<[@y: !felt.type]>) -> (!pod.type<[@y: !felt.type]>) {',
            'scf.condition(%cond2) %arg8 : !pod.type<[@y: !felt.type]>',
            '}',
            'do {',
            'scf.yield %arg8 : !pod.type<[@y: !felt.type]>',
            '}',
        ]
        op1, next1 = SCFWhile.parse(self.lines, 0, self._pod_while_parse_fn)
        op2, _ = SCFWhile.parse(self.lines, next1, self._pod_while_parse_fn)

        assert op1.init_args[0][0].name == "%arg8_w0"
        assert op2.init_args[0][0].name == f"%arg8_w{next1}"
        assert op1.init_args[0][0].name != op2.init_args[0][0].name

        # References inside each while's own body were renamed consistently
        # with that same while's init_args (the scf.condition/scf.yield
        # operand, not just the init_args tuple itself).
        assert op1.before_body[0].args[0].name == "%arg8_w0"
        assert op1.after_body[0].operands[0].name == "%arg8_w0"
        assert op2.before_body[0].args[0].name == f"%arg8_w{next1}"
        assert op2.after_body[0].operands[0].name == f"%arg8_w{next1}"

    def _recursive_while_parse_fn(self, start, end):
        ops = []
        i = start
        while i < end:
            line = self.lines[i].strip()
            if not line or line in ("}", "do {"):
                i += 1
                continue
            if SCFWhile.match(line):
                op, next_i = SCFWhile.parse(self.lines, i, self._recursive_while_parse_fn)
                ops.append(op)
                i = next_i
                continue
            if SCFYield.match(line):
                ops.append(SCFYield.parse(line))
            elif SCFCondition.match(line):
                ops.append(SCFCondition.parse(line))
            i += 1
        return ops

    def test_while_parse_nested_reuse_of_block_arg_name_gets_distinct_suffix(self):
        self.lines = [
            'scf.while (%arg8 = %outer_init) : (index) -> (index) {',   # 0
            'scf.condition(%cond1) %arg8',                              # 1
            '}',                                                        # 2
            'do {',                                                     # 3
            'scf.while (%arg8 = %inner_init) : (index) -> (index) {',   # 4
            'scf.condition(%cond2) %arg8',                              # 5
            '}',                                                        # 6
            'do {',                                                     # 7
            'scf.yield %arg8 : index',                                  # 8
            '}',                                                        # 9
            'scf.yield %arg8 : index',                                  # 10
            '}',                                                        # 11
        ]
        outer, _ = SCFWhile.parse(self.lines, 0, self._recursive_while_parse_fn)
        inner = outer.after_body[0]
        assert isinstance(inner, SCFWhile)

        assert outer.init_args[0][0].name == "%arg8_w0"
        assert inner.init_args[0][0].name == "%arg8_w4"
        assert outer.before_body[0].args[0].name == "%arg8_w0"
        assert inner.before_body[0].args[0].name == "%arg8_w4"
        # The outer's own trailing yield (after the nested while) still
        # references the outer's own (renamed) block arg, not the inner's.
        assert outer.after_body[-1].operands[0].name == "%arg8_w0"

    def test_for_parse_sibling_reuse_of_iv_gets_distinct_suffix(self):
        self.lines = [
            "scf.for %iv = %lb to %ub step %s {",
            "scf.yield",
            "}",
            "scf.for %iv = %lb to %ub step %s {",
            "scf.yield",
            "}",
        ]
        op1, next1 = SCFFor.parse(self.lines, 0, self._simple_parse_fn)
        op2, _ = SCFFor.parse(self.lines, next1, self._simple_parse_fn)
        assert op1.iv.name == "%iv_f0"
        assert op2.iv.name == f"%iv_f{next1}"
        assert op1.iv.name != op2.iv.name

    def test_while_to_core_sibling_block_arg_reuse_does_not_collide_in_ssa2pod_var(self):
        # End-to-end reproduction (in miniature) of the poseidon3_test_
        # concrete.mlir crash: two sibling while occurrences both name their
        # own block arg "%arg8", bound to differently-shaped pods. Before
        # the fix, registering the second while's "%arg8" would silently
        # overwrite the first's entry in the flat ctx.ssa2pod_var dict, so a
        # later read of the FIRST while's own field (here "@x") would
        # KeyError against the SECOND while's (here "@y"-shaped) mapping.
        self.lines = [
            'scf.while (%arg8 = %p_a) : (!pod.type<[@x: !felt.type]>) -> (!pod.type<[@x: !felt.type]>) {',
            'scf.condition(%cond1) %arg8 : !pod.type<[@x: !felt.type]>',
            '}',
            'do {',
            '%r1 = pod.read %arg8 [@x] : !pod.type<[@x: !felt.type]>, !felt.type',
            'scf.yield %arg8 : !pod.type<[@x: !felt.type]>',
            '}',
            'scf.while (%arg8 = %p_b) : (!pod.type<[@y: !felt.type]>) -> (!pod.type<[@y: !felt.type]>) {',
            'scf.condition(%cond2) %arg8 : !pod.type<[@y: !felt.type]>',
            '}',
            'do {',
            '%r2 = pod.read %arg8 [@y] : !pod.type<[@y: !felt.type]>, !felt.type',
            'scf.yield %arg8 : !pod.type<[@y: !felt.type]>',
            '}',
        ]
        op1, next1 = SCFWhile.parse(self.lines, 0, self._pod_while_parse_fn)
        op2, _ = SCFWhile.parse(self.lines, next1, self._pod_while_parse_fn)

        ctx = TranslationContext()
        ctx.ssa2pod_var["%p_a"] = {"@x": ("%p_a_@x", Type("!felt.type"))}
        ctx.ssa2pod_var["%p_b"] = {"@y": ("%p_b_@y", Type("!felt.type"))}

        # Mirrors SCFWhile.to_core's own first registration loop for each
        # while, in program order (op1 first, then op2 -- the ordering that
        # would clobber a shared, un-suffixed "%arg8" key).
        for type_, (lhs, rhs) in zip(op1.func_type[0], op1.init_args):
            translate_assignment_core_with_ctx(lhs, rhs, type_, ctx)
        for type_, (lhs, rhs) in zip(op2.func_type[0], op2.init_args):
            translate_assignment_core_with_ctx(lhs, rhs, type_, ctx)

        assert op1.init_args[0][0].name in ctx.ssa2pod_var
        assert op2.init_args[0][0].name in ctx.ssa2pod_var
        assert op1.init_args[0][0].name != op2.init_args[0][0].name

        pod_read_1 = op1.after_body[0]
        pod_read_2 = op2.after_body[0]
        assert isinstance(pod_read_1, PodRead) and isinstance(pod_read_2, PodRead)

        # Previously: op1's own read (of "@x") would KeyError here, since
        # op2's registration had overwritten the shared "%arg8" key with an
        # "@y"-only mapping. (Result names %r1/%r2 are also cursor-tagged by
        # the existing after_rename mechanism, since they're body-computed;
        # the copied-through variable names derive from each while's own
        # renamed block-arg, per translate_assignment_core_with_ctx's
        # "{lhs.name}_{record}" convention.)
        lines_1 = list(pod_read_1.to_core(ctx))
        lines_2 = list(pod_read_2.to_core(ctx))
        assert lines_1 == ["%r1_aft0 = %arg8_w0_@x"]
        assert lines_2 == [f"%r2_aft{next1} = %arg8_w{next1}_@y"]

    def test_while_to_core_member_backed_pod_arg_preserves_semantic_dest_across_init_and_yield(self):
        # End-to-end reproduction of the poseidon3_test_concrete.mlir crash:
        # a pod-typed while block arg ("%arg9") backs a struct member
        # ("ark"), and each of its fields is ITSELF a nested pod (one level
        # deep). The arg's *initial* value comes from a plain raw-SSA pod
        # (mirroring an llzk.nondet result) -- previously, copying that in
        # would derive a throwaway "%arg9_..._@idx_7" name instead of the
        # semantic "ark.idx_7", and the SAME clobbering happened again on
        # the yield-back, eventually stranding a name nothing could resolve
        # through. A pod.read/pod.read chain inside the body
        # (%598 = pod.read %arg9[@idx_7]; %599 = pod.read %598[@in]) is the
        # exact shape that KeyError'd.
        pod_type_str = "!pod.type<[@idx_7: !pod.type<[@in: !array.type<3 x !felt.type<\"bn128\">>]>]>"
        nested_type_str = "!pod.type<[@in: !array.type<3 x !felt.type<\"bn128\">>]>"
        array_type_str = "!array.type<3 x !felt.type<\"bn128\">>"
        self.lines = [
            f'scf.while (%arg9 = %nondet_p) : ({pod_type_str}) -> ({pod_type_str}) {{',
            f'scf.condition(%cond) %arg9 : {pod_type_str}',
            '}',
            'do {',
            f'%598 = pod.read %arg9 [@idx_7] : {pod_type_str}, {nested_type_str}',
            f'%599 = pod.read %598 [@in] : {nested_type_str}, {array_type_str}',
            f'scf.yield %other : {pod_type_str}',
            '}',
        ]
        op, _ = SCFWhile.parse(self.lines, 0, self._pod_while_parse_fn)

        arg9_name = op.init_args[0][0].name  # renamed block-arg, e.g. "%arg9_w0"

        ctx = TranslationContext()
        ctx.input_pod_to_member[arg9_name] = "ark"

        # Mirrors an llzk.nondet result: raw-SSA field names throughout, not
        # semantic ones.
        ctx.ssa2pod_var["%nondet_p"] = {
            "@idx_7": ("%nondet_p_@idx_7", Type(nested_type_str)),
        }
        ctx.ssa2pod_var["%nondet_p_@idx_7"] = {
            "@in": ("%nondet_p_@idx_7_@in", Type(array_type_str)),
        }
        # A second, independently-raw-named pod the loop yields back instead
        # of %arg9 itself (so the yield-back actually exercises a copy,
        # rather than being skipped as a same-name no-op).
        ctx.ssa2pod_var["%other"] = {
            "@idx_7": ("%other_@idx_7", Type(nested_type_str)),
        }
        ctx.ssa2pod_var["%other_@idx_7"] = {
            "@in": ("%other_@idx_7_@in", Type(array_type_str)),
        }

        # Init-copy: mirrors SCFWhile.to_core's own first registration loop.
        for type_, (lhs, rhs) in zip(op.func_type[0], op.init_args):
            translate_assignment_core_with_ctx(lhs, rhs, type_, ctx)

        assert ctx.ssa2pod_var[arg9_name]["@idx_7"][0] == "ark.idx_7"
        assert ctx.ssa2pod_var["ark.idx_7"]["@in"][0] == "ark.idx_7_in"

        # Body: the pod.read/pod.read chain must resolve without a
        # KeyError -- this is the exact crash this fix targets.
        pod_read_nested, pod_read_leaf, yield_op = op.after_body
        list(pod_read_nested.to_core(ctx))
        list(pod_read_leaf.to_core(ctx))

        # Yield-back: mirrors SCFWhile.to_core's emit_iteration reassignment.
        for yield_val, (before_in_arg, _), type_ in zip(yield_op.operands, op.init_args, op.func_type[0]):
            if yield_val.name != before_in_arg.name:
                translate_assignment_core_with_ctx(before_in_arg, yield_val, type_, ctx)

        # The semantic destination must survive the yield-back too -- not be
        # clobbered a second time by a fresh raw derived name.
        assert ctx.ssa2pod_var[arg9_name]["@idx_7"][0] == "ark.idx_7"
        assert ctx.ssa2pod_var["ark.idx_7"]["@in"][0] == "ark.idx_7_in"
