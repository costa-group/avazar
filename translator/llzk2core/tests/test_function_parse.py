import pytest
from llzk_dialects.function import FunctionReturn, FunctionCall, FunctionDef
from llzk_dialects.core import SSAVar, GlobalVariable, Type, TranslationContext
from llzk_dialects.felt import FeltConst, FeltBinary
from llzk_dialects.pod import PodNew, PodRead


class TestFunction:

    # ── FunctionReturn ────────────────────────────────────────────────────────

    def test_return_empty(self):
        op = FunctionReturn.parse("function.return")
        assert op.operands == []
        assert op.types == []

    def test_return_with_values(self):
        op = FunctionReturn.parse(
            "function.return %a, %b : !felt.type, !felt.type"
        )
        assert op.operands == [SSAVar("%a"), SSAVar("%b")]
        assert op.types == [Type("!felt.type"), Type("!felt.type")]

    def test_return_single(self):
        op = FunctionReturn.parse("  function.return %r : !felt.type  ")
        assert op.operands == [SSAVar("%r")]

    def test_return_nd_array_type_not_split_on_dimension_comma(self):
        # Regression: a single returned N-D array type's own dimension list
        # (e.g. "17,17") contains a comma that is NOT a top-level type
        # separator -- a naive split(",") on the types string broke it into
        # two malformed fragments ("!array.type<17" and
        # "17 x !felt.type<...>>"), silently producing a Type whose
        # to_core() is None (a bare "!array.type<17" matches neither the
        # array nor the felt-scalar case) -- which then leaked the literal
        # string "None" into the emitted Core function signature. Mirrors
        # the real @POSEIDON_M_2 shape from poseidon3_test_concrete.mlir.
        op = FunctionReturn.parse(
            'function.return %1 : !array.type<17,17 x !felt.type<"bn128">>'
        )
        assert op.operands == [SSAVar("%1")]
        assert op.types == [Type('!array.type<17,17 x !felt.type<"bn128">>')]
        assert op.types[0].to_core() == "arr<289>"

    def test_return_match(self):
        assert FunctionReturn.match("function.return") is True
        assert FunctionReturn.match("function.call @f()") is False

    # ── FunctionCall ──────────────────────────────────────────────────────────

    def test_call_no_result(self):
        op = FunctionCall.parse("function.call @constrain(%self) : (!struct.type<@S>) -> ()")
        assert op.results == []
        assert op.callee == GlobalVariable("@constrain")
        assert op.args == [SSAVar("%self")]

    def test_call_with_result(self):
        op = FunctionCall.parse(
            "%r = function.call @compute(%self) : (!struct.type<@S>) -> (!felt.type)"
        )
        assert op.results == [SSAVar("%r")]
        assert op.callee == GlobalVariable("@compute")

    def test_call_no_args(self):
        op = FunctionCall.parse("function.call @init()")
        assert op.args == []

    def test_call_result_property_single(self):
        op = FunctionCall.parse("%r = function.call @f(%x)")
        assert op.result == SSAVar("%r")

    def test_call_result_property_no_result(self):
        op = FunctionCall.parse("function.call @f(%x)")
        assert op.result is None

    def test_call_member_hint_initially_none(self):
        op = FunctionCall.parse("%r = function.call @f(%x)")
        assert op._member_hint is None

    def test_call_match(self):
        assert FunctionCall.match("function.call @f(%x)") is True
        assert FunctionCall.match("function.return") is False

    # ── FunctionCall.to_core — bare member-hint naming ───────────────────────

    def _call_ctx(self):
        ctx = TranslationContext()
        ctx.llzk_func2core["@Sub"] = "Sub"
        ctx.core_func2args["Sub"] = ([], [("@out", Type("!felt.type"))])
        return ctx

    def test_call_to_core_member_hint_non_constant_index(self):
        # _member_hint is the bare member name when the component array
        # this call feeds was read at a non-constant index (struct.py's
        # _annotate_array_component_reads) — there's no single instance to
        # name more specifically at translation time.
        op = FunctionCall.parse("%r = function.call @Sub(%x)")
        op._member_hint = "last"
        ctx = self._call_ctx()
        lines = list(op.to_core(ctx))
        assert lines == ["call Sub(%x) to last.out"]
        assert ctx.ssa_to_name["%r_@out"] == "last.out"

    # ── FunctionCall.to_core — pure function callee (no struct.def) ──────────

    def test_call_to_core_pure_function_single_result(self):
        # A pure function's out-args are its own function.return operand
        # names, never '@'-prefixed (see poly.py's _register_pure_function).
        # The call's result should just be used directly — no member/signal
        # lookup, no ctx.ssa_to_name registration.
        op = FunctionCall.parse(
            "%40 = function.call @pointAdd_1::@pointAdd_1(%29, %31) "
            ': (!felt.type, !felt.type) -> !array.type<2 x !felt.type<"bn128">>'
        )
        ctx = TranslationContext()
        ctx.llzk_func2core["@pointAdd_1::@pointAdd_1"] = "@pointAdd_1"
        ctx.core_func2args["@pointAdd_1"] = (
            [("%arg0", Type("!felt.type")), ("%arg1", Type("!felt.type"))],
            [("%nondet", Type('!array.type<2 x !felt.type<"bn128">>'))],
        )
        lines = list(op.to_core(ctx))
        assert lines == ["call @pointAdd_1(%29,%31) to %40"]
        assert ctx.ssa_to_name == {}

    def test_call_to_core_pure_function_multi_result(self):
        op = FunctionCall.parse(
            "%50:2 = function.call @foo::@foo(%1) : (!felt.type) -> (!felt.type, !felt.type)"
        )
        ctx = TranslationContext()
        ctx.llzk_func2core["@foo::@foo"] = "@foo"
        ctx.core_func2args["@foo"] = (
            [("%arg0", Type("!felt.type"))],
            [("%r0", Type("!felt.type")), ("%r1", Type("!felt.type"))],
        )
        lines = list(op.to_core(ctx))
        assert lines == ["call @foo(%1) to %50#0,%50#1"]

    # ── FunctionDef (BlockOperation) ─────────────────────────────────────────

    def _felt_parse_fn(self, start, end):
        ops = []
        for i in range(start, end):
            line = self.lines[i].strip()
            if not line or line == "}":
                continue
            if FunctionReturn.match(line):
                ops.append(FunctionReturn.parse(line))
            elif FeltBinary.match(line):
                ops.append(FeltBinary.parse(line))
            elif FeltConst.match(line):
                ops.append(FeltConst.parse(line))
        return ops

    def test_function_def_empty(self):
        self.lines = [
            "function.def @empty() {",
            "}",
        ]
        op, next_cur = FunctionDef.parse(self.lines, 0, self._felt_parse_fn)
        assert op.sym_name == GlobalVariable("@empty")
        assert op.body == []
        assert next_cur == 2

    def test_function_def_with_body(self):
        self.lines = [
            "function.def @add(%a: !felt.type, %b: !felt.type) -> (!felt.type) {",
            "%r = felt.add %a, %b",
            "function.return %r : !felt.type",
            "}",
        ]
        op, next_cur = FunctionDef.parse(self.lines, 0, self._felt_parse_fn)
        assert op.sym_name == GlobalVariable("@add")
        assert len(op.body) == 2
        assert next_cur == 4

    def test_function_def_match(self):
        assert FunctionDef.match("function.def @f(%x: !felt.type) {") is True
        assert FunctionDef.match("function.call @f(%x)") is False

    # ── FunctionDef.in_args / in_arg_names ───────────────────────────────────

    def _def_with_signature(self, signature):
        op, _ = FunctionDef.parse([f"function.def @f{signature} {{", "}"], 0, self._felt_parse_fn)
        return op

    def test_in_args_with_results(self):
        op = self._def_with_signature(
            '(%arg0: !array.type<2 x !felt.type<"bn128">> {function.arg_name = "in"}) '
            '-> !struct.type<@A_0::@A_0<[]>> attributes {function.allow_witness}'
        )
        assert op.in_args == [("%arg0", Type('!array.type<2 x !felt.type<"bn128">>'))]
        assert op.in_arg_names == {"%arg0": "in"}

    def test_in_args_without_results_constrain(self):
        # A @constrain has no '->': the 'attributes {...}' after the argument
        # list must not be read as further arguments
        op = self._def_with_signature(
            '(%arg0: !struct.type<@A_0::@A_0<[]>>, '
            '%arg1: !array.type<2 x !felt.type<"bn128">> {function.arg_name = "in"}) '
            'attributes {function.allow_constraint, function.allow_non_native_field_ops}'
        )
        assert op.in_args == [
            ("%arg0", Type("!struct.type<@A_0::@A_0<[]>>")),
            ("%arg1", Type('!array.type<2 x !felt.type<"bn128">>')),
        ]
        assert op.in_arg_names == {"%arg1": "in"}

    def test_in_args_without_results_or_attributes(self):
        op = self._def_with_signature('(%arg0: !felt.type<"bn128"> {function.arg_name = "x"})')
        assert op.in_args == [("%arg0", Type('!felt.type<"bn128">'))]
        assert op.in_arg_names == {"%arg0": "x"}

    def test_in_args_parenthesis_in_loc(self):
        # A ')' inside a quoted loc path does not close the argument list
        op = self._def_with_signature(
            '(%arg0: !felt.type<"bn128"> {function.arg_name = "a"} loc("dir (1)/f.circom":3:1), '
            '%arg1: !felt.type<"bn128"> {function.arg_name = "b"}) attributes {function.allow_constraint}'
        )
        assert [name for name, _ in op.in_args] == ["%arg0", "%arg1"]
        assert op.in_arg_names == {"%arg0": "a", "%arg1": "b"}

    def test_in_args_empty(self):
        op = self._def_with_signature("() attributes {function.allow_constraint}")
        assert op.in_args == []
        assert op.in_arg_names == {}

    # ── FunctionDef.to_core — signature-out naming ───────────────────────────

    def test_function_def_to_core_pure_function_keeps_percent_out_name(self):
        # A struct out-arg ('@out') gets its '@' stripped in the signature.
        # A pure function's out-arg is just its own SSA name ('%nondet') —
        # not '@'-prefixed — and should be kept as-is, consistent with how
        # its input args already keep their '%' prefix in the signature.
        self.lines = [
            'function.def @pointAdd_1(%arg0: !felt.type) -> !array.type<2 x !felt.type<"bn128">> {',
            'function.return %nondet : !array.type<2 x !felt.type<"bn128">>',
            "}",
        ]
        op, _ = FunctionDef.parse(self.lines, 0, self._felt_parse_fn)
        ctx = TranslationContext()
        ctx.current_core_function = "@pointAdd_1"
        ctx.core_func2args["@pointAdd_1"] = (
            [("%arg0", Type("!felt.type"))],
            [("%nondet", Type('!array.type<2 x !felt.type<"bn128">>'))],
        )
        out = ''.join(op.to_core(ctx))
        assert "def @pointAdd_1(%arg0: ff) -> %nondet: arr<2> {" in out

    # ── FunctionDef.to_core — cross-function scope leak ──────────────────────

    def test_to_core_clears_stale_ssa2pod_var_and_var2const_from_a_prior_function(self):
        # Regression: pedersen_test_concrete.mlir crashed with
        # KeyError: '@in' inside PodRead.to_core. Root cause: LLZK/MLIR SSA
        # numbers restart from %0/%1/... in every function, but
        # ctx.ssa2pod_var/ctx.var2const are flat, whole-translation dicts
        # that were never cleared between functions (unlike
        # ctx.ssa_to_name/ctx.input_pod_to_member, which struct.py's
        # StructDef.to_core already clears around each struct's own
        # compute). Two unrelated structs' own @compute bodies each used
        # "%5" for a differently-shaped pod; the second one's pod.read
        # crashed on the first one's stale, still-live registration.
        pod_new = PodNew.parse(
            '%5 = pod.new {@in = %x} : !pod.type<[@in: !felt.type]>'
        )
        pod_read = PodRead.parse(
            '%6 = pod.read %5 [@in] : !pod.type<[@in: !felt.type]>, !felt.type'
        )
        func_return = FunctionReturn.parse('function.return %6 : !felt.type')
        op = FunctionDef(
            GlobalVariable.parse("@f"), "%x: !felt.type -> !felt.type",
            [pod_new, pod_read, func_return],
        )

        ctx = TranslationContext()
        ctx.current_core_function = "@f"
        ctx.core_func2args["@f"] = (
            [("%x", Type("!felt.type"))], [("%6", Type("!felt.type"))]
        )
        # Simulate a PRIOR, unrelated function's leftover state under the
        # exact same bare SSA name this function also happens to reuse.
        ctx.ssa2pod_var["%5"] = {"@count": ("%5_@count", Type("index"))}
        ctx.var2const["%5"] = 999

        out = ''.join(op.to_core(ctx))

        # previously: KeyError on "@in" (the stale "%5" entry only had
        # "@count", not "@in") -- now the pod.new's own fresh registration
        # is used instead.
        assert "%6 = %5_@in" in out
        assert "%5" not in ctx.var2const


class TestFunctionAllSignalsAsOutput:
    """
    --all-signals-as-output (possibly temporary, branch signals_as_output):
    a struct's def returns its outputs, then its inputs, then its
    intermediates (ctx.core_func2extra_outs), and every call binds them.
    """

    def _ctx(self):
        ctx = TranslationContext(all_signals_as_output=True)
        ctx.llzk_func2core["@Sub"] = "Sub"
        ctx.core_func2args["Sub"] = (
            [("%arg0", Type("!felt.type")), ("%arg1", Type('!array.type<2 x !felt.type<"bn128">>'))],
            [("@out", Type("!felt.type"))],
        )
        ctx.core_func2extra_outs["Sub"] = [
            ("a", "%arg0", Type("!felt.type")),
            ("b", "%arg1", Type('!array.type<2 x !felt.type<"bn128">>')),
            ("inv", None, Type("!felt.type")),
        ]
        return ctx

    # ── FunctionCall.to_core ─────────────────────────────────────────────────

    def test_call_dummies_named_like_outputs_with_member_hint(self):
        op = FunctionCall.parse("%r = function.call @Sub(%x, %y)")
        op._member_hint = "c"
        ctx = self._ctx()
        assert list(op.to_core(ctx)) == ["call Sub(%x,%y) to c.out,c.a,c.b,c.inv"]
        # Only the real output is registered for later reads
        assert ctx.ssa_to_name == {"%r_@out": "c.out"}

    def test_call_dummies_without_member_hint(self):
        op = FunctionCall.parse("%r = function.call @Sub(%x, %y)")
        assert list(op.to_core(self._ctx())) == ["call Sub(%x,%y) to %r_@out,%r_@a,%r_@b,%r_@inv"]

    def test_call_without_extras_entry_unchanged(self):
        op = FunctionCall.parse("%r = function.call @Sub(%x, %y)")
        ctx = self._ctx()
        ctx.core_func2extra_outs.clear()
        assert list(op.to_core(ctx)) == ["call Sub(%x,%y) to %r_@out"]

    def test_call_pure_function_unaffected(self):
        op = FunctionCall.parse("%50 = function.call @foo::@foo(%1) : (!felt.type) -> !felt.type")
        ctx = TranslationContext(all_signals_as_output=True)
        ctx.llzk_func2core["@foo::@foo"] = "@foo"
        ctx.core_func2args["@foo"] = ([("%arg0", Type("!felt.type"))], [("%r0", Type("!felt.type"))])
        assert list(op.to_core(ctx)) == ["call @foo(%1) to %50"]

    # ── FunctionDef.to_core ──────────────────────────────────────────────────

    @staticmethod
    def _empty_parse_fn(start, end):
        return []

    def _def(self):
        lines = [
            'function.def @compute(%arg0: !felt.type {function.arg_name = "a"}, '
            '%arg1: !array.type<2 x !felt.type<"bn128">> {function.arg_name = "b"}) -> !struct.type<@Sub::@Sub<[]>> {',
            "}",
        ]
        op, _ = FunctionDef.parse(lines, 0, self._empty_parse_fn)
        return op

    def test_def_signature_outputs_then_inputs_then_intermediates(self):
        ctx = self._ctx()
        ctx.current_core_function = "Sub"
        out = "".join(self._def().to_core(ctx))
        assert out.startswith(
            "def Sub(%arg0: ff, %arg1: arr<2>) -> out: ff, a: ff, b: arr<2>, inv: ff {\n")

    def test_def_copies_input_signals_from_parameters(self):
        ctx = self._ctx()
        ctx.current_core_function = "Sub"
        out = "".join(self._def().to_core(ctx))
        assert "a = %arg0\n" in out
        assert "array.copy %arg1 b\n" in out
        # An intermediate is already assigned by name in the body
        assert "inv =" not in out

    def test_def_without_extras_entry_unchanged(self):
        ctx = self._ctx()
        ctx.core_func2extra_outs.clear()
        ctx.current_core_function = "Sub"
        out = "".join(self._def().to_core(ctx))
        assert out == "def Sub(%arg0: ff, %arg1: arr<2>) -> out: ff {\n}\n\n"
