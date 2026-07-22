import pytest
from llzk_dialects.llzk import LLZKNondet, ModuleOp
from llzk_dialects.core import SSAVar, Type, GlobalVariable, TranslationContext
from llzk_dialects.poly import PolyTemplate
from llzk_dialects.function import FunctionDef, FunctionReturn, FunctionCall


class TestLLZK:

    def test_nondet(self):
        op = LLZKNondet.parse("%x = llzk.nondet : !felt.type")
        assert op.result == SSAVar("%x")
        assert op.result_type == Type("!felt.type")

    def test_nondet_whitespace(self):
        op = LLZKNondet.parse("  %v = llzk.nondet : !array.type<index>  ")
        assert op.result == SSAVar("%v")
        assert op.result_type == Type("!array.type<index>")

    def test_nondet_missing_type(self):
        with pytest.raises(ValueError):
            LLZKNondet.parse("%x = llzk.nondet")

    def test_nondet_match(self):
        assert LLZKNondet.match("%x = llzk.nondet : !felt.type") is True
        assert LLZKNondet.match("%x = felt.const 1") is False

    # ── LLZKNondet.to_core ────────────────────────────────────────────────────

    def test_nondet_to_core_felt(self):
        op = LLZKNondet.parse("%x = llzk.nondet : !felt.type<\"bn128\">")
        lines = list(op.to_core(TranslationContext()))
        assert lines == ["%x = 0"]

    def test_nondet_to_core_felt_array_1d(self):
        op = LLZKNondet.parse("%v = llzk.nondet : !array.type<4 x !felt.type<\"bn128\">>")
        lines = list(op.to_core(TranslationContext()))
        assert lines == ["array.new 4 %v"]

    def test_nondet_to_core_felt_array_2d_uses_total_size(self):
        op = LLZKNondet.parse("%v = llzk.nondet : !array.type<2,3 x !felt.type<\"bn128\">>")
        lines = list(op.to_core(TranslationContext()))
        assert lines == ["array.new 6 %v"]

    def test_nondet_to_core_struct_array(self):
        # Generalized beyond felt-only arrays: any element type, as long as
        # the type itself is array-shaped.
        op = LLZKNondet.parse("%v = llzk.nondet : !array.type<4 x !struct.type<@S<[]>>>")
        lines = list(op.to_core(TranslationContext()))
        assert lines == ["array.new 4 %v"]

    def test_nondet_to_core_pod_array(self):
        op = LLZKNondet.parse(
            "%v = llzk.nondet : !array.type<3 x !pod.type<[@x: !felt.type]>>"
        )
        lines = list(op.to_core(TranslationContext()))
        assert lines == ["array.new 3 %v"]

    def test_nondet_to_core_index_not_recognized_raises(self):
        # A plain (non-array, non-pod) index/struct has no defined "zero
        # value" here -- explicitly unsupported rather than silently
        # mistranslated.
        op = LLZKNondet.parse("%v = llzk.nondet : index")
        with pytest.raises(NotImplementedError):
            list(op.to_core(TranslationContext()))

    # ── LLZKNondet.to_core — pod-typed result (assign like pod.new) ──────────
    #
    # A pod-typed nondet value has no operand of its own (unlike pod.new) to
    # derive its fields' values from -- every field is treated as if pod.new
    # had been given no initial value for it (register_and_allocate_pod).

    def test_nondet_to_core_pod_scalar_field(self):
        op = LLZKNondet.parse("%v = llzk.nondet : !pod.type<[@x: !felt.type]>")
        ctx = TranslationContext()
        list(op.to_core(ctx))
        assert ctx.ssa2pod_var["%v"]["@x"][0] == "%v_@x"

    def test_nondet_to_core_pod_felt_array_field(self):
        op = LLZKNondet.parse(
            "%v = llzk.nondet : !pod.type<[@in: !array.type<3 x !felt.type<\"bn128\">>]>"
        )
        lines = list(op.to_core(TranslationContext()))
        assert lines == ["array.new 3 %v_@in"]

    def test_nondet_to_core_pod_in_pod_registers_recursively(self):
        # Mirrors the exact poseidon3_test_concrete.mlir shape: a nondet pod
        # whose fields are themselves non-empty nested pods
        # (@idx_0: !pod.type<[@in: !array.type<3 x ff>]>) -- must recurse the
        # same way PodNew now does (see _register_nested_pod_vars), not raise
        # or silently misread the nested felt array as the field's own type.
        op = LLZKNondet.parse(
            "%v = llzk.nondet : "
            "!pod.type<[@idx_0: !pod.type<[@in: !array.type<3 x !felt.type<\"bn128\">>]>]>"
        )
        ctx = TranslationContext()
        lines = list(op.to_core(ctx))
        assert lines == ["array.new 3 %v_@idx_0_@in"]
        assert ctx.ssa2pod_var["%v"]["@idx_0"][0] == "%v_@idx_0"
        assert ctx.ssa2pod_var["%v_@idx_0"]["@in"][0] == "%v_@idx_0_@in"

    def test_nondet_to_core_pod_with_struct_and_empty_pod_fields(self):
        # The other real shape from the same file: a nondet pod whose
        # (non-empty) nested pod fields mix an index, a struct, and an empty
        # pod -- the struct field just allocates via _flatten_container_fields
        # (no ssa2pod_var registration needed, per PodNew's existing
        # convention), and the empty pod registers as {}.
        op = LLZKNondet.parse(
            "%v = llzk.nondet : !pod.type<[@idx_0: !pod.type<[@count: index, "
            "@comp: !struct.type<@S<[]>>, @params: !pod.type<[]>]>]>"
        )
        ctx = TranslationContext()
        ctx.llzk_func2core["@S::@compute"] = "S"
        ctx.core_func2args["S"] = ([], [("@out", Type("!felt.type"))])
        list(op.to_core(ctx))
        assert ctx.ssa2pod_var["%v_@idx_0"]["@params"][0] == "%v_@idx_0_@params"
        assert ctx.ssa2pod_var["%v_@idx_0_@params"] == {}

    # ── ModuleOp.to_core — pure-function forward-reference pre-pass ─────────

    def test_module_prepass_registers_forward_referenced_pure_function(self):
        # A pure function template may be declared textually *after* a
        # caller that references it (e.g. escalarmulw4table_concrete.mlir's
        # EscalarMulW4Table_0, declared first, calls pointAdd_1, declared
        # afterwards) — unlike struct-to-struct calls, which this codebase
        # already requires to be declared before their callers. ModuleOp's
        # pre-pass registers every pure function's signature before any body
        # is translated, so this works regardless of declaration order.
        call = FunctionCall([SSAVar("%r")], GlobalVariable("@Callee::@Callee"), [SSAVar("%x")], None)
        caller_func = FunctionDef(
            GlobalVariable("@Caller"), "(%x: !felt.type) -> !felt.type",
            [call, FunctionReturn([SSAVar("%r")], [Type("!felt.type")])],
        )
        callee_func = FunctionDef(
            GlobalVariable("@Callee"), "(%arg0: !felt.type) -> !felt.type",
            [FunctionReturn([SSAVar("%arg0")], [Type("!felt.type")])],
        )
        # Caller declared (and listed) before its callee, on purpose.
        caller_template = PolyTemplate(GlobalVariable("@Caller"), [caller_func])
        callee_template = PolyTemplate(GlobalVariable("@Callee"), [callee_func])

        module = ModuleOp(lang=True, main_type=None, body=[caller_template, callee_template])
        ctx = TranslationContext()
        gen = module.to_core(ctx)
        next(gen)  # the pre-pass runs synchronously, before the first yield
        assert ctx.llzk_func2core["@Callee::@Callee"] == "@Callee"
        assert ctx.llzk_func2core["@Caller::@Caller"] == "@Caller"
