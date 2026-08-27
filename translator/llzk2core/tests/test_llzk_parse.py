import pytest
from llzk_dialects.llzk import LLZKNondet, ModuleOp
from llzk_dialects.core import SSAVar, Type, GlobalVariable, TranslationContext
from llzk_dialects.poly import PolyTemplate
from llzk_dialects.function import FunctionDef, FunctionReturn, FunctionCall
from llzk_dialects.struct import StructDef


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

    # ── ModuleOp.to_core — pure-function emission-order hoisting ────────────

    @staticmethod
    def _pure_template(name: str, calls: list) -> PolyTemplate:
        """
        A pure-function poly.template (bare function.def, no struct.def)
        named `name` (e.g. "@A", template and function share the name, as
        in every real example), whose body issues one function.call per
        (callee_name, result_name) pair in `calls` before returning a felt.
        """
        body = []
        for callee_name, result_name in calls:
            body.append(FunctionCall(
                [SSAVar(result_name)], GlobalVariable(f"{callee_name}::{callee_name}"),
                [SSAVar("%arg0")], None,
            ))
        ret_val = calls[-1][1] if calls else "%arg0"
        body.append(FunctionReturn([SSAVar(ret_val)], [Type("!felt.type")]))
        func = FunctionDef(GlobalVariable(name), "(%arg0: !felt.type) -> !felt.type", body)
        return PolyTemplate(GlobalVariable(name), [func])

    @staticmethod
    def _dummy_main_type(ctx: TranslationContext) -> Type:
        """
        A minimal llzk.main registration these tests don't otherwise care
        about, so draining ModuleOp.to_core() fully (to inspect the body's
        own emitted order) doesn't crash in _yield_main_function for lack
        of a real struct.
        """
        ctx.llzk_func2core["@Main::@Main::@compute"] = "@Main"
        ctx.core_func2args["@Main"] = ([], [])
        return Type('!struct.type<@Main::@Main<[]>>')

    def test_module_hoists_transitive_forward_referenced_pure_functions(self):
        # A -> B -> C, declared in the reverse of dependency order
        # ([A, B, C]), mirrors sha256_2_test_concrete.mlir's real shape:
        # ssigma1_1/ssigma0_2/bsigma1_3 each call rrot_8, declared later in
        # the file. Every def must precede every call referencing it, and
        # (per the DFS-based sort) each callee's own def precedes its
        # caller's def too.
        c_template = self._pure_template("@C", [])
        b_template = self._pure_template("@B", [("@C", "%r")])
        a_template = self._pure_template("@A", [("@B", "%r")])

        ctx = TranslationContext()
        module = ModuleOp(
            lang=True, main_type=self._dummy_main_type(ctx),
            body=[a_template, b_template, c_template],
        )
        text = "".join(module.to_core(ctx))

        assert text.index("def @C") < text.index("def @B") < text.index("def @A")
        assert text.index("def @C") < text.index("call @C")
        assert text.index("def @B") < text.index("call @B")

    def test_module_pure_function_ordering_is_stable_when_independent(self):
        # Two pure functions with no call between them: no reordering should
        # occur -- they keep their original relative (file) order.
        first = self._pure_template("@First", [])
        second = self._pure_template("@Second", [])

        ctx = TranslationContext()
        module = ModuleOp(lang=True, main_type=self._dummy_main_type(ctx), body=[first, second])
        text = "".join(module.to_core(ctx))

        assert text.index("def @First") < text.index("def @Second")

    def test_module_hoists_pure_function_ahead_of_struct_that_calls_it(self):
        # A struct.def (@compute) declared before the pure function it
        # calls -- mirrors sha256_2_test_concrete.mlir's
        # sha256compression_0 struct calling ssigma1_1 etc.
        call = FunctionCall([SSAVar("%r")], GlobalVariable("@Pure::@Pure"), [SSAVar("%x")], None)
        compute = FunctionDef(
            GlobalVariable("@compute"), "(%x: !felt.type) -> !felt.type",
            [call, FunctionReturn([SSAVar("%r")], [Type("!felt.type")])],
        )
        struct_template = PolyTemplate(GlobalVariable("@S"), [StructDef(GlobalVariable("@S"), [compute])])

        pure_func = FunctionDef(
            GlobalVariable("@Pure"), "(%arg0: !felt.type) -> !felt.type",
            [FunctionReturn([SSAVar("%arg0")], [Type("!felt.type")])],
        )
        pure_template = PolyTemplate(GlobalVariable("@Pure"), [pure_func])

        # Struct declared first, its pure-function dependency declared after.
        module = ModuleOp(
            lang=True, main_type=Type('!struct.type<@S::@S<[]>>'),
            body=[struct_template, pure_template],
        )
        ctx = TranslationContext()
        text = "".join(module.to_core(ctx))

        assert text.index("def @Pure") < text.index("call @Pure")

    def test_topo_sort_raises_on_pure_function_cycle(self):
        # Two pure functions calling each other -- mutual recursion among
        # pure functions is not supported; must fail loudly, not silently
        # emit an arbitrary (broken) order.
        a_template = self._pure_template("@A", [("@B", "%r")])
        b_template = self._pure_template("@B", [("@A", "%r")])

        module = ModuleOp(lang=True, main_type=None, body=[a_template, b_template])
        ctx = TranslationContext()
        with pytest.raises(ValueError):
            list(module.to_core(ctx))
