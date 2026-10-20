import pytest
from llzk_dialects.llzk import LLZKNondet, ModuleOp, _topo_sort_struct_templates
from llzk_dialects.core import SSAVar, Type, GlobalVariable, TranslationContext
from llzk_dialects.poly import PolyTemplate
from llzk_dialects.function import FunctionDef, FunctionReturn, FunctionCall
from llzk_dialects.struct import StructDef, StructMember
from llzk_dialects.scf import SCFWhile, SCFCondition, SCFYield
from llzk_dialects.bool import BoolCmp
from llzk_dialects.felt import FeltConst, FeltBinary


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
        # A bare scalar field with no initial value (nondet never has one for
        # ANY field) gets no placeholder -- register_and_allocate_pod shares
        # _allocate_pod_field_storage with PodNew, so it must also record
        # this field as unallocated, exactly like PodNew's own equivalent
        # case, so a later copy of it is skipped rather than referencing an
        # undefined Core variable.
        assert "%v_@x" in ctx.unallocated_pod_fields

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


# isequal_concrete.mlir (circomlib_examples_short/), verbatim: IsEqual_1 is
# declared before the IsZero_0 it instantiates -- the real frontend output
# that broke the old "struct templates are already callee-first" assumption.
ISEQUAL_FORWARD_REF_MLIR = """\
module attributes {llzk.lang = "circom", llzk.main = !struct.type<@IsEqual_1::@IsEqual_1<[]>>} {
  poly.template @IsEqual_1 {
    struct.def @IsEqual_1 {
      struct.member @out : !felt.type<"bn128"> {llzk.pub, signal}
      struct.member @isz : !struct.type<@IsZero_0::@IsZero_0<[]>>
      struct.member @isz$inputs : !pod.type<[@in: !felt.type<"bn128">]> {signal}
      function.def @compute(%arg0: !array.type<2 x !felt.type<"bn128">> {function.arg_name = "in"}) -> !struct.type<@IsEqual_1::@IsEqual_1<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
        %self = struct.new : <@IsEqual_1::@IsEqual_1<[]>>
        %pod = pod.new : <[]>
        %c1 = arith.constant 1 : index
        %pod_0 = pod.new { @count = %c1, @params = %pod }  : <[@count: index, @comp: !struct.type<@IsZero_0::@IsZero_0<[]>>, @params: !pod.type<[]>]>
        %pod_1 = pod.new : <[@in: !felt.type<"bn128">]>
        %felt_const_1 = felt.const  1 : <"bn128">
        %0 = cast.toindex %felt_const_1 : !felt.type<"bn128">
        %1 = array.read %arg0[%0] : <2 x !felt.type<"bn128">>, !felt.type<"bn128">
        %felt_const_0 = felt.const  0 : <"bn128">
        %2 = cast.toindex %felt_const_0 : !felt.type<"bn128">
        %3 = array.read %arg0[%2] : <2 x !felt.type<"bn128">>, !felt.type<"bn128">
        %4 = felt.add %1, %3 : !felt.type<"bn128">, !felt.type<"bn128">
        pod.write %pod_1[@in] = %4 : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
        %5 = pod.read %pod_0[@count] : <[@count: index, @comp: !struct.type<@IsZero_0::@IsZero_0<[]>>, @params: !pod.type<[]>]>, index
        %c1_2 = arith.constant 1 : index
        %6 = arith.subi %5, %c1_2 : index
        pod.write %pod_0[@count] = %6 : <[@count: index, @comp: !struct.type<@IsZero_0::@IsZero_0<[]>>, @params: !pod.type<[]>]>, index
        %c0 = arith.constant 0 : index
        %7 = arith.cmpi eq, %6, %c0 : index
        scf.if %7 {
          %11 = pod.read %pod_0[@params] : <[@count: index, @comp: !struct.type<@IsZero_0::@IsZero_0<[]>>, @params: !pod.type<[]>]>, !pod.type<[]>
          %12 = pod.read %pod_1[@in] : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
          %13 = function.call @IsZero_0::@IsZero_0::@compute(%12) : (!felt.type<"bn128">) -> !struct.type<@IsZero_0::@IsZero_0<[]>> 
          pod.write %pod_0[@comp] = %13 : <[@count: index, @comp: !struct.type<@IsZero_0::@IsZero_0<[]>>, @params: !pod.type<[]>]>, !struct.type<@IsZero_0::@IsZero_0<[]>>
        }
        %8 = pod.read %pod_0[@comp] : <[@count: index, @comp: !struct.type<@IsZero_0::@IsZero_0<[]>>, @params: !pod.type<[]>]>, !struct.type<@IsZero_0::@IsZero_0<[]>>
        %9 = struct.readm %8[@out] : <@IsZero_0::@IsZero_0<[]>>, !felt.type<"bn128">
        struct.writem %self[@out] = %9 : <@IsEqual_1::@IsEqual_1<[]>>, !felt.type<"bn128">
        struct.writem %self[@isz$inputs] = %pod_1 : <@IsEqual_1::@IsEqual_1<[]>>, !pod.type<[@in: !felt.type<"bn128">]>
        %10 = pod.read %pod_0[@comp] : <[@count: index, @comp: !struct.type<@IsZero_0::@IsZero_0<[]>>, @params: !pod.type<[]>]>, !struct.type<@IsZero_0::@IsZero_0<[]>>
        struct.writem %self[@isz] = %10 : <@IsEqual_1::@IsEqual_1<[]>>, !struct.type<@IsZero_0::@IsZero_0<[]>>
        function.return %self : !struct.type<@IsEqual_1::@IsEqual_1<[]>>
      }
    }
  }
  poly.template @IsZero_0 {
    struct.def @IsZero_0 {
      struct.member @out : !felt.type<"bn128"> {llzk.pub, signal}
      struct.member @inv : !felt.type<"bn128"> {signal}
      function.def @compute(%arg0: !felt.type<"bn128"> {function.arg_name = "in"}) -> !struct.type<@IsZero_0::@IsZero_0<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
        %self = struct.new : <@IsZero_0::@IsZero_0<[]>>
        %felt_const_0 = felt.const  0 : <"bn128">
        %0 = bool.cmp ne(%arg0, %felt_const_0) : !felt.type<"bn128">, !felt.type<"bn128">
        %1 = scf.if %0 -> (!felt.type<"bn128">) {
          %felt_const_1_0 = felt.const  1 : <"bn128">
          %5 = felt.div %felt_const_1_0, %arg0 : !felt.type<"bn128">, !felt.type<"bn128">
          struct.writem %self[@inv] = %5 : <@IsZero_0::@IsZero_0<[]>>, !felt.type<"bn128">
          scf.yield %5 : !felt.type<"bn128">
        } else {
          %felt_const_0_0 = felt.const  0 : <"bn128">
          struct.writem %self[@inv] = %felt_const_0_0 : <@IsZero_0::@IsZero_0<[]>>, !felt.type<"bn128">
          scf.yield %felt_const_0_0 : !felt.type<"bn128">
        }
        %2 = felt.neg %arg0 : !felt.type<"bn128">
        %3 = felt.mul %2, %1 : !felt.type<"bn128">, !felt.type<"bn128">
        %felt_const_1 = felt.const  1 : <"bn128">
        %4 = felt.add %3, %felt_const_1 : !felt.type<"bn128">, !felt.type<"bn128">
        struct.writem %self[@out] = %4 : <@IsZero_0::@IsZero_0<[]>>, !felt.type<"bn128">
        function.return %self : !struct.type<@IsZero_0::@IsZero_0<[]>>
      }
    }
  }
}
"""


class TestStructTemplateOrdering:
    """
    ModuleOp.to_core's struct-template topological sort (llzk.py's
    _topo_sort_struct_templates): a struct template may be declared before
    a subcomponent struct it instantiates, so struct templates are
    reordered among themselves, callee-first, in the slots they already
    occupy.
    """

    @staticmethod
    def _struct_template(name: str, calls: list = (), member_types: list = ()) -> PolyTemplate:
        """
        A struct poly.template @name { struct.def @name { ... } } whose
        @compute issues one function.call to `@X::@X::@compute` per X in
        `calls`, and which declares one struct.member per type string in
        `member_types`. Its own @compute signature names its own struct
        type, as every real example's does (a self-reference that must be
        ignored).
        """
        self_type = f"!struct.type<{name}::{name}<[]>>"
        members = [StructMember(GlobalVariable(f"@m{i}"), Type(t)) for i, t in enumerate(member_types)]
        body = [
            FunctionCall([SSAVar(f"%r{i}")], GlobalVariable(f"{callee}::{callee}::@compute"),
                         [SSAVar("%arg0")], None)
            for i, callee in enumerate(calls)
        ]
        body.append(FunctionReturn([SSAVar("%self")], [Type(self_type)]))
        compute = FunctionDef(GlobalVariable("@compute"), f"(%arg0: !felt.type) -> {self_type}", body)
        return PolyTemplate(GlobalVariable(name), [StructDef(GlobalVariable(name), members + [compute])])

    @staticmethod
    def _sorted_names(templates: list) -> list:
        entries = [(t, t.sym_name.name, t.body[0]) for t in templates]
        return [t.sym_name.name for t in _topo_sort_struct_templates(entries)]

    def test_call_dependency_declared_later_is_moved_first(self):
        a = self._struct_template("@A", calls=["@B"])
        b = self._struct_template("@B")
        assert self._sorted_names([a, b]) == ["@B", "@A"]

    def test_transitive_chain_in_reverse_order(self):
        a = self._struct_template("@A", calls=["@B"])
        b = self._struct_template("@B", calls=["@C"])
        c = self._struct_template("@C")
        assert self._sorted_names([a, b, c]) == ["@C", "@B", "@A"]

    def test_member_type_only_dependency(self):
        # An array-of-components member, with no call in the fixture: the
        # member declaration alone must be enough to order @B first.
        a = self._struct_template("@A", member_types=["!array.type<3 x !struct.type<@B::@B<[]>>>"])
        b = self._struct_template("@B")
        assert self._sorted_names([a, b]) == ["@B", "@A"]

    def test_idx_pod_member_dependency(self):
        # Heterogeneous array-of-components (idx-pod) member: each @idx_N
        # field's own struct type is a dependency.
        a = self._struct_template(
            "@A", member_types=["!pod.type<[@idx_0: !struct.type<@B::@B<[]>>, "
                                "@idx_1: !struct.type<@C::@C<[]>>]>"])
        b = self._struct_template("@B")
        c = self._struct_template("@C")
        assert self._sorted_names([a, b, c]) == ["@B", "@C", "@A"]

    def test_already_ordered_and_independent_keep_source_order(self):
        b = self._struct_template("@B")
        a = self._struct_template("@A", calls=["@B"])
        x = self._struct_template("@X")
        assert self._sorted_names([b, x, a]) == ["@B", "@X", "@A"]

    def test_self_reference_and_unknown_template_are_ignored(self):
        # @A names itself (signature/return type) and a pure function
        # template that isn't a struct template -- neither is a struct
        # dependency, so no cycle and no KeyError.
        a = self._struct_template("@A", calls=["@Pure"])
        assert self._sorted_names([a]) == ["@A"]

    def test_struct_cycle_raises(self):
        a = self._struct_template("@A", calls=["@B"])
        b = self._struct_template("@B", calls=["@A"])
        with pytest.raises(ValueError):
            self._sorted_names([a, b])

    def test_forward_referenced_subcomponent_real_fixture(self):
        # Full parse + translation of the real isequal_concrete.mlir: used
        # to crash with KeyError '@IsZero_0::@IsZero_0::@compute'.
        from execution.main_execution import init_llzk_parser
        module = init_llzk_parser(ISEQUAL_FORWARD_REF_MLIR.splitlines(keepends=True)).parse()[0]
        text = "".join(module.to_core(TranslationContext()))

        assert text.index("def @IsZero_0") < text.index("def @IsEqual_1")
        assert text.index("def @IsZero_0") < text.index("call @IsZero_0")
        assert text.index("def @IsEqual_1") < text.index("def main")


class TestPureFunctionSpecialization:
    """
    ModuleOp.to_core's loop-bound-parametric pure function specialization
    pre-pass (llzk.py's _specialize_loop_bound_parametric_pure_functions):
    a pure function whose own while-loop bound depends on one of its own
    parameters gets cloned once per distinct compile-time-constant value
    that parameter takes across all its call sites -- mirrors
    EscalarMulW4Table_0's real shape (escalarmulw4table_concrete.mlir),
    whose bound `arg3 < arg1*4` depends on its own "k" parameter.
    """

    @staticmethod
    def _table_template() -> PolyTemplate:
        """
        A pure function @Table(%arg0 aka "k") -> felt, counting from 0 up
        to its own parameter (bound = %arg0 directly, no arithmetic needed
        to keep the fixture minimal) and returning the while's own external
        result. Structurally the same shape as EscalarMulW4Table_0's
        problematic loop: the bound is unresolvable within the function's
        own scope alone, since %arg0 is a parameter, not a loop-carried
        variable or a literal.
        """
        felt = Type('!felt.type<"bn128">')
        after_body = [
            FeltConst(SSAVar("%c1"), 1),
            FeltBinary(SSAVar("%next"), "felt.add", SSAVar("%ctr"), SSAVar("%c1"), []),
            SCFYield([SSAVar("%next")], [felt]),
        ]
        before_body = [
            BoolCmp(SSAVar("%cond"), "lt", SSAVar("%ctr"), SSAVar("%arg0")),
            SCFCondition(SSAVar("%cond"), [SSAVar("%ctr")], [felt]),
        ]
        while_op = SCFWhile(
            [SSAVar("%result")], [(SSAVar("%ctr"), SSAVar("%c0"))], [[felt], [felt]],
            before_body, [(SSAVar("%ctr"), felt)], after_body,
        )
        func = FunctionDef(
            GlobalVariable("@Table"),
            '(%arg0: !felt.type<"bn128"> {function.arg_name = "k"}) -> !felt.type<"bn128">',
            [FeltConst(SSAVar("%c0"), 0), while_op, FunctionReturn([SSAVar("%result")], [felt])],
        )
        return PolyTemplate(GlobalVariable("@Table"), [func])

    @staticmethod
    def _caller_compute(calls_and_values: list) -> PolyTemplate:
        """
        A @Main struct's @compute calling @Table once per (result_name,
        value) pair in calls_and_values, each with a fresh felt.const
        argument -- mirrors Main_0::@compute's real call sites in
        escalarmulw4table_concrete.mlir.
        """
        felt = Type('!felt.type<"bn128">')
        body = []
        for result_name, value in calls_and_values:
            const_name = f"%c_{result_name.lstrip('%')}"
            body.append(FeltConst(SSAVar(const_name), value))
            body.append(FunctionCall(
                [SSAVar(result_name)], GlobalVariable("@Table::@Table"),
                [SSAVar(const_name)], None,
            ))
        ret_val = calls_and_values[-1][0] if calls_and_values else "%c0"
        body.append(FunctionReturn([SSAVar(ret_val)], [felt]))
        compute = FunctionDef(GlobalVariable("@compute"), "() -> !felt.type<\"bn128\">", body)
        return PolyTemplate(GlobalVariable("@Main"), [StructDef(GlobalVariable("@Main"), [compute])])

    def _translate(self, calls_and_values: list) -> 'tuple[str, TranslationContext]':
        table_template = self._table_template()
        struct_template = self._caller_compute(calls_and_values)
        module = ModuleOp(
            lang=True, main_type=Type('!struct.type<@Main::@Main<[]>>'),
            body=[struct_template, table_template],
        )
        ctx = TranslationContext()
        text = "".join(module.to_core(ctx))
        return text, ctx

    def test_single_constant_value_keeps_original_name(self):
        # Every call site (just one, here) passes the same constant (3):
        # no need to rename -- the generic def is specialized in place.
        text, ctx = self._translate([("%r0", 3)])

        assert "def @Table(" in text
        assert "repeat 3 {" in text
        assert "call @Table(" in text
        assert "@Table::@Table" in ctx.pure_function_specializations
        assert ctx.pure_function_specializations["@Table::@Table"] == [("@Table", {"%arg0": 3})]

    def test_multiple_distinct_values_get_suffixed_clones(self):
        # Two call sites with different constants (1 and 2) -- mirrors
        # escalarmul_test_concrete.mlir's 64 distinct-k call sites (one per
        # scalar-multiplication window). Each gets its own clone, named
        # using the "k" function.arg_name (not the raw "%arg0" SSA name).
        text, ctx = self._translate([("%r1", 1), ("%r2", 2)])

        assert "def @Table__k1(" in text
        assert "def @Table__k2(" in text
        assert "repeat 1 {" in text
        assert "repeat 2 {" in text
        assert "call @Table__k1(" in text
        assert "call @Table__k2(" in text
        # The generic, unspecialized def must not survive alongside the
        # clones -- every call site was resolved and redirected.
        assert "def @Table(" not in text

        specs = ctx.pure_function_specializations["@Table::@Table"]
        assert sorted(specs) == [
            ("@Table__k1", {"%arg0": 1}),
            ("@Table__k2", {"%arg0": 2}),
        ]

    def test_unresolvable_call_argument_leaves_function_unspecialized(self):
        # The call's own argument (%witness) has no defining operation
        # anywhere in the calling function's body -- mirrors
        # pointbits_loopback_concrete.mlir's sqrt_0, whose parameter traces
        # back to a genuine runtime witness signal, never a constant. The
        # whole function must be left exactly as today: one generic def,
        # no specialization entry, no renamed call site.
        felt = Type('!felt.type<"bn128">')
        call = FunctionCall([SSAVar("%r")], GlobalVariable("@Table::@Table"), [SSAVar("%witness")], None)
        compute = FunctionDef(
            GlobalVariable("@compute"), "() -> !felt.type<\"bn128\">",
            [call, FunctionReturn([SSAVar("%r")], [felt])],
        )
        struct_template = PolyTemplate(GlobalVariable("@Main"), [StructDef(GlobalVariable("@Main"), [compute])])
        table_template = self._table_template()

        module = ModuleOp(
            lang=True, main_type=Type('!struct.type<@Main::@Main<[]>>'),
            body=[struct_template, table_template],
        )
        ctx = TranslationContext()
        text = "".join(module.to_core(ctx))

        assert "@Table::@Table" not in ctx.pure_function_specializations
        assert text.count("def @Table(") == 1
        assert "call @Table(" in text


class TestNestedModuleGlobals:
    """
    Nested `module @global { global.def const ... }` (circom-llzk's real
    shape, e.g. poseidon3_test_concrete.mlir): array globals are emitted
    once, in a leading `globals { name: [..] }` block, and each
    `global.read const @mod::@x` either aliases its uses to the global's
    Core name `@mod_@x` (never written to) or copies it (written to later).
    """

    @staticmethod
    def _translate(globals_text: str, body: str) -> str:
        from execution.main_execution import init_llzk_parser
        text = f"""\
module attributes {{llzk.lang = "circom", llzk.main = !struct.type<@Main_0::@Main_0<[]>>}} {{
{globals_text}
  poly.template @Main_0 {{
    struct.def @Main_0 {{
      struct.member @out : !felt.type<"bn128"> {{llzk.pub, signal}}
      function.def @compute(%arg0: !felt.type<"bn128"> {{function.arg_name = "in"}}) -> !struct.type<@Main_0::@Main_0<[]>> attributes {{function.allow_witness}} {{
        %self = struct.new : <@Main_0::@Main_0<[]>>
{body}
        struct.writem %self[@out] = %r : <@Main_0::@Main_0<[]>>, !felt.type<"bn128">
        function.return %self : !struct.type<@Main_0::@Main_0<[]>>
      }}
      function.def @constrain(%arg0: !struct.type<@Main_0::@Main_0<[]>>, %arg1: !felt.type<"bn128"> {{function.arg_name = "in"}}) attributes {{function.allow_constraint}} {{
        function.return
      }}
    }}
  }}
}}
"""
        module = init_llzk_parser(text.splitlines(keepends=True)).parse()[0]
        return "".join(line + "\n" for line in module.to_core(TranslationContext()))

    GLOBAL_ARR = """\
  module @global {
    global.def const @arr : !array.type<2 x !felt.type<"bn128">> = [ 7 : <"bn128">,  8 : <"bn128">]
  }"""

    def test_globals_block_emitted_first_and_aliased_read(self):
        text = self._translate(self.GLOBAL_ARR, """\
        %0 = global.read const @global::@arr : !array.type<2 x !felt.type<"bn128">>
        %c1 = arith.constant 1 : index
        %r = array.read %0[%c1] : <2 x !felt.type<"bn128">>, !felt.type<"bn128">""")

        assert text.startswith("globals {\n@global_@arr: [7, 8]\n}\n")
        assert "array.read @global_@arr[%c1] %r" in text
        # An aliased read emits nothing of its own.
        assert "%0" not in text

    def test_written_read_is_copied(self):
        text = self._translate(self.GLOBAL_ARR, """\
        %0 = global.read const @global::@arr : !array.type<2 x !felt.type<"bn128">>
        %c0 = arith.constant 0 : index
        array.write %0[%c0] = %arg0 : <2 x !felt.type<"bn128">>, !felt.type<"bn128">
        %r = array.read %0[%c0] : <2 x !felt.type<"bn128">>, !felt.type<"bn128">""")

        assert "array.copy @global_@arr %0" in text
        assert "array.write %arg0 %0[%c0]" in text
        assert "array.read %0[%c0] %r" in text
        # The shared global itself is never written to.
        assert "array.write %arg0 @global_@arr" not in text

    def test_sibling_region_same_name_is_untouched(self):
        # %2 reads the global in the then-branch; an unrelated %2 in the
        # else-branch (SSA names reused across sibling regions) must keep
        # its own name.
        text = self._translate(self.GLOBAL_ARR, """\
        %felt_const_1 = felt.const  1 : <"bn128">
        %0 = bool.cmp eq(%arg0, %felt_const_1) : !felt.type<"bn128">, !felt.type<"bn128">
        %r = scf.if %0 -> (!felt.type<"bn128">) {
          %2 = global.read const @global::@arr : !array.type<2 x !felt.type<"bn128">>
          %c0 = arith.constant 0 : index
          %3 = array.read %2[%c0] : <2 x !felt.type<"bn128">>, !felt.type<"bn128">
          scf.yield %3 : !felt.type<"bn128">
        } else {
          %2 = felt.add %arg0, %felt_const_1 : !felt.type<"bn128">, !felt.type<"bn128">
          scf.yield %2 : !felt.type<"bn128">
        }""")

        assert "array.read @global_@arr[%c0] %3" in text
        assert "%2 = felt.add %arg0 %felt_const_1" in text

    def test_two_modules_same_global_name(self):
        text = self._translate("""\
  module @mod1 {
    global.def const @arr : !array.type<1 x !felt.type<"bn128">> = [ 1 : <"bn128">]
  }
  module @mod2 {
    global.def const @arr : !array.type<1 x !felt.type<"bn128">> = [ 2 : <"bn128">]
  }""", """\
        %0 = global.read const @mod1::@arr : !array.type<1 x !felt.type<"bn128">>
        %1 = global.read const @mod2::@arr : !array.type<1 x !felt.type<"bn128">>
        %c0 = arith.constant 0 : index
        %2 = array.read %0[%c0] : <1 x !felt.type<"bn128">>, !felt.type<"bn128">
        %3 = array.read %1[%c0] : <1 x !felt.type<"bn128">>, !felt.type<"bn128">
        %r = felt.add %2, %3 : !felt.type<"bn128">, !felt.type<"bn128">""")

        assert text.startswith("globals {\n@mod1_@arr: [1]\n@mod2_@arr: [2]\n}\n")
        assert "array.read @mod1_@arr[%c0] %2" in text
        assert "array.read @mod2_@arr[%c0] %3" in text

    def test_2d_global_is_flattened(self):
        text = self._translate("""\
  module @global {
    global.def const @m : !array.type<2,2 x !felt.type<"bn128">> = [ 1 : <"bn128">,  2 : <"bn128">,  3 : <"bn128">,  4 : <"bn128">]
  }""", """\
        %0 = global.read const @global::@m : !array.type<2,2 x !felt.type<"bn128">>
        %c1 = arith.constant 1 : index
        %r = array.read %0[%c1, %c1] : <2,2 x !felt.type<"bn128">>, !felt.type<"bn128">""")

        assert "@global_@m: [1, 2, 3, 4]" in text
        assert "@global_@m[" in text

    def test_whole_array_alias_passed_to_call(self):
        from llzk_dialects.global_ import GlobalRead
        from llzk_dialects.llzk import _alias_global_reads
        from llzk_dialects.global_ import _register_global_def, GlobalDef

        ctx = TranslationContext()
        _register_global_def(GlobalDef.parse(
            'global.def const @arr : !array.type<2 x !felt.type<"bn128">> = [ 7 : <"bn128">,  8 : <"bn128">]'
        ), ctx, "@global")
        read = GlobalRead.parse('%0 = global.read const @global::@arr : !array.type<2 x !felt.type<"bn128">>')
        call = FunctionCall([SSAVar("%1")], GlobalVariable("@F::@F"), [SSAVar("%0")], None)
        _alias_global_reads([read, call], ctx)

        assert read.aliased
        assert call.args[0].name == "@global_@arr"

    def test_loop_carried_init_counts_as_written(self):
        from llzk_dialects.global_ import GlobalRead, GlobalDef, _register_global_def
        from llzk_dialects.llzk import _alias_global_reads
        from llzk_dialects.scf import SCFFor

        ctx = TranslationContext()
        _register_global_def(GlobalDef.parse(
            'global.def const @arr : !array.type<2 x !felt.type<"bn128">> = [ 7 : <"bn128">,  8 : <"bn128">]'
        ), ctx, "@global")
        read = GlobalRead.parse('%0 = global.read const @global::@arr : !array.type<2 x !felt.type<"bn128">>')
        loop = SCFFor([SSAVar("%res")], SSAVar("%i"), SSAVar("%lb"), SSAVar("%ub"), SSAVar("%st"),
                      [(SSAVar("%acc"), SSAVar("%0"))], [])
        _alias_global_reads([read, loop], ctx)

        assert not read.aliased
        assert loop.iter_args[0][1].name == "%0"

    def test_scalar_global_is_inlined_not_listed(self):
        text = self._translate("""\
  module @global {
    global.def const @s : !felt.type<"bn128"> = 5 : <"bn128">
  }""", """\
        %0 = global.read const @global::@s : !felt.type<"bn128">
        %r = felt.add %0, %arg0 : !felt.type<"bn128">, !felt.type<"bn128">""")

        assert "globals {" not in text
        assert "%0 = 5" in text

    def test_top_level_global_unified_under_bare_name(self):
        text = self._translate("""\
  global.def const @arr : !array.type<2 x !felt.type<"bn128">> = [ 7 : <"bn128">,  8 : <"bn128">]""", """\
        %0 = global.read @arr : !array.type<2 x !felt.type<"bn128">>
        %c1 = arith.constant 1 : index
        %r = array.read %0[%c1] : <2 x !felt.type<"bn128">>, !felt.type<"bn128">""")

        assert text.startswith("globals {\n@arr: [7, 8]\n}\n")
        assert "array.read @arr[%c1] %r" in text

    def test_nested_module_with_non_global_op_is_rejected(self):
        with pytest.raises(NotImplementedError):
            self._translate("""\
  module @IsZero_0 {
    struct.def @IsZero_0 {
      struct.member @out : !felt.type<"bn128"> {llzk.pub, signal}
    }
  }""", """\
        %r = felt.const  1 : <"bn128">""")
