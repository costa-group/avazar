import pytest
from llzk_dialects.pod import PodNew, PodRead, PodWrite
from llzk_dialects.core import SSAVar, GlobalVariable, Type, TranslationContext
from llzk_dialects.core_utils import translate_assignment_core_with_ctx


class TestPod:

    # ── PodNew ────────────────────────────────────────────────────────────────

    def test_new_empty(self):
        op = PodNew.parse("%p = pod.new : !pod.type<[@x: !felt.type]>")
        assert op.result == SSAVar("%p")
        assert op.init_records == {}
        assert op.result_type == {"@x": Type("!felt.type")}

    def test_new_with_init(self):
        op = PodNew.parse("%p = pod.new {@x = %v0} : !pod.type<[@x: !felt.type]>")
        assert "@x" in op.init_records
        assert op.init_records["@x"] == SSAVar("%v0")

    def test_new_multi_init(self):
        op = PodNew.parse(
            "%p = pod.new {@x = %v0, @y = %v1} : !pod.type<[@x: !felt.type]>"
        )
        assert len(op.init_records) == 2

    def test_new_init_complex_type(self):
        # Init records contain '=' signs — match() must not split on them.
        line = ('%pod = pod.new { @count = %c2 }  : '
                '!pod.type<[@count: index, @comp: !struct.type<@S<[]>>, @params: !pod.type<[]>]>')
        op = PodNew.parse(line)
        assert op.result == SSAVar("%pod")
        assert "@count" in op.init_records
        assert op.init_records["@count"] == SSAVar("%c2")
        assert "@count" in op.result_type
        assert "@comp" in op.result_type
        assert "@params" in op.result_type
        assert op.result_type["@count"] == Type("index")
        assert op.result_type["@comp"] == Type("!struct.type<@S<[]>>")
        assert op.result_type["@params"] == Type("!pod.type<[]>")

    def test_new_empty_pod_type(self):
        op = PodNew.parse("%p = pod.new : !pod.type<[]>")
        assert op.result_type == {}

    def test_new_match(self):
        assert PodNew.match("%p = pod.new : !pod.type<[]>") is True
        assert PodNew.match("%p = pod.read %p [@x] : !t, !t") is False
        # Match must work even when init records introduce extra '=' signs.
        assert PodNew.match("%p = pod.new { @x = %v } : !pod.type<[]>") is True

    # ── PodRead ───────────────────────────────────────────────────────────────

    def test_read(self):
        op = PodRead.parse(
            "%v = pod.read %pod [@x] : !pod.type<[@x: !felt.type]>, !felt.type"
        )
        assert op.result == SSAVar("%v")
        assert op.pod_ref == SSAVar("%pod")
        assert op.record_name == GlobalVariable("@x")
        assert op.pod_type == {"@x": Type("!felt.type")}
        assert op.result_type == Type("!felt.type")

    def test_read_no_type(self):
        op = PodRead.parse("%v = pod.read %pod [@field]")
        assert op.pod_type == {}
        assert op.result_type is None

    def test_read_complex_pod_type(self):
        line = ("%v = pod.read %p [@comp] : "
                "!pod.type<[@count: index, @comp: !struct.type<@S<[]>>, @params: !pod.type<[]>]>, "
                "!struct.type<@S<[]>>")
        op = PodRead.parse(line)
        assert "@count" in op.pod_type
        assert "@comp" in op.pod_type
        assert "@params" in op.pod_type
        assert op.result_type == Type("!struct.type<@S<[]>>")

    def test_read_match(self):
        assert PodRead.match("%v = pod.read %p [@x]") is True
        assert PodRead.match("pod.write %p [@x] = %v") is False

    # ── PodWrite ──────────────────────────────────────────────────────────────

    def test_write(self):
        op = PodWrite.parse(
            "pod.write %pod [@x] = %val : !pod.type<[@x: !felt.type]>, !felt.type"
        )
        assert op.pod_ref == SSAVar("%pod")
        assert op.record_name == GlobalVariable("@x")
        assert op.value == SSAVar("%val")
        assert op.pod_type == {"@x": Type("!felt.type")}
        assert op.value_type == Type("!felt.type")

    def test_write_no_type(self):
        op = PodWrite.parse("pod.write %pod [@x] = %v")
        assert op.pod_type == {}
        assert op.value_type is None

    def test_write_complex_pod_type(self):
        line = ("pod.write %p [@count] = %c : "
                "!pod.type<[@count: index, @comp: !struct.type<@S<[]>>, @params: !pod.type<[]>]>, "
                "index")
        op = PodWrite.parse(line)
        assert "@count" in op.pod_type
        assert "@comp" in op.pod_type
        assert op.value_type == Type("index")

    def test_write_match(self):
        assert PodWrite.match("pod.write %p [@x] = %v") is True
        assert PodWrite.match("%v = pod.read %p [@x]") is False


# ── to_core ───────────────────────────────────────────────────────────────────

class TestPodToCore:
    """
    Tests for the pod-in-pod assignment fix:
      - is_ff no longer treats !pod.type as a scalar
      - empty-string yields are filtered in PodNew/PodRead/PodWrite.to_core()
    """

    def _ctx(self):
        return TranslationContext()

    # ── PodNew — scalar init ──────────────────────────────────────────────────

    def test_new_scalar_init_yields_assignment(self):
        ctx = self._ctx()
        op = PodNew.parse("%p = pod.new {@x = %v} : !pod.type<[@x: !felt.type]>")
        lines = list(op.to_core(ctx))
        assert lines == ["%p_@x = %v"]

    def test_new_registers_storage_var(self):
        ctx = self._ctx()
        op = PodNew.parse("%p = pod.new : !pod.type<[@x: !felt.type]>")
        list(op.to_core(ctx))
        assert "%p" in ctx.ssa2pod_var
        assert ctx.ssa2pod_var["%p"]["@x"][0] == "%p_@x"

    # ── PodNew — pod-typed field init (the fix) ───────────────────────────────

    def test_new_empty_pod_field_yields_nothing(self):
        ctx = self._ctx()
        ctx.ssa2pod_var["%sub"] = {}
        op = PodNew.parse(
            "%p = pod.new {@f = %sub} : !pod.type<[@f: !pod.type<[]>]>"
        )
        lines = list(op.to_core(ctx))
        assert lines == []

    def test_new_empty_pod_field_registers_storage_as_pod(self):
        ctx = self._ctx()
        ctx.ssa2pod_var["%sub"] = {}
        op = PodNew.parse(
            "%p = pod.new {@f = %sub} : !pod.type<[@f: !pod.type<[]>]>"
        )
        list(op.to_core(ctx))
        assert ctx.ssa2pod_var.get("%p_@f") == {}

    # ── PodRead — scalar field ────────────────────────────────────────────────

    def test_read_scalar_yields_assignment(self):
        ctx = self._ctx()
        ctx.ssa2pod_var["%pod"] = {"@x": ("%pod_@x", Type("!felt.type"))}
        op = PodRead.parse("%v = pod.read %pod [@x] : !pod.type<[@x: !felt.type]>, !felt.type")
        lines = list(op.to_core(ctx))
        assert lines == ["%v = %pod_@x"]

    # ── PodRead — pod-typed field (the fix) ───────────────────────────────────

    def test_read_empty_pod_field_yields_nothing(self):
        ctx = self._ctx()
        ctx.ssa2pod_var["%pod_0"] = {"@params": ("%pod_0_@params", Type("!pod.type<[]>"))}
        ctx.ssa2pod_var["%pod_0_@params"] = {}
        op = PodRead.parse(
            "%13 = pod.read %pod_0 [@params] : "
            "!pod.type<[@params: !pod.type<[]>]>, !pod.type<[]>"
        )
        lines = list(op.to_core(ctx))
        assert lines == []

    def test_read_empty_pod_field_registers_result_as_pod(self):
        ctx = self._ctx()
        ctx.ssa2pod_var["%pod_0"] = {"@params": ("%pod_0_@params", Type("!pod.type<[]>"))}
        ctx.ssa2pod_var["%pod_0_@params"] = {}
        op = PodRead.parse(
            "%13 = pod.read %pod_0 [@params] : "
            "!pod.type<[@params: !pod.type<[]>]>, !pod.type<[]>"
        )
        list(op.to_core(ctx))
        assert ctx.ssa2pod_var.get("%13") == {}

    # ── PodWrite — scalar field ───────────────────────────────────────────────

    def test_write_scalar_yields_assignment(self):
        ctx = self._ctx()
        ctx.ssa2pod_var["%pod"] = {"@x": ("%pod_@x", Type("!felt.type"))}
        op = PodWrite.parse("pod.write %pod [@x] = %v : !pod.type<[@x: !felt.type]>, !felt.type")
        lines = list(op.to_core(ctx))
        assert lines == ["%pod_@x = %v"]

    # ── PodWrite — pod-typed field (the fix) ──────────────────────────────────

    def test_write_empty_pod_field_yields_nothing(self):
        ctx = self._ctx()
        ctx.ssa2pod_var["%pod_0"] = {"@params": ("%pod_0_@params", Type("!pod.type<[]>"))}
        ctx.ssa2pod_var["%pod_0_@params"] = {}
        ctx.ssa2pod_var["%new_pod"] = {}
        op = PodWrite.parse(
            "pod.write %pod_0 [@params] = %new_pod : "
            "!pod.type<[@params: !pod.type<[]>]>, !pod.type<[]>"
        )
        lines = list(op.to_core(ctx))
        assert lines == []

    # ── Full chain: new → new (pod field) → read (the fix scenario) ──────────

    def test_pod_in_pod_chain_propagates_empty_mapping(self):
        # Mirrors the IsEqual_1 @compute pattern from subcomponents_simple_concrete.mlir:
        #   %pod = pod.new : <[]>
        #   %pod_0 = pod.new { @params = %pod } : <[@params: !pod.type<[]>]>
        #   %13 = pod.read %pod_0[@params] : ..., !pod.type<[]>
        ctx = self._ctx()

        empty_pod = PodNew.parse("%pod = pod.new : !pod.type<[]>")
        list(empty_pod.to_core(ctx))
        assert ctx.ssa2pod_var["%pod"] == {}

        pod_0 = PodNew.parse(
            "%pod_0 = pod.new {@params = %pod} : !pod.type<[@params: !pod.type<[]>]>"
        )
        list(pod_0.to_core(ctx))
        assert ctx.ssa2pod_var.get("%pod_0_@params") == {}

        read = PodRead.parse(
            "%13 = pod.read %pod_0 [@params] : "
            "!pod.type<[@params: !pod.type<[]>]>, !pod.type<[]>"
        )
        lines = list(read.to_core(ctx))
        assert lines == []
        assert ctx.ssa2pod_var.get("%13") == {}

    # ── Pod-in-pod, non-empty nested field (regression) ───────────────────────
    #
    # Previously, PodNew/ArrayRead only registered ctx.ssa2pod_var for the
    # *first* level of a pod's fields -- a non-empty pod nested inside another
    # pod never became a key itself (only its ultimate leaf got real
    # storage), so a later pod.read/pod.write chained through that
    # intermediate pod (pod-in-pod, e.g. inside an scf.while combining pods)
    # found nothing and KeyError'd. See _register_nested_pod_vars.

    def test_new_nonempty_nested_pod_field_registers_recursively(self):
        ctx = self._ctx()
        op = PodNew.parse(
            "%p = pod.new : !pod.type<[@f: !pod.type<[@in: !felt.type]>]>"
        )
        list(op.to_core(ctx))
        assert ctx.ssa2pod_var["%p_@f"]["@in"][0] == "%p_@f_@in"

    def test_new_nested_pod_field_with_array_leaf_not_misread_as_array(self):
        # Exact real-world shape that originally triggered the bug: an
        # unanchored array_felt_dimensions search matched the "<3 x
        # !felt.type<...>>" pattern nested inside @f's own type, making
        # PodNew treat @f itself as a plain felt array (emitting
        # "array.new 3 %p_@f") instead of recursing into it as a pod.
        ctx = self._ctx()
        op = PodNew.parse(
            "%p = pod.new : "
            "!pod.type<[@f: !pod.type<[@in: !array.type<3 x !felt.type<\"bn128\">>]>]>"
        )
        lines = list(op.to_core(ctx))
        assert "array.new 3 %p_@f" not in lines
        assert "array.new 3 %p_@f_@in" in lines
        assert ctx.ssa2pod_var["%p_@f"]["@in"][0] == "%p_@f_@in"

    def test_new_member_pod_nonempty_nested_field_registers_recursively(self):
        # Mirrors the real "ark.idx_0" shape from
        # poseidon3_test_concrete.mlir: a $inputs pod for a struct member
        # (semantic naming), with a non-empty nested pod field.
        ctx = self._ctx()
        ctx.input_pod_to_member["%p"] = "ark"
        op = PodNew.parse(
            "%p = pod.new : "
            "!pod.type<[@idx_0: !pod.type<[@in: !array.type<3 x !felt.type<\"bn128\">>]>]>"
        )
        lines = list(op.to_core(ctx))
        assert ctx.ssa2pod_var["%p"]["@idx_0"][0] == "ark.idx_0"
        assert ctx.ssa2pod_var["ark.idx_0"]["@in"][0] == "ark.idx_0_in"
        # The allocated storage line must target the SAME name that got
        # registered above -- previously it was derived independently via
        # _container_field_var (which never strips "@"), producing
        # "ark.idx_0_@in", a variable distinct from (and never assigned to)
        # the registered "ark.idx_0_in".
        assert lines == ["array.new 3 ark.idx_0_in"]

    def test_new_member_pod_field_with_initial_value_registers_recursively(self):
        # Same "ark.idx_0" shape as above, but the nested pod field is given
        # an explicit initial value in the pod.new record list (instead of
        # being left to _allocate_pod_field_storage) -- exercises
        # translate_assignment_core_with_ctx's own pod-copy branch directly,
        # which is the other place a member-backed lhs must end up with a
        # recursively-registered semantic destination.
        ctx = self._ctx()
        ctx.input_pod_to_member["%p"] = "ark"
        ctx.ssa2pod_var["%src"] = {
            "@in": ("%src_@in", Type("!array.type<3 x !felt.type<\"bn128\">>")),
        }
        op = PodNew.parse(
            "%p = pod.new {@idx_0 = %src} : "
            "!pod.type<[@idx_0: !pod.type<[@in: !array.type<3 x !felt.type<\"bn128\">>]>]>"
        )
        lines = list(op.to_core(ctx))
        assert ctx.ssa2pod_var["%p"]["@idx_0"][0] == "ark.idx_0"
        assert ctx.ssa2pod_var["ark.idx_0"]["@in"][0] == "ark.idx_0_in"
        assert lines == ["array.copy %src_@in ark.idx_0_in"]

    def test_translate_assignment_preserves_member_backed_lhs_semantic_dest(self):
        # Mirrors the poseidon3_test_concrete.mlir scf.while shape that
        # originally crashed: a member-backed pod (lhs, backing struct
        # member "ark") never yet registered as its own ctx.ssa2pod_var key,
        # assigned from a plain raw-SSA-named pod (rhs, mirroring an
        # llzk.nondet result). The assignment must give lhs's own "@idx_7"
        # field its semantic destination ("ark.idx_7"), not a throwaway
        # "%lhs_@idx_7" derived name -- and that destination must itself be
        # recursively registered so a later pod.read chained through it
        # ("ark.idx_7"'s own "@in" field) resolves.
        ctx = self._ctx()
        ctx.input_pod_to_member["%lhs"] = "ark"
        ctx.ssa2pod_var["%rhs"] = {
            "@idx_7": ("%rhs_@idx_7",
                      Type("!pod.type<[@in: !array.type<3 x !felt.type<\"bn128\">>]>")),
        }
        ctx.ssa2pod_var["%rhs_@idx_7"] = {
            "@in": ("%rhs_@idx_7_@in", Type("!array.type<3 x !felt.type<\"bn128\">>")),
        }

        pod_type = Type(
            "!pod.type<[@idx_7: !pod.type<[@in: !array.type<3 x !felt.type<\"bn128\">>]>]>"
        )
        lines = translate_assignment_core_with_ctx(SSAVar("%lhs"), SSAVar("%rhs"), pod_type, ctx)

        assert ctx.ssa2pod_var["%lhs"]["@idx_7"][0] == "ark.idx_7"
        assert ctx.ssa2pod_var["ark.idx_7"]["@in"][0] == "ark.idx_7_in"
        assert lines == "array.copy %rhs_@idx_7_@in ark.idx_7_in"

        # A pod.read/pod.read chain through lhs must now resolve without a
        # KeyError -- this is the exact crash this fix targets.
        read_nested = PodRead.parse(
            "%598 = pod.read %lhs [@idx_7] : "
            "!pod.type<[@idx_7: !pod.type<[@in: !array.type<3 x !felt.type<\"bn128\">>]>]>, "
            "!pod.type<[@in: !array.type<3 x !felt.type<\"bn128\">>]>"
        )
        list(read_nested.to_core(ctx))
        read_leaf = PodRead.parse(
            "%599 = pod.read %598 [@in] : "
            "!pod.type<[@in: !array.type<3 x !felt.type<\"bn128\">>]>, "
            "!array.type<3 x !felt.type<\"bn128\">>"
        )
        # previously: KeyError on "%598" inside ctx.ssa2pod_var[pod_ref.name]
        leaf_lines = list(read_leaf.to_core(ctx))
        # "@in" is array-typed and its resolved name is semantic, so
        # PodRead.to_core aliases rather than emitting a copy (an
        # array.write into it will use the alias directly) -- see
        # PodRead.to_core's own array_felt_first_dimension early-return.
        assert leaf_lines == []
        assert ctx.ssa_to_name["%599"] == "ark.idx_7_in"

    def test_pod_in_pod_chain_nonempty_field_resolves_without_keyerror(self):
        # Mirrors the poseidon3_test_concrete.mlir shape that originally
        # crashed inside an scf.while combining pods inside pods:
        #   %outer = pod.new : <[@idx_0: !pod.type<[@in: !array.type<3 x ff>]>]>
        #   %573 = pod.read %outer[@idx_0]
        #   %574 = pod.read %573[@in]
        ctx = self._ctx()

        outer = PodNew.parse(
            "%outer = pod.new : "
            "!pod.type<[@idx_0: !pod.type<[@in: !array.type<3 x !felt.type<\"bn128\">>]>]>"
        )
        list(outer.to_core(ctx))

        read_nested_pod = PodRead.parse(
            "%573 = pod.read %outer [@idx_0] : "
            "!pod.type<[@idx_0: !pod.type<[@in: !array.type<3 x !felt.type<\"bn128\">>]>]>, "
            "!pod.type<[@in: !array.type<3 x !felt.type<\"bn128\">>]>"
        )
        lines = list(read_nested_pod.to_core(ctx))
        assert lines == ["array.copy %outer_@idx_0_@in %573_@in"]
        assert ctx.ssa2pod_var["%573"]["@in"][0] == "%573_@in"

        read_leaf = PodRead.parse(
            "%574 = pod.read %573 [@in] : "
            "!pod.type<[@in: !array.type<3 x !felt.type<\"bn128\">>]>, "
            "!array.type<3 x !felt.type<\"bn128\">>"
        )
        lines = list(read_leaf.to_core(ctx))  # previously: KeyError on "%573"
        assert lines == ["array.copy %573_@in %574"]

    def test_new_init_pod_field_with_nested_struct_field_uses_pod_branch(self):
        # Regression: translate_assignment_core_with_ctx's struct-type check
        # was a plain "!struct" substring test, which also matched a POD type
        # that merely contains a struct-typed field (e.g. @comp below) --
        # treating the whole pod as if it were itself that struct's output
        # and looking up a bogus "<Struct>::@compute" entry keyed off a
        # nonsense name, instead of taking the pod-propagation branch. This
        # is the same shape as poseidon3_test_concrete.mlir's
        # "%pod_35 = pod.new {@idx_0 = %pod_20, ...}" (@idx_0's type contains
        # a @comp: !struct.type<...> field).
        ctx = self._ctx()
        ctx.llzk_func2core["@S::@S::@compute"] = "S"
        ctx.core_func2args["S"] = ([], [("@out", Type("!felt.type"))])

        src = PodNew.parse(
            "%src = pod.new {@count = %c, @comp = %s} : "
            "!pod.type<[@count: index, @comp: !struct.type<@S::@S<[]>>]>"
        )
        list(src.to_core(ctx))

        outer = PodNew.parse(
            "%outer = pod.new {@idx_0 = %src} : "
            "!pod.type<[@idx_0: !pod.type<[@count: index, @comp: !struct.type<@S::@S<[]>>]>]>"
        )
        list(outer.to_core(ctx))

        assert ctx.ssa2pod_var["%outer_@idx_0"]["@count"][0] == "%outer_@idx_0_@count"
        assert ctx.ssa2pod_var["%outer_@idx_0"]["@comp"][0] == "%outer_@idx_0_@comp"
