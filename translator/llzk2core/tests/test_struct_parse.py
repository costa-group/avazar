import pytest
from llzk_dialects.struct import (
    StructMember, StructNew, StructReadm, StructWritem, StructDef,
    _annotate_function_calls, _fold_index_constants, _find_array_component_bases,
    _annotate_array_component_reads, _build_component_naming_maps,
    _is_idx_pod_component_member, _idx_read_matches_member, _annotate_idx_pod_component_reads,
    _is_population_write, _trace_to_enclosing_loop, _loop_own_sequence,
    _resolve_population_nest_sequence, _collect_population_write_candidates,
    _walk_array_component_population, _find_array_component_population_sequences,
)
from llzk_dialects.function import FunctionCall
from llzk_dialects.pod import PodNew, PodWrite, PodRead
from llzk_dialects.scf import SCFIf, SCFFor, SCFWhile, SCFCondition, SCFYield
from llzk_dialects.array import ArrayRead, ArrayWrite
from llzk_dialects.arith import ArithConst
from llzk_dialects.cast import CastToIndex
from llzk_dialects.core import SSAVar, GlobalVariable, Type, TranslationContext
from llzk_dialects.felt import FeltConst, FeltBinary
from llzk_dialects.bool import BoolCmp


class TestStruct:

    # ── StructMember ──────────────────────────────────────────────────────────

    def test_member_basic(self):
        op = StructMember.parse("struct.member @x : !felt.type")
        assert op.sym_name == GlobalVariable("@x")
        assert op.member_type == Type("!felt.type")
        assert op.is_column is False
        assert op.is_signal is False

    def test_member_column(self):
        op = StructMember.parse("struct.member @col : !felt.type {column}")
        assert op.is_column is True
        assert op.is_signal is False

    def test_member_signal(self):
        op = StructMember.parse("struct.member @sig : !felt.type {signal}")
        assert op.is_signal is True

    def test_member_invalid(self):
        with pytest.raises(ValueError):
            StructMember.parse("struct.member @x")  # missing type

    def test_member_pod_type_with_spaces(self):
        line = ('struct.member @inputs : '
                '!pod.type<[@in1: !felt.type<"bn128">, @in2: !felt.type<"bn128">]>')
        op = StructMember.parse(line)
        assert op.sym_name == GlobalVariable("@inputs")
        assert '!pod.type' in op.member_type.name
        assert op.is_column is False

    def test_member_pod_type_with_spaces_and_attr(self):
        line = ('struct.member @inputs : '
                '!pod.type<[@in1: !felt.type, @in2: !felt.type]> {column}')
        op = StructMember.parse(line)
        assert '!pod.type' in op.member_type.name
        assert op.is_column is True

    def test_member_match(self):
        assert StructMember.match("struct.member @x : !felt.type") is True
        assert StructMember.match("struct.new : !struct.type<@S>") is False

    # ── StructNew ─────────────────────────────────────────────────────────────

    def test_new(self):
        op = StructNew.parse("%s = struct.new : !struct.type<@Reg>")
        assert op.result == SSAVar("%s")
        assert op.result_type == Type("!struct.type<@Reg>")

    def test_new_whitespace(self):
        op = StructNew.parse("  %self = struct.new : !struct.type<@MyComp>  ")
        assert op.result == SSAVar("%self")

    def test_new_invalid(self):
        with pytest.raises(ValueError):
            StructNew.parse("%s = struct.new")  # missing type

    def test_new_match(self):
        assert StructNew.match("%s = struct.new : !struct.type<@R>") is True
        assert StructNew.match("struct.member @x : !felt.type") is False

    # ── StructReadm ───────────────────────────────────────────────────────────

    def test_readm(self):
        op = StructReadm.parse(
            "%v = struct.readm %self [@x] : !struct.type<@R>, !felt.type"
        )
        assert op.result == SSAVar("%v")
        assert op.component == SSAVar("%self")
        assert op.member_name == GlobalVariable("@x")
        assert len(op.types) == 2

    def test_readm_no_type(self):
        op = StructReadm.parse("%v = struct.readm %s [@field]")
        assert op.types == []

    def test_readm_match(self):
        assert StructReadm.match("%v = struct.readm %s [@x]") is True
        assert StructReadm.match("struct.writem %s [@x] = %v") is False

    # ── StructWritem ──────────────────────────────────────────────────────────

    def test_writem(self):
        op = StructWritem.parse(
            "struct.writem %self [@x] = %val : !struct.type<@R>, !felt.type"
        )
        assert op.component == SSAVar("%self")
        assert op.member_name == GlobalVariable("@x")
        assert op.value == SSAVar("%val")

    def test_writem_no_type(self):
        op = StructWritem.parse("struct.writem %s [@f] = %v")
        assert op.types == []

    def test_writem_match(self):
        assert StructWritem.match("struct.writem %s [@x] = %v") is True
        assert StructWritem.match("%v = struct.readm %s [@x]") is False

    # ── StructDef (BlockOperation) ────────────────────────────────────────────

    def _parse_fn(self, start, end):
        """Minimal parse_fn that delegates to FeltConst for body lines."""
        ops = []
        for i in range(start, end):
            line = self.lines[i].strip()
            if not line or line == "}":
                continue
            if StructMember.match(line):
                ops.append(StructMember.parse(line))
            elif FeltConst.match(line):
                ops.append(FeltConst.parse(line))
        return ops

    def test_struct_def_empty(self):
        self.lines = [
            "struct.def @Empty {",
            "}",
        ]
        op, next_cur = StructDef.parse(self.lines, 0, self._parse_fn)
        assert op.sym_name == GlobalVariable("@Empty")
        assert op.body == []
        assert next_cur == 2

    def test_struct_def_with_members(self):
        self.lines = [
            "struct.def @Reg {",
            "struct.member @x : !felt.type",
            "struct.member @y : !felt.type",
            "}",
        ]
        op, next_cur = StructDef.parse(self.lines, 0, self._parse_fn)
        assert op.sym_name == GlobalVariable("@Reg")
        assert len(op.body) == 2
        assert next_cur == 4

    def test_struct_def_match(self):
        assert StructDef.match("struct.def @MyComp {") is True
        assert StructDef.match("struct.new : !struct.type<@S>") is False


# ── _annotate_function_calls ──────────────────────────────────────────────────

class TestAnnotateFunctionCalls:
    """
    Tests for _annotate_function_calls.

    The core invariant: each FunctionCall Python object is annotated with the
    member name of the component pod it is written into, determined by a
    per-body SSA def-map so that sibling scf.if branches which reuse the same
    SSA name never overwrite each other's hints.
    """

    # ── helpers ───────────────────────────────────────────────────────────────

    def _call(self, ssa="%call"):
        return FunctionCall([SSAVar(ssa)], GlobalVariable("@Sub"), [], None)

    def _pod_write(self, pod, ssa="%call"):
        return PodWrite(SSAVar(pod), GlobalVariable("@comp"), SSAVar(ssa), {}, None)

    def _pod_new_with_comp(self, pod_result, comp_ssa="%call"):
        return PodNew(SSAVar(pod_result), {"@comp": SSAVar(comp_ssa)}, {})

    def _if(self, body, cond="%cond"):
        return SCFIf([], SSAVar(cond), [], body, None)

    # ── flat body ─────────────────────────────────────────────────────────────

    def test_flat_call_and_write_annotated(self):
        call = self._call()
        write = self._pod_write("%pod_a")
        _annotate_function_calls([call, write], {"%pod_a": "comp_a"})
        assert call._member_hint == "comp_a"

    def test_pod_not_in_map_leaves_hint_none(self):
        call = self._call()
        write = self._pod_write("%pod_a")
        _annotate_function_calls([call, write], {"%pod_x": "other"})
        assert call._member_hint is None

    def test_pod_new_comp_field_annotated(self):
        call = self._call()
        pod_new = self._pod_new_with_comp("%pod_a")
        _annotate_function_calls([call, pod_new], {"%pod_a": "cst"})
        assert call._member_hint == "cst"

    # ── sibling scf.if branches — the regression ─────────────────────────────

    def test_sibling_ifs_same_ssa_name_get_distinct_hints(self):
        """
        Two sibling scf.if blocks both define %call as a FunctionCall result
        and each stores it into a different component pod.  Before the fix the
        second write would overwrite the first in a flat dict, so both calls
        got the second member name.  After the fix each call object carries its
        own correct hint.
        """
        call_a = self._call()        # %call in first if-body
        call_b = self._call()        # %call in second if-body — same SSA name, distinct object
        if_a = self._if([call_a, self._pod_write("%pod_a")], cond="%c0")
        if_b = self._if([call_b, self._pod_write("%pod_b")], cond="%c1")

        _annotate_function_calls(
            [if_a, if_b],
            {"%pod_a": "n2ba", "%pod_b": "n2bb"},
        )

        assert call_a._member_hint == "n2ba"
        assert call_b._member_hint == "n2bb"

    def test_sibling_ifs_first_hint_not_overwritten(self):
        """Regression guard: first call must not silently receive the second member."""
        call_a = self._call()
        call_b = self._call()
        if_a = self._if([call_a, self._pod_write("%pod_a")], cond="%c0")
        if_b = self._if([call_b, self._pod_write("%pod_b")], cond="%c1")

        _annotate_function_calls(
            [if_a, if_b],
            {"%pod_a": "n2ba", "%pod_b": "n2bb"},
        )

        assert call_a._member_hint != "n2bb", \
            "first call must not receive the second branch's member name"

    # ── deeper nesting ────────────────────────────────────────────────────────

    def test_call_inside_nested_if_annotated(self):
        call = self._call()
        inner_if = self._if([call, self._pod_write("%pod_a")])
        outer_if = self._if([inner_if])
        _annotate_function_calls([outer_if], {"%pod_a": "deep"})
        assert call._member_hint == "deep"

    def test_multiple_pods_same_body(self):
        call_x = self._call("%cx")
        call_y = self._call("%cy")
        write_x = self._pod_write("%pod_x", "%cx")
        write_y = self._pod_write("%pod_y", "%cy")
        _annotate_function_calls(
            [call_x, write_x, call_y, write_y],
            {"%pod_x": "x", "%pod_y": "y"},
        )
        assert call_x._member_hint == "x"
        assert call_y._member_hint == "y"

    # ── no FunctionCall defining the stored SSA var ───────────────────────────

    def test_write_without_matching_call_is_ignored(self):
        # %call is never defined in this body — no crash, no annotation
        write = self._pod_write("%pod_a")
        _annotate_function_calls([write], {"%pod_a": "a"})  # should not raise


# ── _fold_index_constants ──────────────────────────────────────────────────────

class TestFoldIndexConstants:
    """
    Static (pre-to_core) constant folding used to attribute a specific
    array-of-components slot (e.g. "last#0") to its counting-pod read,
    ahead of when ctx.var2const would normally be populated.
    """

    def test_felt_const_folded(self):
        const = FeltConst(SSAVar("%c0"), 0)
        assert _fold_index_constants([const]) == {"%c0": 0}

    def test_arith_const_folded(self):
        const = ArithConst(SSAVar("%c1"), "1", Type("index"))
        assert _fold_index_constants([const]) == {"%c1": 1}

    def test_cast_to_index_propagates(self):
        const = FeltConst(SSAVar("%fc"), 2)
        cast = CastToIndex(SSAVar("%idx"), SSAVar("%fc"))
        assert _fold_index_constants([const, cast]) == {"%fc": 2, "%idx": 2}

    def test_non_constant_source_not_folded(self):
        # %idx casts a value that was never defined as a constant in this
        # body — must not appear in the resulting map.
        cast = CastToIndex(SSAVar("%idx"), SSAVar("%arg0"))
        assert _fold_index_constants([cast]) == {}


# ── _find_array_component_bases ────────────────────────────────────────────────

class TestFindArrayComponentBases:
    """
    Detects the counting-pod array backing an array-of-subcomponent member,
    from the bulk-copy scf.for loop that reads each element's @comp field
    into the array later struct-written as that member.
    """

    def _bulk_copy_loop(self, counting_arr="%array", target_arr="%array_13", iv="%iv"):
        read = ArrayRead(SSAVar("%elem"), SSAVar(counting_arr), [SSAVar(iv)], [])
        comp = PodRead(SSAVar("%comp"), SSAVar("%elem"), GlobalVariable("@comp"), {}, None)
        write = ArrayWrite(SSAVar(target_arr), [SSAVar(iv)], SSAVar("%comp"), [])
        return SCFFor([], SSAVar(iv), SSAVar("%lb"), SSAVar("%ub"), SSAVar("%step"), [], [read, comp, write])

    def test_detects_counting_array_to_member(self):
        loop = self._bulk_copy_loop()
        writem = StructWritem(SSAVar("%self"), GlobalVariable("@last"), SSAVar("%array_13"),
                              [Type("!array.type<2 x !struct.type<@X>>")])
        assert _find_array_component_bases([loop, writem]) == {"%array": "last"}

    def test_inputs_member_ignored(self):
        # A "$inputs" array member write must not be mistaken for the
        # array-of-struct-component pattern.
        loop = self._bulk_copy_loop()
        writem = StructWritem(SSAVar("%self"), GlobalVariable("@last_inputs"), SSAVar("%array_13"),
                              [Type("!array.type<2 x !pod.type<[@x: !felt.type]>>")])
        assert _find_array_component_bases([loop, writem]) == {}

    def test_no_matching_loop_yields_empty(self):
        writem = StructWritem(SSAVar("%self"), GlobalVariable("@last"), SSAVar("%array_13"),
                              [Type("!array.type<2 x !struct.type<@X>>")])
        assert _find_array_component_bases([writem]) == {}

    def test_loop_indexed_by_other_variable_ignored(self):
        # The array.read/write inside the loop use a different index than
        # the loop's own induction variable — not the bulk-copy pattern.
        read = ArrayRead(SSAVar("%elem"), SSAVar("%array"), [SSAVar("%other")], [])
        comp = PodRead(SSAVar("%comp"), SSAVar("%elem"), GlobalVariable("@comp"), {}, None)
        write = ArrayWrite(SSAVar("%array_13"), [SSAVar("%other")], SSAVar("%comp"), [])
        loop = SCFFor([], SSAVar("%iv"), SSAVar("%lb"), SSAVar("%ub"), SSAVar("%step"), [], [read, comp, write])
        writem = StructWritem(SSAVar("%self"), GlobalVariable("@last"), SSAVar("%array_13"),
                              [Type("!array.type<2 x !struct.type<@X>>")])
        assert _find_array_component_bases([loop, writem]) == {}

    def test_2d_nested_bulk_copy_detected(self):
        # A 2-D array-of-components member (e.g. "@sigmaF : !array.type<8,3
        # x !struct.type<...>>") is bulk-copied by TWO nested scf.for loops
        # -- one per dimension -- with the innermost holding the triple
        # indexed by BOTH enclosing loops' induction variables, in order.
        read = ArrayRead(SSAVar("%elem"), SSAVar("%array"), [SSAVar("%j"), SSAVar("%i")], [])
        comp = PodRead(SSAVar("%comp"), SSAVar("%elem"), GlobalVariable("@comp"), {}, None)
        write = ArrayWrite(SSAVar("%array_13"), [SSAVar("%j"), SSAVar("%i")], SSAVar("%comp"), [])
        inner_loop = SCFFor([], SSAVar("%i"), SSAVar("%lb_i"), SSAVar("%ub_i"), SSAVar("%step_i"),
                            [], [read, comp, write])
        outer_loop = SCFFor([], SSAVar("%j"), SSAVar("%lb_j"), SSAVar("%ub_j"), SSAVar("%step_j"),
                            [], [inner_loop])
        writem = StructWritem(SSAVar("%self"), GlobalVariable("@sigmaF"), SSAVar("%array_13"),
                              [Type("!array.type<8,3 x !struct.type<@X>>")])
        assert _find_array_component_bases([outer_loop, writem]) == {"%array": "sigmaF"}

    def test_2d_nested_loop_with_mismatched_inner_index_count_ignored(self):
        # The innermost triple is indexed by only ONE of the two enclosing
        # loops' induction variables (not the full N-D bulk-copy shape) --
        # must not be misdetected.
        read = ArrayRead(SSAVar("%elem"), SSAVar("%array"), [SSAVar("%i")], [])
        comp = PodRead(SSAVar("%comp"), SSAVar("%elem"), GlobalVariable("@comp"), {}, None)
        write = ArrayWrite(SSAVar("%array_13"), [SSAVar("%i")], SSAVar("%comp"), [])
        inner_loop = SCFFor([], SSAVar("%i"), SSAVar("%lb_i"), SSAVar("%ub_i"), SSAVar("%step_i"),
                            [], [read, comp, write])
        outer_loop = SCFFor([], SSAVar("%j"), SSAVar("%lb_j"), SSAVar("%ub_j"), SSAVar("%step_j"),
                            [], [inner_loop])
        writem = StructWritem(SSAVar("%self"), GlobalVariable("@sigmaF"), SSAVar("%array_13"),
                              [Type("!array.type<8,3 x !struct.type<@X>>")])
        assert _find_array_component_bases([outer_loop, writem]) == {}


# ── _annotate_array_component_reads ────────────────────────────────────────────

class TestAnnotateArrayComponentReads:
    """
    Recursive walk that names a counting-pod array read either "base#idx"
    (one "#idx" segment per dimension, when every index is a compile-time
    constant) or the bare "base" (any index non-constant, e.g. a real
    scf.while iteration variable), feeding the same pod_to_member map that
    _annotate_function_calls consumes.
    """

    def test_constant_index_gets_subindex_name(self):
        const = FeltConst(SSAVar("%c0"), 0)
        cast = CastToIndex(SSAVar("%i0"), SSAVar("%c0"))
        read = ArrayRead(SSAVar("%8"), SSAVar("%array"), [SSAVar("%i0")], [])
        pod_to_member = {}
        _annotate_array_component_reads([const, cast, read], {"%array": "last"}, {}, pod_to_member)
        assert pod_to_member["%8"] == "last#0"

    def test_non_constant_index_gets_bare_name(self):
        # %arg4 is never folded to a constant anywhere — a genuine loop var.
        # There's no single instance to name more specifically at
        # translation time, so this resolves to the bare base name.
        read = ArrayRead(SSAVar("%15"), SSAVar("%array"), [SSAVar("%arg4")], [])
        pod_to_member = {}
        _annotate_array_component_reads([read], {"%array": "Num2Bits_16_325"}, {}, pod_to_member)
        assert pod_to_member["%15"] == "Num2Bits_16_325"

    def test_recurses_into_nested_body_using_inherited_constants(self):
        const = FeltConst(SSAVar("%c1"), 1)
        cast = CastToIndex(SSAVar("%i1"), SSAVar("%c1"))
        read = ArrayRead(SSAVar("%9"), SSAVar("%array"), [SSAVar("%i1")], [])
        inner_if = SCFIf([], SSAVar("%cond"), [], [read], None)
        pod_to_member = {}
        _annotate_array_component_reads([const, cast, inner_if], {"%array": "last"}, {}, pod_to_member)
        assert pod_to_member["%9"] == "last#1"

    def test_sibling_branches_do_not_leak_constants(self):
        # Two sibling scf.if branches both fold "%idx" to *different*
        # values — a flat/shared dict would let one leak into the other.
        const_a = FeltConst(SSAVar("%idx"), 0)
        read_a = ArrayRead(SSAVar("%ra"), SSAVar("%array"), [SSAVar("%idx")], [])
        branch_a = SCFIf([], SSAVar("%ca"), [], [const_a, read_a], None)

        const_b = FeltConst(SSAVar("%idx"), 1)
        read_b = ArrayRead(SSAVar("%rb"), SSAVar("%array"), [SSAVar("%idx")], [])
        branch_b = SCFIf([], SSAVar("%cb"), [], [const_b, read_b], None)

        pod_to_member = {}
        _annotate_array_component_reads([branch_a, branch_b], {"%array": "last"}, {}, pod_to_member)
        assert pod_to_member["%ra"] == "last#0"
        assert pod_to_member["%rb"] == "last#1"

    def test_unregistered_array_ignored(self):
        read = ArrayRead(SSAVar("%r"), SSAVar("%other_array"), [SSAVar("%i")], [])
        pod_to_member = {}
        _annotate_array_component_reads([read], {"%array": "last"}, {}, pod_to_member)
        assert "%r" not in pod_to_member

    def test_2d_all_constant_indices_gets_double_subindex_name(self):
        const_j = FeltConst(SSAVar("%cj"), 1)
        cast_j = CastToIndex(SSAVar("%j0"), SSAVar("%cj"))
        const_i = FeltConst(SSAVar("%ci"), 2)
        cast_i = CastToIndex(SSAVar("%i0"), SSAVar("%ci"))
        read = ArrayRead(SSAVar("%8"), SSAVar("%array"), [SSAVar("%j0"), SSAVar("%i0")], [])
        pod_to_member = {}
        _annotate_array_component_reads(
            [const_j, cast_j, const_i, cast_i, read], {"%array": "sigmaF"}, {}, pod_to_member)
        assert pod_to_member["%8"] == "sigmaF#1#2"

    def test_2d_one_non_constant_index_falls_back_to_bare_name(self):
        # Only the outer index is a compile-time constant -- a partially
        # resolved index still isn't enough to name one specific instance.
        const_j = FeltConst(SSAVar("%cj"), 1)
        cast_j = CastToIndex(SSAVar("%j0"), SSAVar("%cj"))
        read = ArrayRead(SSAVar("%8"), SSAVar("%array"), [SSAVar("%j0"), SSAVar("%arg_i")], [])
        pod_to_member = {}
        _annotate_array_component_reads(
            [const_j, cast_j, read], {"%array": "sigmaF"}, {}, pod_to_member)
        assert pod_to_member["%8"] == "sigmaF"


# ── _build_component_naming_maps — array-of-components integration ────────────

class TestBuildComponentNamingMapsArrays:
    """
    End-to-end (within the pre-pass): a read of the counting-pod array is
    named like a scalar subcomponent slot ("last#0"/"last#1") when its index
    is a compile-time constant, and the FunctionCall stored into that slot's
    @comp field is annotated with that same name — mirroring the fix for
    three_subcomponents_array_concrete.mlir, where component instances used
    to lose their name entirely (falling back to raw SSA names) once they
    were held in an array instead of one variable per instance.

    A read indexed by a genuine runtime loop variable (as in
    ternary_concrete.mlir's scf.while-based Num2Bits_16_325 array) instead
    gets the bare member name, for the caller to reconstruct per-iteration
    names externally.
    """

    def _index_at(self, value, ssa_const, ssa_idx):
        const = FeltConst(SSAVar(ssa_const), value)
        cast = CastToIndex(SSAVar(ssa_idx), SSAVar(ssa_const))
        return [const, cast]

    def _bulk_copy_and_writem(self, counting_arr="%array", member="@last"):
        read = ArrayRead(SSAVar("%elem"), SSAVar(counting_arr), [SSAVar("%iv")], [])
        comp = PodRead(SSAVar("%comp"), SSAVar("%elem"), GlobalVariable("@comp"), {}, None)
        write = ArrayWrite(SSAVar("%array_13"), [SSAVar("%iv")], SSAVar("%comp"), [])
        loop = SCFFor([], SSAVar("%iv"), SSAVar("%lb"), SSAVar("%ub"), SSAVar("%step"), [], [read, comp, write])
        writem = StructWritem(SSAVar("%self"), GlobalVariable(member), SSAVar("%array_13"),
                              [Type("!array.type<2 x !struct.type<@X>>")])
        return loop, writem

    def test_array_slots_named_like_scalar_subcomponents(self):
        ctx = TranslationContext()
        loop, writem = self._bulk_copy_and_writem()

        # Two constant-indexed top-level reads of the counting array (as an
        # unrolled compute would emit for each concrete instance), each
        # followed by a nested scf.if computing that instance's subcomponent.
        idx0 = self._index_at(0, "%c0", "%i0")
        top_read_0 = ArrayRead(SSAVar("%8"), SSAVar("%array"), [SSAVar("%i0")], [])
        call_0 = FunctionCall([SSAVar("%26")], GlobalVariable("@Sub"), [], None)
        write_comp_0 = PodWrite(SSAVar("%8"), GlobalVariable("@comp"), SSAVar("%26"), {}, None)
        if_0 = SCFIf([], SSAVar("%cond0"), [], [call_0, write_comp_0], None)

        idx1 = self._index_at(1, "%c1", "%i1")
        top_read_1 = ArrayRead(SSAVar("%18"), SSAVar("%array"), [SSAVar("%i1")], [])
        call_1 = FunctionCall([SSAVar("%26")], GlobalVariable("@Sub"), [], None)  # same SSA name, distinct object
        write_comp_1 = PodWrite(SSAVar("%18"), GlobalVariable("@comp"), SSAVar("%26"), {}, None)
        if_1 = SCFIf([], SSAVar("%cond1"), [], [call_1, write_comp_1], None)

        body = [
            loop, writem,
            *idx0, top_read_0, if_0,
            *idx1, top_read_1, if_1,
        ]

        _build_component_naming_maps(body, ctx)

        assert call_0._member_hint == "last#0"
        assert call_1._member_hint == "last#1"

    def test_symbolic_loop_index_uses_bare_name(self):
        # Mirrors ternary_concrete.mlir's Num2Bits_16_325: subcomponents are
        # instantiated inside a real (scf.while-style) runtime loop, so the
        # counting-array read's index is never a compile-time constant —
        # there's no single instance to name more specifically at
        # translation time, so every call inside the loop shares the bare
        # member name.
        ctx = TranslationContext()
        loop, writem = self._bulk_copy_and_writem(member="@Num2Bits_16_325")

        top_read = ArrayRead(SSAVar("%15"), SSAVar("%array"), [SSAVar("%arg4")], [])
        call = FunctionCall([SSAVar("%30")], GlobalVariable("@Sub"), [], None)
        write_comp = PodWrite(SSAVar("%15"), GlobalVariable("@comp"), SSAVar("%30"), {}, None)
        loop_body_if = SCFIf([], SSAVar("%cond"), [], [call, write_comp], None)
        # The whole thing sits inside the runtime loop itself (unlike the
        # constant-index case, which reads at the top level).
        runtime_loop = SCFFor([], SSAVar("%arg4"), SSAVar("%lb2"), SSAVar("%ub2"), SSAVar("%step2"),
                              [], [top_read, loop_body_if])

        body = [loop, writem, runtime_loop]

        _build_component_naming_maps(body, ctx)

        assert call._member_hint == "Num2Bits_16_325"


# ── _build_component_naming_maps — N-D array-of-components integration ────────

class TestBuildComponentNamingMapsArraysND:
    """
    N-D generalization of the homogeneous array-of-components mechanism --
    both the .out side (Part 2b, counting-pod bulk copy nested scf.for
    loops) and the .in side (Part 1, $inputs array) -- mirroring
    poseidon3_test_concrete.mlir's real 2-D "@sigmaF" member
    (!array.type<8,3 x !struct.type<@Sigma_1::...>>).
    """

    def test_2d_out_side_end_to_end(self):
        ctx = TranslationContext()

        read = ArrayRead(SSAVar("%elem"), SSAVar("%array"), [SSAVar("%j"), SSAVar("%i")], [])
        comp = PodRead(SSAVar("%comp"), SSAVar("%elem"), GlobalVariable("@comp"), {}, None)
        write = ArrayWrite(SSAVar("%array_13"), [SSAVar("%j"), SSAVar("%i")], SSAVar("%comp"), [])
        inner_loop = SCFFor([], SSAVar("%i"), SSAVar("%lb_i"), SSAVar("%ub_i"), SSAVar("%step_i"),
                            [], [read, comp, write])
        outer_loop = SCFFor([], SSAVar("%j"), SSAVar("%lb_j"), SSAVar("%ub_j"), SSAVar("%step_j"),
                            [], [inner_loop])
        writem = StructWritem(SSAVar("%self"), GlobalVariable("@sigmaF"), SSAVar("%array_13"),
                              [Type("!array.type<8,3 x !struct.type<@X>>")])

        # Constant-indexed top-level read of the counting array (j=0, i=2).
        cj = FeltConst(SSAVar("%cj"), 0)
        castj = CastToIndex(SSAVar("%j0"), SSAVar("%cj"))
        ci = FeltConst(SSAVar("%ci"), 2)
        casti = CastToIndex(SSAVar("%i0"), SSAVar("%ci"))
        top_read = ArrayRead(SSAVar("%8"), SSAVar("%array"), [SSAVar("%j0"), SSAVar("%i0")], [])
        call = FunctionCall([SSAVar("%26")], GlobalVariable("@Sigma_1"), [], None)
        write_comp = PodWrite(SSAVar("%8"), GlobalVariable("@comp"), SSAVar("%26"), {}, None)

        body = [outer_loop, writem, cj, castj, ci, casti, top_read, call, write_comp]
        _build_component_naming_maps(body, ctx)

        assert call._member_hint == "sigmaF#0#2"

    def test_2d_in_side_end_to_end(self):
        ctx = TranslationContext()

        pod_array = SSAVar("%pod_array")
        writem = StructWritem(SSAVar("%self"), GlobalVariable("@sigmaF_inputs"), pod_array,
                              [Type("!array.type<8,3 x !pod.type<[@in: !felt.type]>>")])

        cj = FeltConst(SSAVar("%cj"), 0)
        castj = CastToIndex(SSAVar("%j0"), SSAVar("%cj"))
        ci = FeltConst(SSAVar("%ci"), 2)
        casti = CastToIndex(SSAVar("%i0"), SSAVar("%ci"))
        read = ArrayRead(SSAVar("%9"), pod_array, [SSAVar("%j0"), SSAVar("%i0")], [])

        body = [writem, cj, castj, ci, casti, read]
        _build_component_naming_maps(body, ctx)

        assert read._semantic_base == "sigmaF#0#2"


# ── _is_idx_pod_component_member / _pod_fields_match ───────────────────────────

class TestIsIdxPodComponentMember:
    """
    A heterogeneous array-of-components member: every field a literal
    @idx_N record, AND every field's own type !struct.type (distinguishing
    it from the member's "$inputs" companion pod, whose @idx_N fields are
    themselves !pod.type) -- see poseidon3_test_concrete.mlir's "@ark".
    """

    def test_struct_typed_idx_fields_matches(self):
        type_str = ("!pod.type<[@idx_0: !struct.type<@Ark_0::@Ark_0<[]>>, "
                    "@idx_1: !struct.type<@Ark_2::@Ark_2<[]>>]>")
        fields = _is_idx_pod_component_member(type_str)
        assert fields is not None
        assert set(fields.keys()) == {"@idx_0", "@idx_1"}

    def test_pod_typed_idx_fields_is_inputs_shape_not_matched(self):
        # The "$inputs" companion shape (e.g. "@ark_inputs"): @idx_N fields
        # are !pod.type, not !struct.type -- must not be mistaken for the
        # component-holding member itself.
        type_str = "!pod.type<[@idx_0: !pod.type<[@in: !felt.type]>]>"
        assert _is_idx_pod_component_member(type_str) is None

    def test_non_idx_pod_not_matched(self):
        type_str = "!pod.type<[@count: index, @comp: !struct.type<@S::@S<[]>>]>"
        assert _is_idx_pod_component_member(type_str) is None

    def test_plain_struct_type_not_matched(self):
        assert _is_idx_pod_component_member("!struct.type<@Foo::@Foo<[]>>") is None


class TestIdxReadMatchesMember:
    """
    _idx_read_matches_member: matches a pod.read[@idx_N]'s own declared
    RESULT type against @idx_N's struct type as declared on the struct
    member -- either directly, or (the shape real LLZK output actually
    uses) through a "counting pod" (@count/@comp/@params) wrapper's own
    @comp field.
    """

    ARK_0 = Type("!struct.type<@Ark_0::@Ark_0<[]>>")

    def test_direct_struct_type_match(self):
        assert _idx_read_matches_member(self.ARK_0, self.ARK_0) is True

    def test_counting_pod_wrapper_comp_field_matches(self):
        wrapped = Type(
            "!pod.type<[@count: index, @comp: !struct.type<@Ark_0::@Ark_0<[]>>, "
            "@params: !pod.type<[]>]>"
        )
        assert _idx_read_matches_member(wrapped, self.ARK_0) is True

    def test_counting_pod_wrapper_different_comp_type_no_match(self):
        wrapped = Type(
            "!pod.type<[@count: index, @comp: !struct.type<@Ark_2::@Ark_2<[]>>, "
            "@params: !pod.type<[]>]>"
        )
        assert _idx_read_matches_member(wrapped, self.ARK_0) is False

    def test_unrelated_pod_type_no_match(self):
        other = Type("!pod.type<[@in: !felt.type]>")
        assert _idx_read_matches_member(other, self.ARK_0) is False

    def test_none_result_type_no_match(self):
        assert _idx_read_matches_member(None, self.ARK_0) is False


# ── _annotate_idx_pod_component_reads ───────────────────────────────────────────

def _counting_pod_type(struct_type_str: str) -> Type:
    """
    The real shape a heterogeneous slot's counting-pod holder is read as in
    actual LLZK output: pod.read %holder[@idx_N] : ...,
    !pod.type<[@count: index, @comp: !struct.type<...>, @params: !pod.type<[]>]>
    -- see _idx_read_matches_member.
    """
    return Type(f"!pod.type<[@count: index, @comp: {struct_type_str}, "
               f"@params: !pod.type<[]>]>")


class TestAnnotateIdxPodComponentReads:

    ARK_FIELDS = {
        "@idx_0": Type("!struct.type<@Ark_0::@Ark_0<[]>>"),
        "@idx_1": Type("!struct.type<@Ark_2::@Ark_2<[]>>"),
    }

    def test_matching_read_registered_as_member_hash_idx(self):
        read = PodRead(SSAVar("%577"), SSAVar("%holder"), GlobalVariable("@idx_0"),
                       {}, _counting_pod_type("!struct.type<@Ark_0::@Ark_0<[]>>"))
        pod_to_member = {}
        _annotate_idx_pod_component_reads([read], {"ark": self.ARK_FIELDS}, pod_to_member)
        assert pod_to_member["%577"] == "ark#0"

    def test_second_idx_uses_its_own_number(self):
        read = PodRead(SSAVar("%578"), SSAVar("%holder"), GlobalVariable("@idx_1"),
                       {}, _counting_pod_type("!struct.type<@Ark_2::@Ark_2<[]>>"))
        pod_to_member = {}
        _annotate_idx_pod_component_reads([read], {"ark": self.ARK_FIELDS}, pod_to_member)
        assert pod_to_member["%578"] == "ark#1"

    def test_direct_struct_result_type_also_matches(self):
        # The un-wrapped shape (a bare struct value, no counting-pod
        # wrapper) is also accepted -- see _idx_read_matches_member.
        read = PodRead(SSAVar("%577"), SSAVar("%holder"), GlobalVariable("@idx_0"),
                       {}, Type("!struct.type<@Ark_0::@Ark_0<[]>>"))
        pod_to_member = {}
        _annotate_idx_pod_component_reads([read], {"ark": self.ARK_FIELDS}, pod_to_member)
        assert pod_to_member["%577"] == "ark#0"

    def test_recurses_into_nested_bodies(self):
        # Mirrors the real file's runtime-index scf.if dispatch ladder: the
        # matching pod.read sits inside a nested scf.if branch, not at the
        # top level.
        read = PodRead(SSAVar("%577"), SSAVar("%holder"), GlobalVariable("@idx_0"),
                       {}, _counting_pod_type("!struct.type<@Ark_0::@Ark_0<[]>>"))
        branch = SCFIf([], SSAVar("%cond"), [], [read], None)
        pod_to_member = {}
        _annotate_idx_pod_component_reads([branch], {"ark": self.ARK_FIELDS}, pod_to_member)
        assert pod_to_member["%577"] == "ark#0"

    def test_non_idx_record_ignored(self):
        read = PodRead(SSAVar("%1"), SSAVar("%holder"), GlobalVariable("@comp"),
                       {}, _counting_pod_type("!struct.type<@Ark_0::@Ark_0<[]>>"))
        pod_to_member = {}
        _annotate_idx_pod_component_reads([read], {"ark": self.ARK_FIELDS}, pod_to_member)
        assert pod_to_member == {}

    def test_mismatched_comp_struct_type_ignored(self):
        # Same @idx_0 record name, but the read's own counting-pod @comp
        # type doesn't match "ark"'s @idx_0 declared struct type -- must
        # not be misattributed.
        read = PodRead(SSAVar("%1"), SSAVar("%holder"), GlobalVariable("@idx_0"),
                       {}, _counting_pod_type("!struct.type<@Other_0::@Other_0<[]>>"))
        pod_to_member = {}
        _annotate_idx_pod_component_reads([read], {"ark": self.ARK_FIELDS}, pod_to_member)
        assert pod_to_member == {}


# ── _build_component_naming_maps — heterogeneous (idx-pod) integration ────────

class TestBuildComponentNamingMapsIdxPods:
    """
    Heterogeneous array-of-components member (poseidon3_test_concrete.mlir's
    "@ark": each index instantiates a *different* template, e.g. Ark_0 at
    idx_0, Ark_2 at idx_1 -- so LLZK lowers it to a pod with one @idx_N
    field per index instead of a real !array.type). Unlike the homogeneous
    array case (TestBuildComponentNamingMapsArrays), the index is always a
    compile-time-literal pod field name, so every occurrence -- no matter
    which control-flow shape it sits inside -- is named "{member}#{idx}"
    unconditionally, with no compile-time-constant-vs-runtime-loop
    distinction to make.
    """

    ARK_FIELDS = {
        "@idx_0": Type("!struct.type<@Ark_0::@Ark_0<[]>>"),
        "@idx_1": Type("!struct.type<@Ark_2::@Ark_2<[]>>"),
    }

    def test_idx_pod_reads_named_and_calls_annotated(self):
        ctx = TranslationContext()

        read_0 = PodRead(SSAVar("%577"), SSAVar("%holder"), GlobalVariable("@idx_0"),
                         {}, _counting_pod_type("!struct.type<@Ark_0::@Ark_0<[]>>"))
        call_0 = FunctionCall([SSAVar("%584")], GlobalVariable("@Ark_0"), [], None)
        write_0 = PodWrite(SSAVar("%577"), GlobalVariable("@comp"), SSAVar("%584"), {}, None)

        # idx_1's occurrence sits inside a nested scf.if, mirroring the real
        # file's per-idx runtime dispatch branches -- confirms the
        # recursive walk reaches it regardless of nesting depth.
        read_1 = PodRead(SSAVar("%578"), SSAVar("%holder"), GlobalVariable("@idx_1"),
                         {}, _counting_pod_type("!struct.type<@Ark_2::@Ark_2<[]>>"))
        call_1 = FunctionCall([SSAVar("%585")], GlobalVariable("@Ark_2"), [], None)
        write_1 = PodWrite(SSAVar("%578"), GlobalVariable("@comp"), SSAVar("%585"), {}, None)
        branch_1 = SCFIf([], SSAVar("%cond1"), [], [read_1, call_1, write_1], None)

        body = [read_0, call_0, write_0, branch_1]

        _build_component_naming_maps(body, ctx, {"ark": self.ARK_FIELDS})

        assert call_0._member_hint == "ark#0"
        assert call_1._member_hint == "ark#1"

    def test_unrelated_pod_type_not_misattributed(self):
        # A pod.read[@idx_N] whose counting-pod @comp type doesn't match
        # any registered idx-pod member's declared struct type must not be
        # attributed to it.
        ctx = TranslationContext()
        read = PodRead(SSAVar("%1"), SSAVar("%holder"), GlobalVariable("@idx_0"),
                       {}, _counting_pod_type("!struct.type<@Other_0::@Other_0<[]>>"))
        call = FunctionCall([SSAVar("%2")], GlobalVariable("@Other_0"), [], None)
        write = PodWrite(SSAVar("%1"), GlobalVariable("@comp"), SSAVar("%2"), {}, None)

        body = [read, call, write]
        _build_component_naming_maps(body, ctx, {"ark": self.ARK_FIELDS})

        assert call._member_hint is None

    def test_no_idx_pod_members_argument_is_backward_compatible(self):
        # idx_pod_member_types omitted (defaults to None) must leave the
        # existing (array/scalar) call signature and behavior unaffected.
        ctx = TranslationContext()
        _build_component_naming_maps([], ctx)  # must not raise


# ── _build_component_naming_maps — 2-D heterogeneous (idx-pod) integration ────

class TestBuildComponentNamingMapsIdxPods2D:
    """
    2-D heterogeneous array-of-components member (mirrors
    multidimensional_components_concrete.mlir's "@components": a 2x2
    collection where each slot instantiates a different Num2Ternary
    template, so LLZK lowers it to a pod with one @idx_{i}_{j} field per
    index instead of a real !array.type). Confirms the N-D generalization
    threads all the way through: _idx_pod_child_name builds the
    "#i#j"-joined name, and _annotate_idx_pod_component_reads /
    _annotate_function_calls need no changes to consume it.
    """

    COMPONENTS_FIELDS = {
        "@idx_0_0": Type("!struct.type<@Num2Ternary_0::@Num2Ternary_0<[]>>"),
        "@idx_0_1": Type("!struct.type<@Num2Ternary_1::@Num2Ternary_1<[]>>"),
        "@idx_1_0": Type("!struct.type<@Num2Ternary_0::@Num2Ternary_0<[]>>"),
        "@idx_1_1": Type("!struct.type<@Num2Ternary_1::@Num2Ternary_1<[]>>"),
    }

    def test_2d_idx_pod_reads_named_and_calls_annotated(self):
        ctx = TranslationContext()

        read_00 = PodRead(SSAVar("%77"), SSAVar("%holder"), GlobalVariable("@idx_0_0"),
                          {}, _counting_pod_type("!struct.type<@Num2Ternary_0::@Num2Ternary_0<[]>>"))
        call_00 = FunctionCall([SSAVar("%84")], GlobalVariable("@Num2Ternary_0"), [], None)
        write_00 = PodWrite(SSAVar("%77"), GlobalVariable("@comp"), SSAVar("%84"), {}, None)

        read_11 = PodRead(SSAVar("%78"), SSAVar("%holder"), GlobalVariable("@idx_1_1"),
                          {}, _counting_pod_type("!struct.type<@Num2Ternary_1::@Num2Ternary_1<[]>>"))
        call_11 = FunctionCall([SSAVar("%85")], GlobalVariable("@Num2Ternary_1"), [], None)
        write_11 = PodWrite(SSAVar("%78"), GlobalVariable("@comp"), SSAVar("%85"), {}, None)
        # idx_1_1's occurrence sits inside a nested scf.if, mirroring the
        # real file's runtime dispatch ladder testing both indices.
        branch_11 = SCFIf([], SSAVar("%cond"), [], [read_11, call_11, write_11], None)

        body = [read_00, call_00, write_00, branch_11]

        _build_component_naming_maps(body, ctx, {"components": self.COMPONENTS_FIELDS})

        assert call_00._member_hint == "components#0#0"
        assert call_11._member_hint == "components#1#1"


# ── _build_component_naming_maps — $inputs array through nested scf.while ─────

class TestBuildComponentNamingMapsNestedWhileInputs:
    """
    A $inputs array threaded through TWO nested scf.while loops (mirrors
    poseidon3_test_concrete.mlir's "@mixLast$inputs": an outer scf.while
    carries the array as %arg2, whose after_body contains a second, inner
    scf.while re-carrying it as %arg4) must get BOTH loops' own block-arg
    names aliased to the same member base -- not just the outermost one,
    which is all the previous (non-recursive) while_iter_args collection
    covered.
    """

    ARR_TYPE = Type("!array.type<1 x !pod.type<[@in: !felt.type]>>")

    def test_inner_while_block_arg_aliased_and_read_named(self):
        ctx = TranslationContext()

        # Inner while: (%arg4 = %arg2) -- re-carries the same $inputs array
        # one level deeper. Its body reads element 0 (a compile-time
        # constant index) via its OWN block-arg name, %arg4.
        const0 = FeltConst(SSAVar("%c0"), 0)
        idx0 = CastToIndex(SSAVar("%i0"), SSAVar("%c0"))
        read = ArrayRead(SSAVar("%588"), SSAVar("%arg4"), [SSAVar("%i0")], [])
        inner_while = SCFWhile(
            [SSAVar("%567", n_components=1)],
            [(SSAVar("%arg4"), SSAVar("%arg2"))],
            [[self.ARR_TYPE], [self.ARR_TYPE]],
            [], [], [const0, idx0, read],
        )

        # Outer while: (%arg2 = %array_117) -- the top-level alias that
        # already worked before this fix; its after_body contains the
        # inner while nested one level deeper.
        outer_while = SCFWhile(
            [SSAVar("%422", n_components=1)],
            [(SSAVar("%arg2"), SSAVar("%array_117"))],
            [[self.ARR_TYPE], [self.ARR_TYPE]],
            [], [], [inner_while],
        )

        writem = StructWritem(
            SSAVar("%self"), GlobalVariable("@mixLast_inputs"), SSAVar("%422"),
            [self.ARR_TYPE],
        )

        body = [outer_while, writem]
        _build_component_naming_maps(body, ctx)

        assert ctx.input_pod_to_member["%arg2"] == "mixLast"
        assert ctx.input_pod_to_member["%arg4"] == "mixLast"
        assert read._semantic_base == "mixLast#0"


# ── _is_population_write ────────────────────────────────────────────────────

class TestIsPopulationWrite:
    """
    _is_population_write: a real read-modify-write population write (its
    value traces back to an ArrayRead of the SAME array) vs. e.g. the
    array's own initial-fill loop (a fresh pod.new written into every slot,
    never read from first).
    """

    def test_read_modify_write_is_population(self):
        read = ArrayRead(SSAVar("%14"), SSAVar("%array"), [SSAVar("%i"), SSAVar("%j")], [])
        write = ArrayWrite(SSAVar("%array"), [SSAVar("%i"), SSAVar("%j")], SSAVar("%14"), [])
        def_map = {"%14": read}
        assert _is_population_write(write, def_map) is True

    def test_fresh_value_is_not_population(self):
        fresh = PodNew(SSAVar("%pod_8"), {}, {})
        write = ArrayWrite(SSAVar("%array"), [SSAVar("%i"), SSAVar("%j")], SSAVar("%pod_8"), [])
        def_map = {"%pod_8": fresh}
        assert _is_population_write(write, def_map) is False

    def test_read_of_different_array_is_not_population(self):
        read = ArrayRead(SSAVar("%14"), SSAVar("%other_array"), [SSAVar("%i"), SSAVar("%j")], [])
        write = ArrayWrite(SSAVar("%array"), [SSAVar("%i"), SSAVar("%j")], SSAVar("%14"), [])
        def_map = {"%14": read}
        assert _is_population_write(write, def_map) is False

    def test_unknown_source_is_not_population(self):
        write = ArrayWrite(SSAVar("%array"), [SSAVar("%i"), SSAVar("%j")], SSAVar("%unknown"), [])
        assert _is_population_write(write, {}) is False


# ── _trace_to_enclosing_loop ────────────────────────────────────────────────

class TestTraceToEnclosingLoop:
    """
    Resolves an index name back through cast.toindex/cast.tofelt to
    whichever loop_stack member it equals -- by SSA identity, never
    positionally (an array's own dimension order need not match its
    population loop's own nesting order).
    """

    def _for_loop(self, iv):
        return SCFFor([], SSAVar(iv), SSAVar("%lb"), SSAVar("%ub"), SSAVar("%step"), [], [])

    def test_direct_match_scf_for(self):
        loop = self._for_loop("%iv")
        assert _trace_to_enclosing_loop("%iv", [loop], {}) is loop

    def test_match_through_cast(self):
        loop = self._for_loop("%iv")
        cast = CastToIndex(SSAVar("%7"), SSAVar("%iv"))
        def_map = {"%7": cast}
        assert _trace_to_enclosing_loop("%7", [loop], def_map) is loop

    def test_scf_while_matches_its_own_after_arg(self):
        while_op = SCFWhile([], [(SSAVar("%arg2"), SSAVar("%init"))], [[Type("index")]],
                            [], [(SSAVar("%arg2"), Type("index"))], [])
        assert _trace_to_enclosing_loop("%arg2", [while_op], {}) is while_op

    def test_not_positional_inner_loop_drives_outer_dimension(self):
        # Mirrors arbitrary_traversal_array_components.circom exactly:
        # "components[i][j]" (array dim 0 = i, dim 1 = j) with i driven by
        # the INNER loop and j by the OUTER one -- resolution must find the
        # correct loop regardless of where it sits in loop_stack, never by
        # position.
        outer = self._for_loop("%j")   # loop_stack[0], drives array dim 1
        inner = self._for_loop("%i")   # loop_stack[1], drives array dim 0
        assert _trace_to_enclosing_loop("%i", [outer, inner], {}) is inner
        assert _trace_to_enclosing_loop("%j", [outer, inner], {}) is outer

    def test_unresolvable_returns_none(self):
        loop = self._for_loop("%iv")
        assert _trace_to_enclosing_loop("%unrelated", [loop], {}) is None


# ── _loop_own_sequence ──────────────────────────────────────────────────────

class TestLoopOwnSequence:

    def test_scf_for_range(self):
        loop = SCFFor([], SSAVar("%iv"), SSAVar("%lb"), SSAVar("%ub"), SSAVar("%step"), [], [])
        const_map = {"%lb": 0, "%ub": 6, "%step": 2}
        assert _loop_own_sequence(loop, const_map) == [0, 2, 4]

    def test_scf_for_default_step_one(self):
        loop = SCFFor([], SSAVar("%iv"), SSAVar("%lb"), SSAVar("%ub"), SSAVar("%step"), [], [])
        const_map = {"%lb": 0, "%ub": 3}
        assert _loop_own_sequence(loop, const_map) == [0, 1, 2]

    def test_scf_for_unresolvable_bound_returns_none(self):
        loop = SCFFor([], SSAVar("%iv"), SSAVar("%lb"), SSAVar("%ub"), SSAVar("%step"), [], [])
        assert _loop_own_sequence(loop, {"%lb": 0}) is None

    def _while_loop(self, bound_name="%c3", bound_op=None):
        after_body = [
            FeltConst(SSAVar("%c1"), 1),
            FeltBinary(SSAVar("%next"), "felt.add", SSAVar("%arg1"), SSAVar("%c1"), []),
            SCFYield([SSAVar("%next")], [Type("index")]),
        ]
        before_ops = []
        if bound_op is not None:
            before_ops.append(bound_op)
        before_ops += [
            BoolCmp(SSAVar("%cond"), "lt", SSAVar("%arg1"), SSAVar(bound_name)),
            SCFCondition(SSAVar("%cond"), [SSAVar("%arg1")], [Type("index")]),
        ]
        return SCFWhile(
            [], [(SSAVar("%arg1"), SSAVar("%c0"))], [[Type("index")], [Type("index")]],
            before_ops, [(SSAVar("%arg1"), Type("index"))], after_body,
        )

    def test_scf_while_sequence(self):
        loop = self._while_loop(bound_op=FeltConst(SSAVar("%c3"), 3))
        assert _loop_own_sequence(loop, {"%c0": 0}) == [0, 1, 2]

    def test_scf_while_unresolvable_returns_none(self):
        loop = self._while_loop(bound_name="%bound")
        assert _loop_own_sequence(loop, {"%c0": 0}) is None

    def test_not_a_loop_returns_none(self):
        assert _loop_own_sequence(object(), {}) is None


# ── _resolve_population_nest_sequence ───────────────────────────────────────

class TestResolvePopulationNestSequence:
    """
    Combines the implicated loops' own sequences into one nest's list of
    index tuples, in ARRAY DIMENSION order (matching the write's own index
    order) -- which is not necessarily the same as loop_stack's own
    (outer-to-inner) nesting order.
    """

    def test_positional_2d_outer_slow_inner_fast(self):
        # Nesting order matches dimension order here (the common/simple
        # case): outer loop = dim 0, inner loop = dim 1.
        outer = SCFFor([], SSAVar("%j"), SSAVar("%lb_j"), SSAVar("%ub_j"), SSAVar("%step_j"), [], [])
        inner = SCFFor([], SSAVar("%i"), SSAVar("%lb_i"), SSAVar("%ub_i"), SSAVar("%step_i"), [], [])
        write = ArrayWrite(SSAVar("%array"), [SSAVar("%j"), SSAVar("%i")], SSAVar("%14"), [])
        const_map = {"%lb_j": 0, "%ub_j": 2, "%step_j": 1, "%lb_i": 0, "%ub_i": 3, "%step_i": 1}
        result = _resolve_population_nest_sequence(write, [outer, inner], {}, const_map)
        assert result == [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)]

    def test_non_positional_dimension_order_differs_from_nesting(self):
        # Mirrors arbitrary_traversal_array_components.circom: "components[i][j]"
        # (array dim 0 = i, dim 1 = j), with i (inner loop) fast-varying and
        # j (outer loop) slow-varying -- the write's own index list is
        # [i-derived, j-derived], the OPPOSITE of loop_stack's nesting order.
        outer_j = SCFFor([], SSAVar("%j"), SSAVar("%lb_j"), SSAVar("%ub_j"), SSAVar("%step_j"), [], [])
        inner_i = SCFFor([], SSAVar("%i"), SSAVar("%lb_i"), SSAVar("%ub_i"), SSAVar("%step_i"), [], [])
        cast_i = CastToIndex(SSAVar("%7"), SSAVar("%i"))
        cast_j = CastToIndex(SSAVar("%8"), SSAVar("%j"))
        write = ArrayWrite(SSAVar("%array"), [SSAVar("%7"), SSAVar("%8")], SSAVar("%14"), [])
        def_map = {"%7": cast_i, "%8": cast_j}
        const_map = {"%lb_j": 0, "%ub_j": 4, "%step_j": 2, "%lb_i": 0, "%ub_i": 6, "%step_i": 2}
        result = _resolve_population_nest_sequence(write, [outer_j, inner_i], def_map, const_map)
        # j (outer) varies slowest: j=0 -> i=0,2,4; j=2 -> i=0,2,4. Each
        # tuple is (i, j) -- ARRAY dimension order, not nesting order.
        assert result == [(0, 0), (2, 0), (4, 0), (0, 2), (2, 2), (4, 2)]

    def test_unrelated_enclosing_loop_ignored(self):
        # An enclosing loop that doesn't drive any of this write's indices
        # doesn't need to be resolvable at all.
        unrelated = SCFFor([], SSAVar("%k"), SSAVar("%lb_k"), SSAVar("%ub_k"), SSAVar("%step_k"), [], [])
        only = SCFFor([], SSAVar("%i"), SSAVar("%lb_i"), SSAVar("%ub_i"), SSAVar("%step_i"), [], [])
        write = ArrayWrite(SSAVar("%array"), [SSAVar("%i")], SSAVar("%14"), [])
        const_map = {"%lb_i": 0, "%ub_i": 2, "%step_i": 1}  # no %lb_k etc. at all
        result = _resolve_population_nest_sequence(write, [unrelated, only], {}, const_map)
        assert result == [(0,), (1,)]

    def test_unresolvable_index_returns_none(self):
        loop = SCFFor([], SSAVar("%i"), SSAVar("%lb"), SSAVar("%ub"), SSAVar("%step"), [], [])
        write = ArrayWrite(SSAVar("%array"), [SSAVar("%unrelated")], SSAVar("%14"), [])
        assert _resolve_population_nest_sequence(write, [loop], {}, {"%lb": 0, "%ub": 2}) is None

    def test_unresolvable_loop_sequence_returns_none(self):
        loop = SCFFor([], SSAVar("%i"), SSAVar("%lb"), SSAVar("%ub"), SSAVar("%step"), [], [])
        write = ArrayWrite(SSAVar("%array"), [SSAVar("%i")], SSAVar("%14"), [])
        assert _resolve_population_nest_sequence(write, [loop], {}, {}) is None


# ── _collect_population_write_candidates ────────────────────────────────────

class TestCollectPopulationWriteCandidates:
    """
    More than one structurally-valid population write can exist in the same
    scope -- LLZK re-checks "ready to call yet?" once per input-signal
    assignment for a multi-input component, each with its own full
    call+array-write scaffolding, but only the textually LAST one is ever
    satisfied at runtime (confirmed via
    arbitrary_traversal_array_components_concrete.mlir's 2-input IsZero).
    """

    def _population_write(self, ssa="%14"):
        read = ArrayRead(SSAVar(ssa), SSAVar("%array"), [SSAVar("%i")], [])
        write = ArrayWrite(SSAVar("%array"), [SSAVar("%i")], SSAVar(ssa), [])
        return read, write

    def test_single_candidate_found(self):
        read, write = self._population_write()
        branch = SCFIf([], SSAVar("%cond"), [], [read, write], None)
        out = []
        _collect_population_write_candidates([branch], {"%array": "comp"}, {}, {}, out)
        assert len(out) == 1
        assert out[0][0] is write

    def test_multiple_sibling_candidates_all_collected_in_order(self):
        # Mirrors the real shape: two SIBLING scf.if blocks (one per input
        # signal checkpoint) at the same body level, each independently
        # writing to the same registered array.
        read1, write1 = self._population_write(ssa="%14")
        branch1 = SCFIf([], SSAVar("%cond1"), [], [read1, write1], None)
        read2, write2 = self._population_write(ssa="%32")
        branch2 = SCFIf([], SSAVar("%cond2"), [], [read2, write2], None)

        out = []
        _collect_population_write_candidates([branch1, branch2], {"%array": "comp"}, {}, {}, out)
        assert [c[0] for c in out] == [write1, write2]

    def test_does_not_cross_into_nested_loop(self):
        # A write inside a FURTHER nested scf.for is a different dimension's
        # own population site, not this scope's -- must not be collected
        # here (the caller handles it via its own separate recursion).
        read, write = self._population_write()
        nested_for = SCFFor([], SSAVar("%k"), SSAVar("%lb"), SSAVar("%ub"), SSAVar("%step"),
                            [], [read, write])
        out = []
        _collect_population_write_candidates([nested_for], {"%array": "comp"}, {}, {}, out)
        assert out == []

    def test_non_population_write_not_collected(self):
        # A write whose value is a fresh pod.new (not read-modify-write) --
        # e.g. the array's own init-fill loop -- is filtered out by
        # _is_population_write, same as at the top level.
        fresh = PodNew(SSAVar("%pod_8"), {}, {})
        write = ArrayWrite(SSAVar("%array"), [SSAVar("%i")], SSAVar("%pod_8"), [])
        out = []
        _collect_population_write_candidates([fresh, write], {"%array": "comp"}, {}, {}, out)
        assert out == []


# ── _find_array_component_population_sequences (full integration) ─────────────

class TestFindArrayComponentPopulationSequences:
    """
    End-to-end: for each array-of-components member populated inside at
    least one genuinely symbolic loop, computes the real sequence of
    concrete array-index tuples the population loop(s) actually visit, in
    true execution order.
    """

    def _population_nest(self, array="%array", idx_names=("%i",), lb=0, ub=2, step=1):
        """
        A single scf.for population nest: reads the counting-pod array,
        writes it straight back (a trivial but valid read-modify-write),
        indexed by one or more freshly-declared induction variables (one
        scf.for per name, innermost holding the read/write).
        """
        read = ArrayRead(SSAVar("%14"), SSAVar(array), [SSAVar(n) for n in idx_names], [])
        write = ArrayWrite(SSAVar(array), [SSAVar(n) for n in idx_names], SSAVar("%14"), [])
        body = [read, write]
        for name in reversed(idx_names):
            body = [SCFFor([], SSAVar(name), SSAVar(f"%lb{name}"), SSAVar(f"%ub{name}"),
                           SSAVar(f"%step{name}"), [], body)]
        const_map = {}
        for name in idx_names:
            const_map[f"%lb{name}"] = lb
            const_map[f"%ub{name}"] = ub
            const_map[f"%step{name}"] = step
        return body, const_map

    def _consts(self, const_map):
        return [FeltConst(SSAVar(name), value) for name, value in const_map.items()]

    def test_simple_scf_for_population(self):
        nest, const_map = self._population_nest(idx_names=("%i",), lb=0, ub=3, step=1)
        body = self._consts(const_map) + nest
        result = _find_array_component_population_sequences(body, {"%array": "comp"})
        assert result == {"comp": [(0,), (1,), (2,)]}

    def test_simple_scf_while_population(self):
        after_body = [
            FeltConst(SSAVar("%c1"), 1),
            ArrayRead(SSAVar("%14"), SSAVar("%array"), [SSAVar("%arg1")], []),
            ArrayWrite(SSAVar("%array"), [SSAVar("%arg1")], SSAVar("%14"), []),
            FeltBinary(SSAVar("%next"), "felt.add", SSAVar("%arg1"), SSAVar("%c1"), []),
            SCFYield([SSAVar("%next")], [Type("index")]),
        ]
        before_body = [
            FeltConst(SSAVar("%c2"), 2),
            BoolCmp(SSAVar("%cond"), "lt", SSAVar("%arg1"), SSAVar("%c2")),
            SCFCondition(SSAVar("%cond"), [SSAVar("%arg1")], [Type("index")]),
        ]
        loop = SCFWhile(
            [], [(SSAVar("%arg1"), SSAVar("%c0"))], [[Type("index")], [Type("index")]],
            before_body, [(SSAVar("%arg1"), Type("index"))], after_body,
        )
        body = [FeltConst(SSAVar("%c0"), 0), loop]
        result = _find_array_component_population_sequences(body, {"%array": "comp"})
        assert result == {"comp": [(0,), (1,)]}

    def test_2d_dimension_order_differs_from_nesting_order(self):
        # Mirrors arbitrary_traversal_array_components.circom's actual
        # shape: components[i][j], i (dim 0) driven by the INNER loop, j
        # (dim 1) by the OUTER loop.
        read = ArrayRead(SSAVar("%14"), SSAVar("%array"), [SSAVar("%7"), SSAVar("%8")], [])
        write = ArrayWrite(SSAVar("%array"), [SSAVar("%7"), SSAVar("%8")], SSAVar("%14"), [])
        cast_i = CastToIndex(SSAVar("%7"), SSAVar("%i"))
        cast_j = CastToIndex(SSAVar("%8"), SSAVar("%j"))
        inner_i = SCFFor([], SSAVar("%i"), SSAVar("%lbi"), SSAVar("%ubi"), SSAVar("%stepi"),
                         [], [cast_i, cast_j, read, write])
        outer_j = SCFFor([], SSAVar("%j"), SSAVar("%lbj"), SSAVar("%ubj"), SSAVar("%stepj"),
                         [], [inner_i])
        body = [
            FeltConst(SSAVar("%lbi"), 0), FeltConst(SSAVar("%ubi"), 5), FeltConst(SSAVar("%stepi"), 2),
            FeltConst(SSAVar("%lbj"), 0), FeltConst(SSAVar("%ubj"), 4), FeltConst(SSAVar("%stepj"), 2),
            outer_j,
        ]
        result = _find_array_component_population_sequences(body, {"%array": "components"})
        assert result == {"components": [(0, 0), (2, 0), (4, 0), (0, 2), (2, 2), (4, 2)]}

    def test_two_separate_nests_concatenated_in_body_order(self):
        # Mirrors arbitrary_traversal_array_components.circom's own
        # even-index and odd-index nests -- two SEPARATE scf.for loops
        # populating the same member, run strictly sequentially. Each
        # nest's own induction variable and bounds get distinct SSA names,
        # matching real LLZK output's own SSA-uniqueness guarantee (a
        # literal name is never redefined with a different value within
        # the same function).
        nest1, const1 = self._population_nest(idx_names=("%i1",), lb=0, ub=2, step=1)
        nest2, const2 = self._population_nest(idx_names=("%i2",), lb=2, ub=4, step=1)
        body = self._consts(const1) + nest1 + self._consts(const2) + nest2
        result = _find_array_component_population_sequences(body, {"%array": "comp"})
        assert result == {"comp": [(0,), (1,), (2,), (3,)]}

    def test_unresolvable_bound_member_absent_from_result(self):
        # No consts defining %lb/%ub at all -- the population site is found
        # structurally but its own sequence can't be computed.
        nest, _ = self._population_nest(idx_names=("%i",))
        result = _find_array_component_population_sequences(nest, {"%array": "comp"})
        assert result == {}

    def test_no_population_at_all_returns_empty(self):
        result = _find_array_component_population_sequences([], {"%array": "comp"})
        assert result == {}

    def test_duplicate_checkpoints_in_same_scope_keeps_only_last(self):
        # Mirrors the real multi-input-signal shape: two structurally valid
        # population writes exist in the SAME scf.for body (one per
        # checkpoint) -- only the textually last is the real one.
        read1 = ArrayRead(SSAVar("%14"), SSAVar("%array"), [SSAVar("%i")], [])
        write1 = ArrayWrite(SSAVar("%array"), [SSAVar("%i")], SSAVar("%14"), [])
        branch1 = SCFIf([], SSAVar("%cond1"), [], [read1, write1], None)

        read2 = ArrayRead(SSAVar("%32"), SSAVar("%array"), [SSAVar("%i")], [])
        write2 = ArrayWrite(SSAVar("%array"), [SSAVar("%i")], SSAVar("%32"), [])
        branch2 = SCFIf([], SSAVar("%cond2"), [], [read2, write2], None)

        loop = SCFFor([], SSAVar("%i"), SSAVar("%lb"), SSAVar("%ub"), SSAVar("%step"),
                      [], [branch1, branch2])
        body = [FeltConst(SSAVar("%lb"), 0), FeltConst(SSAVar("%ub"), 3), FeltConst(SSAVar("%step"), 1), loop]
        result = _find_array_component_population_sequences(body, {"%array": "comp"})
        # Exactly one sequence recorded (not duplicated 2x) -- the dedup
        # itself is what's under test; the exact write chosen is opaque
        # from the outside since both are structurally identical.
        assert result == {"comp": [(0,), (1,), (2,)]}

    def test_scf_while_population_via_after_region_block_arg(self):
        # Regression for the poseidon3_test_concrete.mlir "sigmaF"/"sigmaP"
        # bug: array_member_base is keyed by the counting array's SSA name
        # as seen in the POST-loop bulk-copy nest -- the while's own result
        # component ("%421#1") -- but the real population write lives
        # INSIDE the while's after-region, referencing the array via that
        # region's OWN block-arg name ("%arg9"), never "%421#1" directly.
        # Before the fix, this was structurally invisible to
        # _collect_population_write_candidates (op.arr_ref.name ==
        # "%arg9" was never "in array_member_base"), so the whole member
        # was silently absent from the result. Also uses a DIFFERENT name
        # for the before-region's own block-arg ("%arg3") for the same
        # array, and a different name for the index in each region
        # ("%arg_idx" vs "%arg_idx_after") -- confirming the fix resolves
        # via after_args specifically, not by init_args/after_args
        # happening to share the same printed name.
        read = ArrayRead(SSAVar("%14"), SSAVar("%arg9"), [SSAVar("%arg_idx_after")], [])
        write = ArrayWrite(SSAVar("%arg9"), [SSAVar("%arg_idx_after")], SSAVar("%14"), [])
        after_body = [
            FeltConst(SSAVar("%c1"), 1),
            read, write,
            FeltBinary(SSAVar("%next"), "felt.add", SSAVar("%arg_idx_after"), SSAVar("%c1"), []),
            SCFYield([SSAVar("%next"), SSAVar("%arg9")], [Type("index"), Type("index")]),
        ]
        before_body = [
            FeltConst(SSAVar("%c2"), 2),
            BoolCmp(SSAVar("%cond"), "lt", SSAVar("%arg_idx"), SSAVar("%c2")),
            SCFCondition(SSAVar("%cond"), [SSAVar("%arg_idx"), SSAVar("%arg3")],
                        [Type("index"), Type("index")]),
        ]
        loop = SCFWhile(
            [SSAVar("%421", 2)],
            [(SSAVar("%arg_idx"), SSAVar("%c0")), (SSAVar("%arg3"), SSAVar("%outer_array"))],
            [[Type("index"), Type("index")], [Type("index"), Type("index")]],
            before_body,
            [(SSAVar("%arg_idx_after"), Type("index")), (SSAVar("%arg9"), Type("index"))],
            after_body,
        )
        body = [FeltConst(SSAVar("%c0"), 0), loop]
        result = _find_array_component_population_sequences(body, {"%421#1": "comp"})
        assert result == {"comp": [(0,), (1,)]}

    def test_scf_while_population_via_after_region_block_arg_nested_in_scf_if(self):
        # Same after-region block-arg aliasing as above, but the population
        # write itself sits inside an scf.if within the after-region --
        # mirrors the real "ready to call yet?" checkpoint idiom
        # (_collect_population_write_candidates' own docstring), confirming
        # the extended array_member_base is threaded through that nesting
        # too, not just direct after-region statements.
        read = ArrayRead(SSAVar("%14"), SSAVar("%arg9"), [SSAVar("%arg_idx_after")], [])
        write = ArrayWrite(SSAVar("%arg9"), [SSAVar("%arg_idx_after")], SSAVar("%14"), [])
        checkpoint = SCFIf([], SSAVar("%ready"), [], [read, write], None)
        after_body = [
            FeltConst(SSAVar("%c1"), 1),
            checkpoint,
            FeltBinary(SSAVar("%next"), "felt.add", SSAVar("%arg_idx_after"), SSAVar("%c1"), []),
            SCFYield([SSAVar("%next"), SSAVar("%arg9")], [Type("index"), Type("index")]),
        ]
        before_body = [
            FeltConst(SSAVar("%c2"), 2),
            BoolCmp(SSAVar("%cond"), "lt", SSAVar("%arg_idx"), SSAVar("%c2")),
            SCFCondition(SSAVar("%cond"), [SSAVar("%arg_idx"), SSAVar("%arg3")],
                        [Type("index"), Type("index")]),
        ]
        loop = SCFWhile(
            [SSAVar("%421", 2)],
            [(SSAVar("%arg_idx"), SSAVar("%c0")), (SSAVar("%arg3"), SSAVar("%outer_array"))],
            [[Type("index"), Type("index")], [Type("index"), Type("index")]],
            before_body,
            [(SSAVar("%arg_idx_after"), Type("index")), (SSAVar("%arg9"), Type("index"))],
            after_body,
        )
        body = [FeltConst(SSAVar("%c0"), 0), loop]
        result = _find_array_component_population_sequences(body, {"%421#1": "comp"})
        assert result == {"comp": [(0,), (1,)]}

    def test_compile_time_constant_index_skipped(self):
        # A write outside any loop (loop_stack empty) is the ALREADY-fully-
        # resolved compile-time-constant case (Part 2b) -- this pre-pass
        # must not also produce a (spurious, single-element) sequence for
        # it.
        const0 = FeltConst(SSAVar("%c0"), 0)
        cast0 = CastToIndex(SSAVar("%i0"), SSAVar("%c0"))
        read = ArrayRead(SSAVar("%14"), SSAVar("%array"), [SSAVar("%i0")], [])
        write = ArrayWrite(SSAVar("%array"), [SSAVar("%i0")], SSAVar("%14"), [])
        body = [const0, cast0, read, write]
        result = _find_array_component_population_sequences(body, {"%array": "comp"})
        assert result == {}
