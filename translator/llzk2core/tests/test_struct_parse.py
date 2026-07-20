import pytest
from llzk_dialects.struct import (
    StructMember, StructNew, StructReadm, StructWritem, StructDef,
    _annotate_function_calls, _fold_index_constants, _find_array_component_bases,
    _annotate_array_component_reads, _build_component_naming_maps,
)
from llzk_dialects.function import FunctionCall
from llzk_dialects.pod import PodNew, PodWrite, PodRead
from llzk_dialects.scf import SCFIf, SCFFor
from llzk_dialects.array import ArrayRead, ArrayWrite
from llzk_dialects.arith import ArithConst
from llzk_dialects.cast import CastToIndex
from llzk_dialects.core import SSAVar, GlobalVariable, Type, TranslationContext, LoopIndexedName
from llzk_dialects.felt import FeltConst


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
    array-of-components slot (e.g. "last_0") to its counting-pod read,
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


# ── _annotate_array_component_reads ────────────────────────────────────────────

class TestAnnotateArrayComponentReads:
    """
    Recursive walk that names a counting-pod array read either "base_idx"
    (constant index) or the bare "base" (non-constant index, e.g. a real
    scf.while iteration variable), feeding the same pod_to_member map that
    _annotate_function_calls consumes.
    """

    def test_constant_index_gets_subindex_name(self):
        const = FeltConst(SSAVar("%c0"), 0)
        cast = CastToIndex(SSAVar("%i0"), SSAVar("%c0"))
        read = ArrayRead(SSAVar("%8"), SSAVar("%array"), [SSAVar("%i0")], [])
        pod_to_member = {}
        _annotate_array_component_reads([const, cast, read], {"%array": "last"}, {}, pod_to_member)
        assert pod_to_member["%8"] == "last_0"

    def test_non_constant_index_gets_loop_indexed_name(self):
        # %arg4 is never folded to a constant anywhere — a genuine loop var.
        # SCFFor/SCFWhile.to_core resolves this into "Num2Bits_16_325#i" if
        # it unrolls the enclosing loop, or the bare name otherwise.
        read = ArrayRead(SSAVar("%15"), SSAVar("%array"), [SSAVar("%arg4")], [])
        pod_to_member = {}
        _annotate_array_component_reads([read], {"%array": "Num2Bits_16_325"}, {}, pod_to_member)
        assert pod_to_member["%15"] == LoopIndexedName("Num2Bits_16_325")

    def test_recurses_into_nested_body_using_inherited_constants(self):
        const = FeltConst(SSAVar("%c1"), 1)
        cast = CastToIndex(SSAVar("%i1"), SSAVar("%c1"))
        read = ArrayRead(SSAVar("%9"), SSAVar("%array"), [SSAVar("%i1")], [])
        inner_if = SCFIf([], SSAVar("%cond"), [], [read], None)
        pod_to_member = {}
        _annotate_array_component_reads([const, cast, inner_if], {"%array": "last"}, {}, pod_to_member)
        assert pod_to_member["%9"] == "last_1"

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
        assert pod_to_member["%ra"] == "last_0"
        assert pod_to_member["%rb"] == "last_1"

    def test_unregistered_array_ignored(self):
        read = ArrayRead(SSAVar("%r"), SSAVar("%other_array"), [SSAVar("%i")], [])
        pod_to_member = {}
        _annotate_array_component_reads([read], {"%array": "last"}, {}, pod_to_member)
        assert "%r" not in pod_to_member


# ── _build_component_naming_maps — array-of-components integration ────────────

class TestBuildComponentNamingMapsArrays:
    """
    End-to-end (within the pre-pass): a read of the counting-pod array is
    named like a scalar subcomponent slot ("last_0"/"last_1") when its index
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

        assert call_0._member_hint == "last_0"
        assert call_1._member_hint == "last_1"

    def test_symbolic_loop_index_uses_loop_indexed_name(self):
        # Mirrors ternary_concrete.mlir's Num2Bits_16_325: subcomponents are
        # instantiated inside a real (scf.while-style) runtime loop, so the
        # counting-array read's index is never a compile-time constant.
        # SCFFor.to_core resolves this into "Num2Bits_16_325#i" per
        # iteration when it unrolls this exact loop (it does, since the
        # loop body contains a function.call — see scf.py's
        # _contains_function_call).
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

        assert call._member_hint == LoopIndexedName("Num2Bits_16_325")
