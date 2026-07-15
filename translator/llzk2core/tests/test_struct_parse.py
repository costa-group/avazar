import pytest
from llzk_dialects.struct import StructMember, StructNew, StructReadm, StructWritem, StructDef, _annotate_function_calls
from llzk_dialects.function import FunctionCall
from llzk_dialects.pod import PodNew, PodWrite
from llzk_dialects.scf import SCFIf
from llzk_dialects.core import SSAVar, GlobalVariable, Type, TranslationContext
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
