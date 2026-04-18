import pytest
from llzk_dialects.struct import StructMember, StructNew, StructReadm, StructWritem, StructDef
from llzk_dialects.core import SSAVar, GlobalVariable, Type
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
