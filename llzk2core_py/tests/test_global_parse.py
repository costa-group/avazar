import pytest
from src.llzk_dialects.global_ import GlobalDef, GlobalRead, GlobalWrite
from src.llzk_dialects.core import SSAVar, GlobalVariable, Type


class TestGlobal:

    # ── GlobalDef ─────────────────────────────────────────────────────────────

    def test_def_mutable(self):
        op = GlobalDef.parse("global.def @counter : !felt.type = 0")
        assert op.sym_name == GlobalVariable("@counter")
        assert op.type_ == Type("!felt.type")
        assert op.initial_value == "0"
        assert op.is_const is False

    def test_def_const(self):
        op = GlobalDef.parse("global.def const @PRIME : !felt.type = 17")
        assert op.is_const is True
        assert op.sym_name == GlobalVariable("@PRIME")

    def test_def_whitespace(self):
        op = GlobalDef.parse("  global.def @x : index = 0  ")
        assert op.sym_name == GlobalVariable("@x")

    def test_def_invalid(self):
        with pytest.raises(ValueError):
            GlobalDef.parse("global.def @x : !felt.type")  # missing = value

    # ── GlobalRead ────────────────────────────────────────────────────────────

    def test_read(self):
        op = GlobalRead.parse("%v = global.read @counter : !felt.type")
        assert op.result == SSAVar("%v")
        assert op.name_ref == GlobalVariable("@counter")
        assert op.result_type == Type("!felt.type")

    def test_read_whitespace(self):
        op = GlobalRead.parse("  %r = global.read @g : index  ")
        assert op.result == SSAVar("%r")

    def test_read_missing_type(self):
        with pytest.raises(ValueError):
            GlobalRead.parse("%v = global.read @counter")

    def test_read_match(self):
        assert GlobalRead.match("%v = global.read @x : !felt.type") is True
        assert GlobalRead.match("global.write @x = %v : !felt.type") is False

    # ── GlobalWrite ───────────────────────────────────────────────────────────

    def test_write(self):
        op = GlobalWrite.parse("global.write @counter = %new_val : !felt.type")
        assert op.name_ref == GlobalVariable("@counter")
        assert op.value == SSAVar("%new_val")
        assert op.value_type == Type("!felt.type")

    def test_write_whitespace(self):
        op = GlobalWrite.parse("  global.write @g = %v : index  ")
        assert op.name_ref == GlobalVariable("@g")

    def test_write_invalid(self):
        with pytest.raises(ValueError):
            GlobalWrite.parse("global.write @x %v : !felt.type")  # missing =

    def test_write_match(self):
        assert GlobalWrite.match("global.write @x = %v : !felt.type") is True
        assert GlobalWrite.match("%v = global.read @x : !felt.type") is False
