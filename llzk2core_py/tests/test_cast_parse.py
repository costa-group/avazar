import pytest
from llzk_dialects.cast import CastToFelt, CastToIndex
from llzk_dialects.core import SSAVar, Type


class TestCast:

    # ── CastToFelt ────────────────────────────────────────────────────────────

    def test_tofelt_from_index(self):
        op = CastToFelt.parse("%r = cast.tofelt %idx : index")
        assert op.result == SSAVar("%r")
        assert op.value == SSAVar("%idx")
        assert op.src_type == Type("index")

    def test_tofelt_from_bool(self):
        op = CastToFelt.parse("  %f = cast.tofelt %b : i1  ")
        assert op.value == SSAVar("%b")
        assert op.src_type == Type("i1")

    def test_tofelt_missing_type(self):
        with pytest.raises(ValueError):
            CastToFelt.parse("%r = cast.tofelt %x")  # type is required

    def test_tofelt_match(self):
        assert CastToFelt.match("%r = cast.tofelt %x : index") is True
        assert CastToFelt.match("%r = cast.toindex %x") is False

    # ── CastToIndex ───────────────────────────────────────────────────────────

    def test_toindex(self):
        op = CastToIndex.parse("%i = cast.toindex %f")
        assert op.result == SSAVar("%i")
        assert op.value == SSAVar("%f")

    def test_toindex_whitespace(self):
        op = CastToIndex.parse("   %idx = cast.toindex %felt_val   ")
        assert op.result == SSAVar("%idx")
        assert op.value == SSAVar("%felt_val")

    def test_toindex_invalid(self):
        with pytest.raises(ValueError):
            CastToIndex.parse("%i = cast.toindex")  # missing operand

    def test_toindex_match(self):
        assert CastToIndex.match("%i = cast.toindex %f") is True
        assert CastToIndex.match("%i = cast.tofelt %x : i1") is False
