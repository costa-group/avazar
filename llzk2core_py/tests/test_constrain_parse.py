import pytest
from src.llzk_dialects.constrain import ConstrainEq, ConstrainIn
from src.llzk_dialects.core import SSAVar, Type


class TestConstrain:

    # ── ConstrainEq ───────────────────────────────────────────────────────────

    def test_eq_simplified(self):
        op = ConstrainEq.parse("constrain.eq %a, %b")
        assert op.lhs == SSAVar("%a")
        assert op.rhs == SSAVar("%b")
        assert op.types == []

    def test_eq_with_type(self):
        op = ConstrainEq.parse("  constrain.eq %x, %y : !felt.type  ")
        assert op.lhs == SSAVar("%x")
        assert op.rhs == SSAVar("%y")
        assert op.types == [Type("!felt.type")]

    def test_eq_invalid(self):
        with pytest.raises(ValueError):
            ConstrainEq.parse("constrain.eq %a")  # single operand

    def test_eq_match(self):
        assert ConstrainEq.match("constrain.eq %a, %b") is True
        assert ConstrainEq.match("constrain.in %a, %b") is False

    # ── ConstrainIn ───────────────────────────────────────────────────────────

    def test_in_simplified(self):
        op = ConstrainIn.parse("constrain.in %v, %arr")
        assert op.lhs == SSAVar("%v")
        assert op.rhs == SSAVar("%arr")
        assert op.types == []

    def test_in_with_types(self):
        op = ConstrainIn.parse(
            "constrain.in %v, %arr : !felt.type, !array.type<index>"
        )
        assert op.types == [Type("!felt.type"), Type("!array.type<index>")]

    def test_in_match(self):
        assert ConstrainIn.match("constrain.in %a, %b") is True
        assert ConstrainIn.match("constrain.eq %a, %b") is False
