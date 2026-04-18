import pytest
from llzk_dialects.bool import BoolBinary, BoolNot, BoolCmp, BoolAssert
from llzk_dialects.core import SSAVar


class TestBool:

    # ── BoolBinary ────────────────────────────────────────────────────────────

    def test_and(self):
        op = BoolBinary.parse("%r = bool.and %a, %b")
        assert op.op == "bool.and"
        assert op.result == SSAVar("%r")
        assert op.lhs == SSAVar("%a")
        assert op.rhs == SSAVar("%b")

    def test_or(self):
        op = BoolBinary.parse("  %res = bool.or %x, %y  ")
        assert op.op == "bool.or"

    def test_xor(self):
        op = BoolBinary.parse("%r = bool.xor %p, %q")
        assert op.op == "bool.xor"

    def test_binary_invalid_op(self):
        with pytest.raises((ValueError, AssertionError)):
            BoolBinary.parse("%r = bool.nand %a, %b")

    def test_binary_match(self):
        assert BoolBinary.match("%r = bool.and %a, %b") is True
        assert BoolBinary.match("%r = bool.not %a") is False

    # ── BoolNot ───────────────────────────────────────────────────────────────

    def test_not(self):
        op = BoolNot.parse("  %r = bool.not %cond  ")
        assert op.result == SSAVar("%r")
        assert op.operand == SSAVar("%cond")

    def test_not_invalid(self):
        with pytest.raises(ValueError):
            BoolNot.parse("%r = bool.not")  # missing operand

    def test_not_match(self):
        assert BoolNot.match("%r = bool.not %x") is True
        assert BoolNot.match("%r = bool.and %x, %y") is False

    # ── BoolCmp ───────────────────────────────────────────────────────────────

    def test_cmp_eq(self):
        op = BoolCmp.parse("%r = bool.cmp eq(%a, %b)")
        assert op.result == SSAVar("%r")
        assert op.predicate == "eq"
        assert op.lhs == SSAVar("%a")
        assert op.rhs == SSAVar("%b")

    def test_cmp_lt(self):
        op = BoolCmp.parse("  %c = bool.cmp lt(%x, %y)  ")
        assert op.predicate == "lt"

    def test_cmp_ge(self):
        op = BoolCmp.parse("%c = bool.cmp ge(%x, %y)")
        assert op.predicate == "ge"

    def test_cmp_invalid_predicate(self):
        with pytest.raises((ValueError, AssertionError)):
            BoolCmp.parse("%r = bool.cmp badpred(%a, %b)")

    def test_cmp_all_predicates(self):
        for pred in ("eq", "ne", "lt", "le", "gt", "ge"):
            op = BoolCmp.parse(f"%r = bool.cmp {pred}(%a, %b)")
            assert op.predicate == pred

    # ── BoolAssert ────────────────────────────────────────────────────────────

    def test_assert_no_msg(self):
        op = BoolAssert.parse("bool.assert %cond")
        assert op.condition == SSAVar("%cond")
        assert op.msg is None

    def test_assert_with_msg(self):
        op = BoolAssert.parse('  bool.assert %ok, "expected true"  ')
        assert op.condition == SSAVar("%ok")
        assert op.msg == '"expected true"'

    def test_assert_match(self):
        assert BoolAssert.match("bool.assert %c") is True
        assert BoolAssert.match("%r = bool.not %c") is False
