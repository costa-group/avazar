import pytest
from src.llzk_dialects.felt import FeltUnary, FeltBinary, FeltConst
from src.llzk_dialects.core import SSAVar, Type


class TestFelt:

    # ── FeltConst ─────────────────────────────────────────────────────────────

    def test_const(self):
        op = FeltConst.parse("        %felt_const_1 = felt.const  1  ")
        assert op.result == SSAVar("%felt_const_1")
        assert op.constant == 1

    def test_const_zero(self):
        op = FeltConst.parse("%z = felt.const 0")
        assert op.constant == 0

    def test_const_large(self):
        op = FeltConst.parse("%big = felt.const 999999999999")
        assert op.constant == 999999999999

    def test_const_invalid(self):
        with pytest.raises((ValueError, AssertionError)):
            FeltConst.parse("%x = felt.const")  # missing value

    # ── FeltUnary ─────────────────────────────────────────────────────────────

    def test_unary_simplified(self):
        op = FeltUnary.parse("   %0 = felt.bit_not %arg0 ")
        assert op.op == "felt.bit_not"
        assert op.result == SSAVar('%0')
        assert op.operand == SSAVar('%arg0')
        assert op.types == []

    def test_unary_full(self):
        op = FeltUnary.parse("        %10 = felt.inv %50 : !felt.type   ")
        assert op.op == "felt.inv"
        assert op.result == SSAVar('%10')
        assert op.operand == SSAVar('%50')
        assert op.types == [Type("!felt.type")]

    def test_unary_neg(self):
        op = FeltUnary.parse("%r = felt.neg %x")
        assert op.op == "felt.neg"
        assert op.operand == SSAVar("%x")

    def test_unary_invalid_op(self):
        with pytest.raises((ValueError, AssertionError), match=".*felt.op.*"):
            FeltUnary.parse("       %0 = felt.op %arg0 : !felt.type ")

    def test_unary_match(self):
        assert FeltUnary.match("  %r = felt.inv %x") is True
        assert FeltUnary.match("  %r = felt.add %x, %y") is False

    # ── FeltBinary ────────────────────────────────────────────────────────────

    def test_binary_simplified(self):
        op = FeltBinary.parse("   %0 = felt.mul %arg0, %arg1 ")
        assert op.op == "felt.mul"
        assert op.result == SSAVar('%0')
        assert op.lhs == SSAVar('%arg0')
        assert op.rhs == SSAVar('%arg1')
        assert op.types == []

    def test_binary_full(self):
        op = FeltBinary.parse(
            "        %10 = felt.bit_and %50, %81 : !felt.type, !felt.type   "
        )
        assert op.op == "felt.bit_and"
        assert op.result == SSAVar('%10')
        assert op.lhs == SSAVar('%50')
        assert op.rhs == SSAVar('%81')
        assert op.types == [Type("!felt.type"), Type("!felt.type")]

    def test_binary_sub(self):
        op = FeltBinary.parse("%r = felt.sub %a, %b")
        assert op.op == "felt.sub"

    def test_binary_invalid_op(self):
        with pytest.raises((ValueError, AssertionError), match=".*felt.op.*"):
            FeltBinary.parse("       %0 = felt.op %arg0, %arg1 ")

    def test_binary_match(self):
        assert FeltBinary.match("%r = felt.add %x, %y") is True
        assert FeltBinary.match("%r = felt.inv %x") is False
