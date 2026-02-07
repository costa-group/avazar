import pytest
from src.llzk_dialects.felt import FeltUnary, FeltBinary, SSAVar, Type

class TestFelt:

    def test_unary_simplified(self):
        unary_simplified = FeltUnary.parse("   %0 = felt.bit_not %arg0 ")
        assert unary_simplified.op == "felt.bit_not"
        assert unary_simplified.result == SSAVar('%0', 1)
        assert unary_simplified.operand == SSAVar('%arg0', 1)
        assert unary_simplified.types == []

    def test_unary_full(self):
        unary_full = FeltUnary.parse("        %10 = felt.inv %50 : !felt.type   ")
        assert unary_full.op == "felt.inv"
        assert unary_full.result == SSAVar('%10', 1)
        assert unary_full.operand == SSAVar('%50', 1)
        assert unary_full.types == [Type("!felt.type")]

    def test_unary_op_not_valid(self):
        # Exception includes the wrong operand as part of the message
        with pytest.raises(Exception, match=".*felt.op.*"):
            binary_op_wrong_op = FeltUnary.parse("       %0 = felt.op %arg0 : !felt.type, !felt.type ")

    def test_binary_simplified(self):
        binary_simplified = FeltBinary.parse("   %0 = felt.mul %arg0, %arg1 ")
        assert binary_simplified.op == "felt.mul"
        assert binary_simplified.result == SSAVar('%0', 1)
        assert binary_simplified.lhs == SSAVar('%arg0', 1)
        assert binary_simplified.rhs == SSAVar('%arg1', 1)
        assert binary_simplified.types == []

    def test_binary_full(self):
        binary_full = FeltBinary.parse("        %10 = felt.bit_and %50, %81 : !felt.type, !felt.type   ")
        assert binary_full.op == "felt.bit_and"
        assert binary_full.result == SSAVar('%10', 1)
        assert binary_full.lhs == SSAVar('%50', 1)
        assert binary_full.rhs == SSAVar('%81', 1)
        assert binary_full.types == [Type("!felt.type"), Type("!felt.type")]

    def test_binary_op_not_valid(self):
        with pytest.raises(Exception, match=".*felt.op.*"):
            binary_op_wrong_op = FeltBinary.parse("       %0 = felt.op %arg0 : !felt.type, !felt.type ")
