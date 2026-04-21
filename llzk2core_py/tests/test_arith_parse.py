import pytest
from llzk_dialects.arith import ArithConst, ArithBinary, ArithCmpi, ArithCast
from llzk_dialects.core import SSAVar, Type


class TestArith:

    # ── ArithConst ────────────────────────────────────────────────────────────

    def test_const_integer(self):
        op = ArithConst.parse("%c = arith.constant 42 : i32")
        assert op.result == SSAVar("%c")
        assert op.value == "42"
        assert op.result_type == Type("i32")

    def test_const_index(self):
        op = ArithConst.parse("%n = arith.constant 0 : index")
        assert op.value == "0"
        assert op.result_type == Type("index")

    def test_const_negative(self):
        op = ArithConst.parse("%m = arith.constant -1 : i64")
        assert op.value == "-1"

    def test_const_invalid(self):
        with pytest.raises(ValueError):
            ArithConst.parse("%c = arith.constant : i32")  # missing value

    def test_const_match(self):
        assert ArithConst.match("%c = arith.constant 1 : i32") is True
        assert ArithConst.match("%r = arith.addi %a, %b : i32") is False

    # ── ArithBinary ───────────────────────────────────────────────────────────

    def test_binary_addi(self):
        op = ArithBinary.parse("%r = arith.addi %a, %b : i32")
        assert op.result == SSAVar("%r")
        assert op.op == "arith.addi"
        assert op.lhs == SSAVar("%a")
        assert op.rhs == SSAVar("%b")
        assert op.operand_type == Type("i32")

    def test_binary_index(self):
        op = ArithBinary.parse("%r = arith.addi %a, %b : index")
        assert op.operand_type == Type("index")

    def test_binary_muli(self):
        op = ArithBinary.parse("%r = arith.muli %x, %y : i64")
        assert op.op == "arith.muli"

    def test_binary_bitwise(self):
        op = ArithBinary.parse("%r = arith.andi %a, %b : i32")
        assert op.op == "arith.andi"

    def test_binary_invalid_op(self):
        with pytest.raises(AssertionError):
            ArithBinary.parse("%r = arith.unknown %a, %b : i32")

    def test_binary_match(self):
        assert ArithBinary.match("%r = arith.subi %a, %b : i32") is True
        assert ArithBinary.match("%c = arith.constant 1 : i32") is False

    # ── ArithCmpi ─────────────────────────────────────────────────────────────

    def test_cmpi_eq(self):
        op = ArithCmpi.parse("%r = arith.cmpi eq, %a, %b : i32")
        assert op.result == SSAVar("%r")
        assert op.predicate == "eq"
        assert op.lhs == SSAVar("%a")
        assert op.rhs == SSAVar("%b")
        assert op.operand_type == Type("i32")

    def test_cmpi_signed(self):
        op = ArithCmpi.parse("%r = arith.cmpi slt, %x, %y : index")
        assert op.predicate == "slt"

    def test_cmpi_unsigned(self):
        op = ArithCmpi.parse("%r = arith.cmpi ult, %x, %y : i64")
        assert op.predicate == "ult"

    def test_cmpi_invalid_predicate(self):
        with pytest.raises(AssertionError):
            ArithCmpi.parse("%r = arith.cmpi bad, %a, %b : i32")

    def test_cmpi_match(self):
        assert ArithCmpi.match("%r = arith.cmpi ne, %a, %b : i32") is True
        assert ArithCmpi.match("%r = arith.addi %a, %b : i32") is False

    # ── ArithCast ─────────────────────────────────────────────────────────────

    def test_cast_extsi(self):
        op = ArithCast.parse("%r = arith.extsi %a : i32 to i64")
        assert op.result == SSAVar("%r")
        assert op.op == "arith.extsi"
        assert op.operand == SSAVar("%a")
        assert op.src_type == Type("i32")
        assert op.dst_type == Type("i64")

    def test_cast_trunci(self):
        op = ArithCast.parse("%r = arith.trunci %a : i64 to i32")
        assert op.op == "arith.trunci"
        assert op.src_type == Type("i64")
        assert op.dst_type == Type("i32")

    def test_cast_index_cast(self):
        op = ArithCast.parse("%r = arith.index_cast %a : i32 to index")
        assert op.op == "arith.index_cast"
        assert op.dst_type == Type("index")

    def test_cast_index_castui(self):
        op = ArithCast.parse("%r = arith.index_castui %a : index to i64")
        assert op.op == "arith.index_castui"

    def test_cast_invalid_op(self):
        with pytest.raises(AssertionError):
            ArithCast.parse("%r = arith.unknown %a : i32 to i64")

    def test_cast_match(self):
        assert ArithCast.match("%r = arith.extui %a : i32 to i64") is True
        assert ArithCast.match("%r = arith.cmpi eq, %a, %b : i32") is False
