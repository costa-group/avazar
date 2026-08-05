import pytest
from llzk_dialects.felt import FeltUnary, FeltBinary, FeltConst
from llzk_dialects.core import SSAVar, Type, TranslationContext


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

    # ── FeltBinary.to_core constant folding ──────────────────────────────────
    #
    # Needed so a chain of arithmetic rooted at an outer loop's induction
    # variable (only known once that loop is unrolled) keeps resolving to a
    # concrete int all the way through to a nested loop's bound.

    def test_binary_to_core_folds_when_both_operands_known(self):
        op = FeltBinary(SSAVar("%r"), "felt.add", SSAVar("%a"), SSAVar("%b"), [])
        ctx = TranslationContext()
        ctx.var2const["%a"] = 3
        ctx.var2const["%b"] = 4
        list(op.to_core(ctx))
        assert ctx.var2const["%r"] == 7

    def test_binary_to_core_uintdiv_folds(self):
        # Mirrors the babypbk_test_concrete.mlir chain: (%17 - 1) uintdiv 3.
        op = FeltBinary(SSAVar("%19"), "felt.uintdiv", SSAVar("%18"), SSAVar("%c3"), [])
        ctx = TranslationContext()
        ctx.var2const["%18"] = 248
        ctx.var2const["%c3"] = 3
        list(op.to_core(ctx))
        assert ctx.var2const["%19"] == 82

    def test_binary_to_core_does_not_fold_when_one_operand_unknown(self):
        op = FeltBinary(SSAVar("%r"), "felt.mul", SSAVar("%a"), SSAVar("%b"), [])
        ctx = TranslationContext()
        ctx.var2const["%a"] = 3
        list(op.to_core(ctx))
        assert "%r" not in ctx.var2const

    def test_binary_to_core_does_not_fold_when_both_operands_unknown(self):
        op = FeltBinary(SSAVar("%r"), "felt.add", SSAVar("%a"), SSAVar("%b"), [])
        ctx = TranslationContext()
        list(op.to_core(ctx))
        assert "%r" not in ctx.var2const

    def test_binary_to_core_div_by_zero_does_not_crash_or_fold(self):
        # SCFIf always translates both branches unconditionally, so a
        # guarded division that's only safe in the "real" branch may still
        # get folded-attempted here on the dead-for-this-iteration branch.
        op = FeltBinary(SSAVar("%r"), "felt.div", SSAVar("%a"), SSAVar("%b"), [])
        ctx = TranslationContext()
        ctx.var2const["%a"] = 10
        ctx.var2const["%b"] = 0
        list(op.to_core(ctx))  # must not raise
        assert "%r" not in ctx.var2const

    def test_binary_to_core_emits_same_line_as_before(self):
        op = FeltBinary(SSAVar("%r"), "felt.sub", SSAVar("%a"), SSAVar("%b"), [])
        ctx = TranslationContext()
        ctx.var2const["%a"] = 5
        ctx.var2const["%b"] = 2
        out = list(op.to_core(ctx))
        assert out == ["%r = felt.sub %a %b"]

    # ── FeltUnary.to_core constant folding ───────────────────────────────────

    def test_unary_to_core_folds_when_operand_known(self):
        op = FeltUnary(SSAVar("%r"), "felt.neg", SSAVar("%a"), [])
        ctx = TranslationContext()
        ctx.var2const["%a"] = 5
        list(op.to_core(ctx))
        assert ctx.var2const["%r"] == -5

    def test_unary_to_core_does_not_fold_when_operand_unknown(self):
        op = FeltUnary(SSAVar("%r"), "felt.neg", SSAVar("%a"), [])
        ctx = TranslationContext()
        list(op.to_core(ctx))
        assert "%r" not in ctx.var2const
