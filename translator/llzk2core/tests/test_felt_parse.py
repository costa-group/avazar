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

    def test_binary_to_core_sub_wraps_at_prime(self):
        # felt.sub is genuine field arithmetic: 0 - 1 folds to prime-1, not
        # a raw -1 -- this is what makes a "for (i=n; i!=-1; i--)"-shaped
        # loop's simulation terminate correctly (see
        # smtprocessor10_test_concrete.mlir / TestPrimeAwareSimulation in
        # test_core_utils.py).
        op = FeltBinary(SSAVar("%r"), "felt.sub", SSAVar("%a"), SSAVar("%b"), [])
        ctx = TranslationContext()
        ctx.var2const["%a"] = 0
        ctx.var2const["%b"] = 1
        list(op.to_core(ctx))
        assert ctx.var2const["%r"] == ctx.prime - 1

    def test_binary_to_core_pow_uses_modular_exponentiation(self):
        op = FeltBinary(SSAVar("%r"), "felt.pow", SSAVar("%a"), SSAVar("%b"), [])
        ctx = TranslationContext()
        ctx.var2const["%a"] = 3
        ctx.var2const["%b"] = 5
        list(op.to_core(ctx))
        assert ctx.var2const["%r"] == pow(3, 5, ctx.prime)

    def test_binary_to_core_uintdiv_not_reduced_modulo_prime(self):
        # Confirms felt.uintdiv (an integer op, not field arithmetic) is
        # unaffected by prime-aware reduction, even for an operand that
        # would otherwise be near the field's modulus.
        op = FeltBinary(SSAVar("%r"), "felt.uintdiv", SSAVar("%a"), SSAVar("%b"), [])
        ctx = TranslationContext()
        ctx.var2const["%a"] = 100
        ctx.var2const["%b"] = 7
        list(op.to_core(ctx))
        assert ctx.var2const["%r"] == 100 // 7

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
        # felt.neg is genuine field arithmetic: the fold reduces modulo
        # ctx.prime (goldilocks by default), so -5 becomes prime-5, not a
        # raw negative Python int -- see core.py's TranslationContext.prime
        # and felt.py's _FIELD_ARITHMETIC_OPS.
        op = FeltUnary(SSAVar("%r"), "felt.neg", SSAVar("%a"), [])
        ctx = TranslationContext()
        ctx.var2const["%a"] = 5
        list(op.to_core(ctx))
        assert ctx.var2const["%r"] == ctx.prime - 5

    def test_unary_to_core_does_not_fold_when_operand_unknown(self):
        op = FeltUnary(SSAVar("%r"), "felt.neg", SSAVar("%a"), [])
        ctx = TranslationContext()
        list(op.to_core(ctx))
        assert "%r" not in ctx.var2const

    def test_felt_inv_is_a_real_modular_inverse(self):
        # Fermat's little theorem: x * inv(x) == 1 (mod prime). "1 // x"
        # (this codebase's behavior before it had a prime to work with) was
        # never correct -- see felt.py's FeltUnary.to_function.
        op = FeltUnary(SSAVar("%r"), "felt.inv", SSAVar("%a"), [])
        ctx = TranslationContext()
        ctx.var2const["%a"] = 5
        list(op.to_core(ctx))
        assert (5 * ctx.var2const["%r"]) % ctx.prime == 1

    def test_felt_inv_of_zero_raises_and_skips_the_fold(self):
        op = FeltUnary(SSAVar("%r"), "felt.inv", SSAVar("%a"), [])
        ctx = TranslationContext()
        ctx.var2const["%a"] = 0
        list(op.to_core(ctx))
        assert "%r" not in ctx.var2const

    def test_felt_inv_to_function_without_prime_matches_old_behavior(self):
        # Backward compatible: a caller not passing a prime (none of this
        # codebase's own call sites do this anymore, but to_function() is a
        # public-ish interface) keeps today's placeholder behavior.
        op = FeltUnary(SSAVar("%r"), "felt.inv", SSAVar("%a"), [])
        assert op.to_function()(5) == 1 // 5

    def test_felt_bit_not_is_not_reduced_modulo_prime(self):
        # felt.bit_not is a bitwise operation on the value's underlying bit
        # pattern (e.g. bit-extraction loops), not field arithmetic --
        # reducing it modulo the field's prime would be wrong, not just
        # unnecessary. Deliberately excluded from FeltUnary._FIELD_ARITHMETIC_OPS.
        op = FeltUnary(SSAVar("%r"), "felt.bit_not", SSAVar("%a"), [])
        ctx = TranslationContext()
        ctx.var2const["%a"] = 5
        list(op.to_core(ctx))
        assert ctx.var2const["%r"] == ~5
