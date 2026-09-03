import pytest
from llzk_dialects.bool import BoolBinary, BoolNot, BoolCmp, BoolAssert
from llzk_dialects.core import SSAVar, TranslationContext


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

    # ── BoolBinary.to_core / BoolNot.to_core constant folding ────────────────
    #
    # Not required by the motivating example (a bare BoolCmp condition), but
    # closes the same gap for a bool.and/or/xor/not-gated scf.if elsewhere.

    def test_and_to_core_folds_when_both_operands_known(self):
        op = BoolBinary(SSAVar("%r"), "bool.and", SSAVar("%a"), SSAVar("%b"))
        ctx = TranslationContext()
        ctx.var2const["%a"] = 1
        ctx.var2const["%b"] = 0
        list(op.to_core(ctx))
        assert ctx.var2const["%r"] == 0

    def test_or_to_core_folds(self):
        op = BoolBinary(SSAVar("%r"), "bool.or", SSAVar("%a"), SSAVar("%b"))
        ctx = TranslationContext()
        ctx.var2const["%a"] = 1
        ctx.var2const["%b"] = 0
        list(op.to_core(ctx))
        assert ctx.var2const["%r"] == 1

    def test_binary_to_core_does_not_fold_when_operand_unknown(self):
        op = BoolBinary(SSAVar("%r"), "bool.and", SSAVar("%a"), SSAVar("%b"))
        ctx = TranslationContext()
        ctx.var2const["%a"] = 1
        list(op.to_core(ctx))
        assert "%r" not in ctx.var2const

    def test_not_to_core_folds_when_operand_known(self):
        op = BoolNot(SSAVar("%r"), SSAVar("%a"))
        ctx = TranslationContext()
        ctx.var2const["%a"] = 0
        list(op.to_core(ctx))
        assert ctx.var2const["%r"] == 1

    def test_not_to_core_does_not_fold_when_operand_unknown(self):
        op = BoolNot(SSAVar("%r"), SSAVar("%a"))
        ctx = TranslationContext()
        list(op.to_core(ctx))
        assert "%r" not in ctx.var2const

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

    # ── BoolCmp.to_core constant folding ──────────────────────────────────────
    #
    # This is what lets an scf.if's condition become a known compile-time
    # constant (see SCFIf.to_core), which transitively lets a nested loop's
    # bound resolve once an enclosing loop's induction variable is concrete.

    @pytest.mark.parametrize("pred,a,b,expected", [
        ("eq", 3, 3, 1), ("eq", 3, 4, 0),
        ("ne", 3, 4, 1), ("ne", 3, 3, 0),
        ("lt", 3, 4, 1), ("lt", 4, 3, 0),
        ("le", 3, 3, 1), ("le", 4, 3, 0),
        ("gt", 4, 3, 1), ("gt", 3, 4, 0),
        ("ge", 3, 3, 1), ("ge", 3, 4, 0),
    ])
    def test_cmp_to_core_folds_each_predicate(self, pred, a, b, expected):
        op = BoolCmp(SSAVar("%r"), pred, SSAVar("%a"), SSAVar("%b"), [])
        ctx = TranslationContext()
        ctx.var2const["%a"] = a
        ctx.var2const["%b"] = b
        list(op.to_core(ctx))
        assert ctx.var2const["%r"] == expected

    def test_cmp_to_core_does_not_fold_when_operand_unknown(self):
        op = BoolCmp(SSAVar("%r"), "lt", SSAVar("%a"), SSAVar("%b"), [])
        ctx = TranslationContext()
        ctx.var2const["%a"] = 3
        list(op.to_core(ctx))
        assert "%r" not in ctx.var2const

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
