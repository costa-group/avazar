import pytest
from llzk_dialects.core_utils import (
    infer_n_repetitions_from_expressions,
    infer_iteration_sequence_from_expressions,
    construct_function_from_expressions,
    count_iterations,
    iterate_values,
    SymbolicSteps,
    _collect_setup_ops,
    _collect_free_var_names,
    _detect_affine_step,
    _combine_min_steps,
    translate_assignment_core_with_ctx,
)
from llzk_dialects.core import SSAVar, Type, TranslationContext
from llzk_dialects.felt import FeltConst, FeltBinary
from llzk_dialects.bool import BoolCmp, BoolBinary


def _felt_const(name, value):
    return FeltConst(SSAVar(name), value)


def _bool_and(name, lhs, rhs):
    return BoolBinary(SSAVar(name), "bool.and", SSAVar(lhs), SSAVar(rhs))


def _felt_binary(name, op, lhs, rhs):
    return FeltBinary(SSAVar(name), op, SSAVar(lhs), SSAVar(rhs), [])


class TestInferNRepetitions:
    """
    infer_n_repetitions_from_expressions identifies the loop-carried variable
    directly from initial_values membership (not from the caller's leftover
    "ground_variables" bookkeeping, which is unreliable when the variable's
    own recurrence collapses to a constant -- see test_collapsed_recurrence).
    """

    def _basic_var2expression(self, bound_name="%c2", predicate="lt"):
        # %arg1 starts at 0, increments by 1 each pass, condition
        # "%arg1 <predicate> bound_name".
        return {
            "%cond": BoolCmp(SSAVar("%cond"), predicate, SSAVar("%arg1"), SSAVar(bound_name)),
            "%arg1": "%next",
            "%next": _felt_binary("%next", "felt.add", "%arg1", "%c1"),
            "%c1": _felt_const("%c1", 1),
        }

    def test_simple_form_fully_resolved_bound_returns_concrete_int(self):
        var2expression = self._basic_var2expression()
        var2expression["%c2"] = _felt_const("%c2", 2)
        result = infer_n_repetitions_from_expressions(
            var2expression, "%cond", {"%arg1": 0}
        )
        assert result == 2

    def test_full_form_free_variable_resolved_via_var2const(self):
        # The bound ("%bound") isn't defined anywhere inside the while itself
        # (e.g. an enclosing function's own parameter) but IS known via
        # var2const -- folded in as a constant, same as a literal felt.const.
        var2expression = self._basic_var2expression(bound_name="%bound")
        result = infer_n_repetitions_from_expressions(
            var2expression, "%cond", {"%arg1": 0}, var2const={"%bound": 4}
        )
        assert result == 4

    def test_variable_recurrence_free_variable_resolved_via_var2const(self):
        # Regression test: mirrors poseidon3_new_optimized.mlir's
        # MixS_9::compute, whose loop-carried variable's own recurrence step
        # ("%next = felt.add %arg1, %c1") reuses a felt.const hoisted above
        # the while (no var2expression entry of its own) instead of
        # redefining it locally each iteration -- previously a raw KeyError
        # deep inside construct_function_from_expressions; now resolved via
        # var2const, same as an unresolved bound already was.
        var2expression = {
            "%cond": BoolCmp(SSAVar("%cond"), "lt", SSAVar("%arg1"), SSAVar("%c2")),
            "%c2": _felt_const("%c2", 2),
            "%arg1": "%next",
            "%next": _felt_binary("%next", "felt.add", "%arg1", "%c1"),
        }
        result = infer_n_repetitions_from_expressions(
            var2expression, "%cond", {"%arg1": 0}, var2const={"%c1": 1}
        )
        assert result == 2

    def test_variable_recurrence_unresolved_free_variable_raises(self):
        # Same shape, but %c1 isn't known via var2const either -- a clear
        # NotImplementedError instead of a raw KeyError.
        var2expression = {
            "%cond": BoolCmp(SSAVar("%cond"), "lt", SSAVar("%arg1"), SSAVar("%c2")),
            "%c2": _felt_const("%c2", 2),
            "%arg1": "%next",
            "%next": _felt_binary("%next", "felt.add", "%arg1", "%c1"),
        }
        with pytest.raises(NotImplementedError):
            infer_n_repetitions_from_expressions(var2expression, "%cond", {"%arg1": 0})

    def test_unresolved_bound_returns_symbolic_steps_lt(self):
        var2expression = self._basic_var2expression(bound_name="%bound")
        result = infer_n_repetitions_from_expressions(
            var2expression, "%cond", {"%arg1": 0}
        )
        assert isinstance(result, SymbolicSteps)
        assert result == SymbolicSteps(
            setup_ops=[], bound_var=SSAVar("%bound"), initial_value=0,
            op="lt", variable_is_lhs=True,
        )

    def test_unresolved_bound_returns_symbolic_steps_le(self):
        var2expression = self._basic_var2expression(bound_name="%bound", predicate="le")
        result = infer_n_repetitions_from_expressions(
            var2expression, "%cond", {"%arg1": 0}
        )
        assert isinstance(result, SymbolicSteps)
        assert result.op == "le"
        assert result.variable_is_lhs is True

    def test_unresolved_bound_variable_on_rhs_decreasing(self):
        # condition is "bound < arg1", so arg1 must decrease (step -1) each
        # iteration for the loop to terminate.
        var2expression = {
            "%cond": BoolCmp(SSAVar("%cond"), "lt", SSAVar("%bound"), SSAVar("%arg1")),
            "%arg1": "%next",
            "%next": _felt_binary("%next", "felt.sub", "%arg1", "%c1"),
            "%c1": _felt_const("%c1", 1),
        }
        result = infer_n_repetitions_from_expressions(
            var2expression, "%cond", {"%arg1": 5}
        )
        assert isinstance(result, SymbolicSteps)
        assert result.variable_is_lhs is False
        assert result.initial_value == 5
        assert result.bound_var == SSAVar("%bound")

    def test_gt_ge_predicates_normalized(self):
        # "gt"/"ge" get swapped to the equivalent "lt"/"le" form, same as
        # before this rewrite.
        var2expression = {
            "%cond": BoolCmp(SSAVar("%cond"), "gt", SSAVar("%c2"), SSAVar("%arg1")),
            "%arg1": "%next",
            "%next": _felt_binary("%next", "felt.add", "%arg1", "%c1"),
            "%c1": _felt_const("%c1", 1),
            "%c2": _felt_const("%c2", 2),
        }
        result = infer_n_repetitions_from_expressions(var2expression, "%cond", {"%arg1": 0})
        assert result == 2

    def test_ne_predicate_concrete_bound(self):
        # "ne" (concrete bound only -- see core_utils.py:485's assert):
        # continues while unequal, same trip count as the equivalent "lt"
        # here since the step is a plain +1 -- mirrors
        # smtprocessor10_test_concrete.mlir's "for (i=nLevels-1; i!=-1; i--)"
        # shape (ascending here for simplicity; the descending/wraparound
        # case is covered by TestPrimeAwareSimulation below).
        var2expression = self._basic_var2expression(predicate="ne")
        var2expression["%c2"] = _felt_const("%c2", 2)
        result = infer_n_repetitions_from_expressions(var2expression, "%cond", {"%arg1": 0})
        assert result == 2

    def test_eq_predicate_concrete_bound(self):
        # "eq": continues while EQUAL -- the mirror image of "ne". Starting
        # equal to the bound (0) runs exactly one iteration before the
        # update makes it diverge.
        var2expression = self._basic_var2expression(bound_name="%c0", predicate="eq")
        var2expression["%c0"] = _felt_const("%c0", 0)
        result = infer_n_repetitions_from_expressions(var2expression, "%cond", {"%arg1": 0})
        assert result == 1

    def test_ne_predicate_unresolved_bound_raises(self):
        # eq/ne stay concrete-bound-only: no known example needs a symbolic
        # eq/ne formula, and an eq/ne loop's termination isn't a monotonic
        # bound crossing the way lt/le/gt/ge's SymbolicSteps formula assumes.
        var2expression = self._basic_var2expression(bound_name="%bound", predicate="ne")
        with pytest.raises(NotImplementedError):
            infer_n_repetitions_from_expressions(var2expression, "%cond", {"%arg1": 0})

    def test_edge_case_collapsed_recurrence_to_constant(self):
        # Regression test: mirrors mux1_1_concrete.mlir's while, whose loop
        # variable is unconditionally reset to a literal each iteration
        # (arg1' = 1) rather than incremented (arg1' = arg1 + 1). Its
        # recurrence chain fully resolves to constants, so it never survives
        # as a "leftover" in the caller's backward-walk bookkeeping -- yet
        # it's still the genuine loop-carried variable, correctly identified
        # here via initial_values membership instead.
        var2expression = {
            "%cond": BoolCmp(SSAVar("%cond"), "lt", SSAVar("%arg1"), SSAVar("%c1")),
            "%c1": _felt_const("%c1", 1),
            "%arg1": "%reset_to_one",
            "%reset_to_one": _felt_const("%reset_to_one", 1),
        }
        result = infer_n_repetitions_from_expressions(var2expression, "%cond", {"%arg1": 0})
        assert result == 1

    def test_invalid_both_sides_loop_carried_raises(self):
        var2expression = {
            "%cond": BoolCmp(SSAVar("%cond"), "lt", SSAVar("%arg1"), SSAVar("%arg2")),
        }
        with pytest.raises(NotImplementedError):
            infer_n_repetitions_from_expressions(
                var2expression, "%cond", {"%arg1": 0, "%arg2": 5}
            )

    def test_invalid_neither_side_loop_carried_raises(self):
        var2expression = {
            "%cond": BoolCmp(SSAVar("%cond"), "lt", SSAVar("%a"), SSAVar("%b")),
        }
        with pytest.raises(NotImplementedError):
            infer_n_repetitions_from_expressions(var2expression, "%cond", {})

    def test_invalid_non_affine_update_with_unresolved_bound_raises(self):
        var2expression = {
            "%cond": BoolCmp(SSAVar("%cond"), "lt", SSAVar("%arg1"), SSAVar("%bound")),
            "%arg1": "%next",
            "%next": _felt_binary("%next", "felt.mul", "%arg1", "%two"),
            "%two": _felt_const("%two", 2),
        }
        with pytest.raises(NotImplementedError):
            infer_n_repetitions_from_expressions(var2expression, "%cond", {"%arg1": 1})

    def test_invalid_non_unit_step_with_unresolved_bound_raises(self):
        var2expression = {
            "%cond": BoolCmp(SSAVar("%cond"), "lt", SSAVar("%arg1"), SSAVar("%bound")),
            "%arg1": "%next",
            "%next": _felt_binary("%next", "felt.add", "%arg1", "%c2"),
            "%c2": _felt_const("%c2", 2),
        }
        with pytest.raises(NotImplementedError):
            infer_n_repetitions_from_expressions(var2expression, "%cond", {"%arg1": 0})

    def test_setup_ops_collected_for_expression_bound(self):
        # Mirrors escalarmulw4table_concrete.mlir's "%arg1 * 4" bound: %extern
        # is unresolved (an enclosing function's own parameter), %four is an
        # ordinary literal already present in var2expression.
        var2expression = {
            "%cond": BoolCmp(SSAVar("%cond"), "lt", SSAVar("%arg1"), SSAVar("%boundexpr")),
            "%arg1": "%next",
            "%next": _felt_binary("%next", "felt.add", "%arg1", "%c1"),
            "%c1": _felt_const("%c1", 1),
            "%boundexpr": _felt_binary("%boundexpr", "felt.mul", "%extern", "%four"),
            "%four": _felt_const("%four", 4),
        }
        result = infer_n_repetitions_from_expressions(var2expression, "%cond", {"%arg1": 0})
        assert isinstance(result, SymbolicSteps)
        assert result.bound_var == SSAVar("%boundexpr")
        assert [op.result for op in result.setup_ops] == [SSAVar("%four"), SSAVar("%boundexpr")]


class TestPrimeAwareSimulation:
    """
    construct_function_from_expressions (and therefore
    infer_n_repetitions_from_expressions/count_iterations) reduces every
    composed operation modulo `prime` -- this is what makes a descending
    counter correctly wrap to prime-1 instead of drifting off as a raw
    negative Python int, mirroring smtprocessor10_test_concrete.mlir's real
    "for (i=nLevels-1; i!=-1; i--)" shape, where circom's "-1" is
    represented as the field-wrapped prime-1.
    """

    def test_ne_predicate_wraps_at_prime_like_a_countdown_to_minus_one(self):
        # %arg1 starts at 2, decrements by 1 each pass, condition is
        # "%arg1 != 6" -- with prime=7, 6 is exactly how "-1" looks after
        # wraparound (7 - 1). Without prime-aware simulation this would
        # never terminate (2, 1, 0, -1, -2, ... never equals 6).
        var2expression = {
            "%cond": BoolCmp(SSAVar("%cond"), "ne", SSAVar("%arg1"), SSAVar("%bound")),
            "%bound": _felt_const("%bound", 6),
            "%arg1": "%next",
            "%next": _felt_binary("%next", "felt.sub", "%arg1", "%c1"),
            "%c1": _felt_const("%c1", 1),
        }
        result = infer_n_repetitions_from_expressions(
            var2expression, "%cond", {"%arg1": 2}, prime=7
        )
        # Visits 2, 1, 0 -- then 0 - 1 wraps to 6, matching the bound.
        assert result == 3

    def test_ge_predicate_terminates_after_wrapping_past_zero(self):
        # Mirrors report_zisk_reduced/recursivef_concrete.mlir's real
        # "@VerifyPoW_11" bug (pow.circom): a felt counter counting down to
        # AND INCLUDING 0 via "arg >= 0" (not a pre-wrapped equality bound
        # like the ne test above). With prime=7, starting at 2 and
        # decrementing: 2, 1, 0, then wraps to 6 (== -1 mod 7). Under a raw
        #/unsigned comparison "0 <= x", 6 still satisfies "x >= 0" forever
        # -- this is exactly what used to run the real simulation past its
        # 1,000,000-iteration safety cap. The canonical-signed
        # interpretation (_to_signed) correctly reads 6 as -1, so the
        # comparison goes false right after 0.
        var2expression = {
            "%cond": BoolCmp(SSAVar("%cond"), "ge", SSAVar("%arg1"), SSAVar("%bound")),
            "%bound": _felt_const("%bound", 0),
            "%arg1": "%next",
            "%next": _felt_binary("%next", "felt.sub", "%arg1", "%c1"),
            "%c1": _felt_const("%c1", 1),
        }
        result = infer_n_repetitions_from_expressions(
            var2expression, "%cond", {"%arg1": 2}, prime=7
        )
        # Visits 2, 1, 0 -- then wraps to 6, correctly read as negative.
        assert result == 3

    def test_le_predicate_bound_on_lhs_terminates_after_wrapping(self):
        # Same shape as above but with the loop variable on the RHS of the
        # comparison (bound <= arg, normalized the same way "gt" is).
        var2expression = {
            "%cond": BoolCmp(SSAVar("%cond"), "le", SSAVar("%bound"), SSAVar("%arg1")),
            "%bound": _felt_const("%bound", 0),
            "%arg1": "%next",
            "%next": _felt_binary("%next", "felt.sub", "%arg1", "%c1"),
            "%c1": _felt_const("%c1", 1),
        }
        result = infer_n_repetitions_from_expressions(
            var2expression, "%cond", {"%arg1": 2}, prime=7
        )
        assert result == 3

    def test_ge_predicate_non_wrapping_case_unaffected(self):
        # A counter that never approaches prime/2 must behave identically
        # to before this fix (the signed reinterpretation is a no-op below
        # prime/2) -- mirrors the real file's OTHER while (63 -> 42).
        var2expression = {
            "%cond": BoolCmp(SSAVar("%cond"), "ge", SSAVar("%arg1"), SSAVar("%bound")),
            "%bound": _felt_const("%bound", 42),
            "%arg1": "%next",
            "%next": _felt_binary("%next", "felt.sub", "%arg1", "%c1"),
            "%c1": _felt_const("%c1", 1),
        }
        result = infer_n_repetitions_from_expressions(
            var2expression, "%cond", {"%arg1": 63}
        )
        assert result == 22

    def test_construct_function_from_expressions_reduces_modulo_prime(self):
        var2expression = {
            "%r": _felt_binary("%r", "felt.sub", "%zero", "%one"),
            "%zero": _felt_const("%zero", 0),
            "%one": _felt_const("%one", 1),
        }
        fn = construct_function_from_expressions(SSAVar("%r"), var2expression, set(), prime=7)
        assert fn(0) == 6  # -1 mod 7

    def test_construct_function_from_expressions_defaults_to_goldilocks(self):
        var2expression = {
            "%r": _felt_binary("%r", "felt.sub", "%zero", "%one"),
            "%zero": _felt_const("%zero", 0),
            "%one": _felt_const("%one", 1),
        }
        fn = construct_function_from_expressions(SSAVar("%r"), var2expression, set())
        assert fn(0) == 18446744069414584321 - 1


class TestSimulationSafetyCap:
    """
    count_iterations/iterate_values fail fast on a non-terminating
    recurrence instead of hanging indefinitely -- a genuinely
    non-terminating shape (a translator bug, or one this codebase doesn't
    model correctly yet) should never silently freeze the translator.
    """

    def test_count_iterations_raises_instead_of_hanging(self, monkeypatch):
        import llzk_dialects.core_utils as core_utils_module
        monkeypatch.setattr(core_utils_module, "_MAX_SIMULATED_ITERATIONS", 100)
        with pytest.raises(RuntimeError):
            count_iterations(0, lambda x: True, lambda x: x + 1)

    def test_iterate_values_raises_instead_of_hanging(self, monkeypatch):
        import llzk_dialects.core_utils as core_utils_module
        monkeypatch.setattr(core_utils_module, "_MAX_SIMULATED_ITERATIONS", 100)
        with pytest.raises(RuntimeError):
            iterate_values(0, lambda x: True, lambda x: x + 1)


class TestCollectHelpers:
    def test_collect_setup_ops_skips_external_free_variable(self):
        var2expression = {
            "%boundexpr": _felt_binary("%boundexpr", "felt.mul", "%extern", "%four"),
            "%four": _felt_const("%four", 4),
        }
        ops = _collect_setup_ops(SSAVar("%boundexpr"), var2expression, set())
        assert [op.result for op in ops] == [SSAVar("%four"), SSAVar("%boundexpr")]

    def test_collect_setup_ops_on_bare_external_variable_needs_no_setup(self):
        assert _collect_setup_ops(SSAVar("%extern"), {}, set()) == []

    def test_collect_free_var_names_finds_unresolved_leaf(self):
        var2expression = {
            "%boundexpr": _felt_binary("%boundexpr", "felt.mul", "%extern", "%four"),
            "%four": _felt_const("%four", 4),
        }
        assert _collect_free_var_names(SSAVar("%boundexpr"), var2expression, set()) == {"%extern"}

    def test_collect_free_var_names_empty_when_fully_resolved(self):
        var2expression = {"%four": _felt_const("%four", 4)}
        assert _collect_free_var_names(SSAVar("%four"), var2expression, set()) == set()

    def test_detect_affine_step_positive(self):
        var2expression = {
            "%arg1": "%next",
            "%next": _felt_binary("%next", "felt.add", "%arg1", "%c1"),
            "%c1": _felt_const("%c1", 1),
        }
        update_func = construct_function_from_expressions(SSAVar("%arg1"), var2expression, set())
        assert _detect_affine_step(update_func) == 1

    def test_detect_affine_step_none_for_non_affine(self):
        var2expression = {
            "%arg1": "%next",
            "%next": _felt_binary("%next", "felt.mul", "%arg1", "%two"),
            "%two": _felt_const("%two", 2),
        }
        update_func = construct_function_from_expressions(SSAVar("%arg1"), var2expression, set())
        assert _detect_affine_step(update_func) is None


class TestBoolAndCondition:
    """
    A while condition that is bool.and(cmp1, cmp2): each half is inferred
    independently (as if it were the whole condition) and the smaller count
    wins, since the loop stops as soon as either half first goes false.
    """

    def test_same_loop_variable_takes_min(self):
        # Both halves track the same loop variable, with different bounds.
        var2expression = {
            "%cond": _bool_and("%cond", "%c1cond", "%c2cond"),
            "%c1cond": BoolCmp(SSAVar("%c1cond"), "lt", SSAVar("%arg1"), SSAVar("%b1")),
            "%b1": _felt_const("%b1", 5),
            "%c2cond": BoolCmp(SSAVar("%c2cond"), "lt", SSAVar("%arg1"), SSAVar("%b2")),
            "%b2": _felt_const("%b2", 3),
            "%arg1": "%next",
            "%next": _felt_binary("%next", "felt.add", "%arg1", "%c1"),
            "%c1": _felt_const("%c1", 1),
        }
        result = infer_n_repetitions_from_expressions(var2expression, "%cond", {"%arg1": 0})
        assert result == 3

    def test_different_loop_variables_takes_min(self):
        # Each half tracks a DIFFERENT loop-carried variable -- the min is
        # still correct, since each count already fully accounts for its own
        # condition's failure point in isolation.
        var2expression = {
            "%cond": _bool_and("%cond", "%acond", "%bcond"),
            "%acond": BoolCmp(SSAVar("%acond"), "lt", SSAVar("%a"), SSAVar("%boundA")),
            "%boundA": _felt_const("%boundA", 7),
            "%a": "%a_next",
            "%a_next": _felt_binary("%a_next", "felt.add", "%a", "%c1"),
            "%bcond": BoolCmp(SSAVar("%bcond"), "lt", SSAVar("%b"), SSAVar("%boundB")),
            "%boundB": _felt_const("%boundB", 2),
            "%b": "%b_next",
            "%b_next": _felt_binary("%b_next", "felt.add", "%b", "%c1"),
            "%c1": _felt_const("%c1", 1),
        }
        result = infer_n_repetitions_from_expressions(
            var2expression, "%cond", {"%a": 0, "%b": 0}
        )
        assert result == 2

    def test_gt_ge_normalized_combined_with_lt(self):
        var2expression = {
            "%cond": _bool_and("%cond", "%c1cond", "%c2cond"),
            # "gt" gets swapped to the equivalent "lt" form.
            "%c1cond": BoolCmp(SSAVar("%c1cond"), "gt", SSAVar("%b1"), SSAVar("%arg1")),
            "%b1": _felt_const("%b1", 5),
            "%c2cond": BoolCmp(SSAVar("%c2cond"), "lt", SSAVar("%arg1"), SSAVar("%b2")),
            "%b2": _felt_const("%b2", 3),
            "%arg1": "%next",
            "%next": _felt_binary("%next", "felt.add", "%arg1", "%c1"),
            "%c1": _felt_const("%c1", 1),
        }
        result = infer_n_repetitions_from_expressions(var2expression, "%cond", {"%arg1": 0})
        assert result == 3

    def test_raises_when_either_half_symbolic(self):
        # One half's bound is unresolved -- combining a symbolic count with
        # anything via min() is out of scope (would need a Core-level
        # conditional to pick the smaller at runtime).
        var2expression = {
            "%cond": _bool_and("%cond", "%c1cond", "%c2cond"),
            "%c1cond": BoolCmp(SSAVar("%c1cond"), "lt", SSAVar("%arg1"), SSAVar("%extern")),
            "%c2cond": BoolCmp(SSAVar("%c2cond"), "lt", SSAVar("%arg1"), SSAVar("%b2")),
            "%b2": _felt_const("%b2", 3),
            "%arg1": "%next",
            "%next": _felt_binary("%next", "felt.add", "%arg1", "%c1"),
            "%c1": _felt_const("%c1", 1),
        }
        with pytest.raises(NotImplementedError):
            infer_n_repetitions_from_expressions(var2expression, "%cond", {"%arg1": 0})

    def test_raises_when_operand_not_boolcmp(self):
        var2expression = {
            "%cond": _bool_and("%cond", "%nested_and", "%c2cond"),
            "%nested_and": _bool_and("%nested_and", "%c1cond", "%c1cond"),
            "%c1cond": BoolCmp(SSAVar("%c1cond"), "lt", SSAVar("%arg1"), SSAVar("%b1")),
            "%b1": _felt_const("%b1", 5),
            "%c2cond": BoolCmp(SSAVar("%c2cond"), "lt", SSAVar("%arg1"), SSAVar("%b2")),
            "%b2": _felt_const("%b2", 3),
        }
        with pytest.raises(AssertionError):
            infer_n_repetitions_from_expressions(var2expression, "%cond", {"%arg1": 0})

    def test_combine_min_steps_both_int(self):
        assert _combine_min_steps(5, 3) == 3

    def test_combine_min_steps_raises_with_symbolic(self):
        symbolic = SymbolicSteps([], SSAVar("%bound"), 0, "lt", True)
        with pytest.raises(NotImplementedError):
            _combine_min_steps(5, symbolic)


class TestIterateValues:
    """
    iterate_values: like count_iterations, but returns the actual sequence
    of values visited instead of just the count.
    """

    def test_returns_sequence_not_just_count(self):
        assert iterate_values(0, lambda x: x < 4, lambda x: x + 1) == [0, 1, 2, 3]

    def test_step_other_than_one(self):
        assert iterate_values(0, lambda x: x < 6, lambda x: x + 2) == [0, 2, 4]

    def test_zero_iterations(self):
        assert iterate_values(5, lambda x: x < 5, lambda x: x + 1) == []


class TestInferIterationSequence:
    """
    infer_iteration_sequence_from_expressions: like
    infer_n_repetitions_from_expressions, but returns the actual sequence of
    values the loop-carried variable visits instead of just the count --
    used by struct.py's array-component index-sequence pre-pass. Shares its
    resolution logic with the count-only path (_resolve_comparison_recurrence)
    so the two can never silently disagree about what a while loop does.
    """

    def _basic_var2expression(self, bound_name="%c2", predicate="lt"):
        return {
            "%cond": BoolCmp(SSAVar("%cond"), predicate, SSAVar("%arg1"), SSAVar(bound_name)),
            "%arg1": "%next",
            "%next": _felt_binary("%next", "felt.add", "%arg1", "%c1"),
            "%c1": _felt_const("%c1", 1),
        }

    def test_simple_form_returns_concrete_sequence(self):
        var2expression = self._basic_var2expression()
        var2expression["%c2"] = _felt_const("%c2", 3)
        result = infer_iteration_sequence_from_expressions(
            var2expression, "%cond", {"%arg1": 0}
        )
        assert result == [0, 1, 2]

    def test_free_variable_resolved_via_var2const(self):
        var2expression = self._basic_var2expression(bound_name="%bound")
        result = infer_iteration_sequence_from_expressions(
            var2expression, "%cond", {"%arg1": 0}, var2const={"%bound": 4}
        )
        assert result == [0, 1, 2, 3]

    def test_unresolved_bound_returns_none(self):
        # Mirrors test_unresolved_bound_returns_symbolic_steps_lt in
        # TestInferNRepetitions -- there's no way to list concrete values
        # for a count that's itself only known as a Core-level formula.
        var2expression = self._basic_var2expression(bound_name="%bound")
        result = infer_iteration_sequence_from_expressions(
            var2expression, "%cond", {"%arg1": 0}
        )
        assert result is None

    def test_bool_and_takes_shorter_sequence(self):
        # Mirrors TestBoolAndCondition.test_same_loop_variable_takes_min --
        # the loop stops as soon as either half first goes false, so the
        # shorter (not necessarily lexicographically smaller) sequence wins.
        var2expression = {
            "%cond": _bool_and("%cond", "%c1cond", "%c2cond"),
            "%c1cond": BoolCmp(SSAVar("%c1cond"), "lt", SSAVar("%arg1"), SSAVar("%b1")),
            "%b1": _felt_const("%b1", 5),
            "%c2cond": BoolCmp(SSAVar("%c2cond"), "lt", SSAVar("%arg1"), SSAVar("%b2")),
            "%b2": _felt_const("%b2", 3),
            "%arg1": "%next",
            "%next": _felt_binary("%next", "felt.add", "%arg1", "%c1"),
            "%c1": _felt_const("%c1", 1),
        }
        result = infer_iteration_sequence_from_expressions(var2expression, "%cond", {"%arg1": 0})
        assert result == [0, 1, 2]

    def test_bool_and_either_half_unresolved_returns_none(self):
        var2expression = {
            "%cond": _bool_and("%cond", "%c1cond", "%c2cond"),
            "%c1cond": BoolCmp(SSAVar("%c1cond"), "lt", SSAVar("%arg1"), SSAVar("%extern")),
            "%c2cond": BoolCmp(SSAVar("%c2cond"), "lt", SSAVar("%arg1"), SSAVar("%b2")),
            "%b2": _felt_const("%b2", 3),
            "%arg1": "%next",
            "%next": _felt_binary("%next", "felt.add", "%arg1", "%c1"),
            "%c1": _felt_const("%c1", 1),
        }
        result = infer_iteration_sequence_from_expressions(var2expression, "%cond", {"%arg1": 0})
        assert result is None

    def test_ge_predicate_sequence_terminates_after_wrapping_past_zero(self):
        # Shares _resolve_comparison_recurrence with TestPrimeAwareSimulation's
        # test_ge_predicate_terminates_after_wrapping_past_zero -- confirms
        # the fix applies to the sequence variant too, not just the count.
        var2expression = {
            "%cond": BoolCmp(SSAVar("%cond"), "ge", SSAVar("%arg1"), SSAVar("%bound")),
            "%bound": _felt_const("%bound", 0),
            "%arg1": "%next",
            "%next": _felt_binary("%next", "felt.sub", "%arg1", "%c1"),
            "%c1": _felt_const("%c1", 1),
        }
        result = infer_iteration_sequence_from_expressions(
            var2expression, "%cond", {"%arg1": 2}, prime=7
        )
        assert result == [2, 1, 0]

    def test_raises_when_operand_not_boolcmp(self):
        var2expression = {
            "%cond": _bool_and("%cond", "%nested_and", "%c2cond"),
            "%nested_and": _bool_and("%nested_and", "%c1cond", "%c1cond"),
            "%c1cond": BoolCmp(SSAVar("%c1cond"), "lt", SSAVar("%arg1"), SSAVar("%b1")),
            "%b1": _felt_const("%b1", 5),
            "%c2cond": BoolCmp(SSAVar("%c2cond"), "lt", SSAVar("%arg1"), SSAVar("%b2")),
            "%b2": _felt_const("%b2", 3),
        }
        with pytest.raises(AssertionError):
            infer_iteration_sequence_from_expressions(var2expression, "%cond", {"%arg1": 0})


class TestAssignPodVarsTypeDriven:
    """
    translate_assignment_core_with_ctx's "Assign pod vars" branch must
    flatten a pod-typed assignment all the way to real leaf storage even
    when neither side is already a registered ctx.ssa2pod_var key --
    dispatch is driven by type_ itself (mirroring the !struct.type branch
    just above it in the same function), not by pre-existing registration.

    Mirrors the poseidon3_test_concrete.mlir shape that produced a broken
    .core file (llzk_cli: "Variable '...#1_@idx_0' not found"): a
    scf.if/else cascade re-assigns a pod one level at a time, and some
    branches mint a fresh pod-typed name (via this same branch's own
    recursive `dest` derivation) that is itself never pre-registered before
    being copied again one level up. See DECISIONS.md for why the fix
    dispatches on type_ rather than on registration.
    """

    def _ctx_with_ark_struct(self):
        ctx = TranslationContext()
        # A minimal stand-in for @Ark_0::@Ark_0's registered @compute
        # signature -- a single array-typed output "@out" (the real Ark_0
        # emits a 3-element felt array), matching the real shape's
        # !struct.type<@Ark_0::@Ark_0<[]>> @comp field.
        ctx.llzk_func2core["@Ark_0::@Ark_0::@compute"] = "Ark_0"
        ctx.core_func2args["Ark_0"] = (
            [], [("@out", Type("!array.type<3 x !felt.type<\"bn128\">>"))]
        )
        return ctx

    def _nested_pod_type(self):
        # Matches the real crashing shape exactly: @count (scalar),
        # @comp (a struct), @params (an empty pod -- contributes no leaves).
        return Type(
            "!pod.type<[@count: index, "
            "@comp: !struct.type<@Ark_0::@Ark_0<[]>>, "
            "@params: !pod.type<[]>]>"
        )

    def test_flattens_fully_even_when_neither_side_is_pre_registered(self):
        ctx = self._ctx_with_ark_struct()
        type_ = self._nested_pod_type()

        result = translate_assignment_core_with_ctx(
            SSAVar("%lhs"), SSAVar("%rhs"), type_, ctx
        )

        # The bug: a bare "array.copy %rhs %lhs" (or similar), referencing a
        # name that was never allocated as real storage anywhere. The fix:
        # a fully-flattened per-leaf copy, same convention as every other
        # already-correct call site in this codebase.
        assert result == "%lhs_@count = %rhs_@count\narray.copy %rhs_@comp_@out %lhs_@comp_@out"
        assert "array.copy %rhs %lhs" not in result

    def test_registers_rhs_and_the_nested_comp_pod_recursively(self):
        ctx = self._ctx_with_ark_struct()
        type_ = self._nested_pod_type()

        translate_assignment_core_with_ctx(SSAVar("%lhs"), SSAVar("%rhs"), type_, ctx)

        # rhs itself becomes a registered top-level pod...
        assert ctx.ssa2pod_var["%rhs"]["@count"][0] == "%rhs_@count"
        # ...and so does lhs, at every level this branch's own recursion
        # touches -- proving the fix is self-healing at each depth, not
        # just the first one.
        assert ctx.ssa2pod_var["%lhs"]["@count"][0] == "%lhs_@count"
        assert ctx.ssa2pod_var["%lhs"]["@comp"][0] == "%lhs_@comp"

    def test_pre_registered_rhs_still_takes_this_branch_unchanged(self):
        # No-regression check: when rhs IS already registered, behavior is
        # exactly as before this fix (the "if rhs.name not in ctx.ssa2pod_var"
        # guard is a no-op).
        ctx = self._ctx_with_ark_struct()
        ctx.ssa2pod_var["%rhs"] = {
            "@count": ("%rhs_@count", Type("index")),
        }
        type_ = Type("!pod.type<[@count: index]>")

        result = translate_assignment_core_with_ctx(
            SSAVar("%lhs"), SSAVar("%rhs"), type_, ctx
        )

        assert result == "%lhs_@count = %rhs_@count"
