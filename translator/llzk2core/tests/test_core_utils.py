import pytest
from llzk_dialects.core_utils import (
    infer_n_repetitions_from_expressions,
    construct_function_from_expressions,
    count_iterations,
    SymbolicSteps,
    _collect_setup_ops,
    _collect_free_var_names,
    _detect_affine_step,
)
from llzk_dialects.core import SSAVar
from llzk_dialects.felt import FeltConst, FeltBinary
from llzk_dialects.bool import BoolCmp


def _felt_const(name, value):
    return FeltConst(SSAVar(name), value)


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
