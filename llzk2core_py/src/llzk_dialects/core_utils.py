"""
Module for useful methods applies to the classes in core.py
"""
from typing import List, Set, Dict, Union, Optional, Callable
from llzk_dialects.core import SSAVar, TranslationContext, Type, Operation
from llzk_dialects.utils import translate_assignment_core
from llzk_dialects.bool import BoolCmp
from llzk_dialects.felt import FeltConst, FeltBinary


def translate_assignment_core_with_ctx(lhs: SSAVar, rhs: SSAVar, type_: Type, ctx: TranslationContext) -> str:
    """
    Generates a str with the translation of an assignment in core. Moreover,
    it updates the context if rhs corresponds to a variable that evaluates to a constant
    """
    is_ff = "array" not in type_.name

    if is_ff:
        # Only check constants in case it is a ff
        const = ctx.var2const.get(rhs.name)
        if const is not None:
            ctx.var2const[lhs.name] = const

    return translate_assignment_core(lhs.to_core(), rhs.to_core(), is_ff)


def infer_n_repetitions_from_expressions(ground_variables: Set[str],
                                         var2expression: Dict[str, Union[str, Operation]],
                                         condition_var_core: str) -> int:
    """
    Using the information retrieved from all involved expressions in the condition
    (ground_variables, var2expression and condition_var) and the initial assignments
    (initial_args2const), detects how many iterations are performed
    until the condition is reached
    """
    if len(ground_variables) > 1:
        raise NotImplementedError("While condition relies on two expressions to be computed")
    assert len(ground_variables) == 1, "The while must depend on a linear expression"
    ground_var = [var for var in ground_variables][0]

    initial_comparison = var2expression[condition_var_core]
    assert isinstance(initial_comparison, BoolCmp), f"For now, only BoolCmp whiles are handled: {initial_comparison}"

    # For now, we only handle lt, le, gt and ge
    # TODO: cover more cases if needed

    # Reverse the arguments
    if initial_comparison.predicate == "gt":
        lhs, rhs = initial_comparison.rhs, initial_comparison.lhs
        op = "lt"
    elif initial_comparison.predicate == "ge":
        lhs, rhs = initial_comparison.rhs, initial_comparison.lhs
        op = "le"
    else:
        lhs, rhs = initial_comparison.lhs, initial_comparison.rhs
        op = initial_comparison.predicate

    if isinstance(var2expression[lhs.name], FeltConst):
        variable = rhs
        initial_value = var2expression[lhs.name].constant

        if op == "lt":
            compare_func = lambda x: var2expression[lhs.name].constant < x
        else:
            assert op == "le", "Only inequalities are implemented"
            compare_func = lambda x: var2expression[lhs.name].constant <= x

    else:
        assert isinstance(var2expression[rhs.name], FeltConst), \
            "One of the variables must be constant"
        variable = lhs
        initial_value = var2expression[rhs.name].constant

        if op == "lt":
            compare_func = lambda x: x < var2expression[rhs.name].constant
        else:
            assert op == "le", "Only inequalities are implemented"
            compare_func = lambda x: x <= var2expression[rhs.name].constant

    # We can deduce the update function and the original variable
    update_func = construct_function_from_expressions(variable, var2expression, set())
    return count_iterations(initial_value, compare_func, update_func)


def construct_function_from_expressions(current_expr: SSAVar,
                                        var2expression: Dict[str, Union[str, Operation]],
                                        traversed: Set[str]) -> Callable:
    """
    Construct a Python callable f(x) -> int that computes current_expr
    in terms of ground_var.

    var2expression values are either:
      - an Operation: call its to_function(), recurse on operands
      - a str: the name of another SSA variable with the same value (alias)
    """
    # Ignore the case where an element has already been traversed (base case)
    if current_expr.name in traversed:
        return lambda x: x

    traversed.add(current_expr.name)
    expression = var2expression[current_expr.name]

    if isinstance(expression, str):
        return construct_function_from_expressions(
            SSAVar(expression), var2expression, traversed
        )

    raw_fn = expression.to_function()
    operand_fns = [
        construct_function_from_expressions(op, var2expression, traversed)
        for op in expression.operands
    ]

    # Use default-arg capture to avoid late-binding closure issues
    if not operand_fns:
        return lambda x, _fn=raw_fn: _fn()
    return lambda x, _fn=raw_fn, _fns=operand_fns: _fn(*[f(x) for f in _fns])


def count_iterations(initial_value, condition_fn, update_fn):
    value = initial_value
    count = 0
    while condition_fn(value):
        value = update_fn(value)
        count += 1
    return count
