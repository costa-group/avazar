"""
Module for useful methods applies to the classes in core.py
"""
import re
from typing import List, Set, Dict, Union, Optional, Callable, Tuple
from llzk_dialects.core import SSAVar, TranslationContext, Type, Operation
from llzk_dialects.utils import translate_assignment_core
from llzk_dialects.bool import BoolCmp
from llzk_dialects.felt import FeltConst, FeltBinary


def struct_type_name(type_str: str) -> Optional[str]:
    """
    Extracts the template::struct name from a struct type string. Also works if "!struct.type<*>" does not appear

    Example: '!struct.type<@Num2Bits_2::@Num2Bits_2<[]>>' -> '@Num2Bits_2::@Num2Bits_2',
                           '@Num2Bits_2::@Num2Bits_2<[]>'  -> '@Num2Bits_2::@Num2Bits_2'
    """
    m = re.search(r'!struct\.type<([^><]+)', type_str)
    if m is not None:
        return m.group(1).strip()

    m = re.search(r'([^><]+)', type_str)
    # Ignore !felt.type inside the string, as otherwise it matches every possible operand
    return m.group(1).strip() if m is not None and "!felt.type" not in type_str else None


def signature_args(args: List[Tuple[str, Type]]) -> str:
    """
    Given a list of args and their types, returns a string for declaring
    the signature of a function in CORE, with the format: "arg1: type1, arg2: type2, ..."
    """
    return', '.join(f"{arg}: {type_.to_core()}" for arg, type_ in args)


def signature_args_with_prefix(args: List[Tuple[str, Type]], prefix: str) -> str:
    """
    Given a list of args and their types, returns a string for declaring
    the signature of a function in CORE, with the format: "arg1*: type1, arg2*: type2, ..."

    argi* is determined by argi and adding the corresponding prefix from the context

    """
    return', '.join(f"{prefix}.{arg[1:]}: {type_.to_core()}" for arg, type_ in args)


def invocation_args(args: List[Tuple[str, Type]]) -> str:
    """
    Given a list of args and their types, returns a string for invoking
    a function in CORE, with the format: "arg1, arg2, ..."
    """
    return ', '.join(arg for arg, _ in args)


def translate_assignment_core_with_ctx(lhs: SSAVar, rhs: SSAVar, type_: Type, ctx: TranslationContext) -> str:
    """
    Generates a str with the translation of an assignment in core. Moreover,
    it updates the context if rhs corresponds to a variable that evaluates to a constant
    """

    if "!struct" in type_.name:
        llzk_func = f"{struct_type_name(type_.name)}::@compute"
        core_func = ctx.llzk_func2core[llzk_func]
        _, output_args = ctx.core_func2args[core_func]

        # Convert recursively the functions
        return '\n'.join(translate_assignment_core_with_ctx(SSAVar(lhs.name + "_" + out_var),
                                                            SSAVar(rhs.name + "_" + out_var),
                                                            out_type, ctx)
                         for out_var, out_type in output_args)

    is_ff = "array" not in type_.name and "!struct"

    if is_ff:
        # Only check constants in case it is a ff
        const = ctx.var2const.get(rhs.name)
        if const is not None:
            ctx.var2const[lhs.name] = const

    # Assign pod vars
    elif rhs.name in ctx.ssa2pod_var:
        pod_vars = ctx.ssa2pod_var[rhs.name]
        new_pod_vars = {}
        assignments = []
        for record, (initial_value, type_) in pod_vars.items():

            # Add a new assignment
            assignments.append(translate_assignment_core_with_ctx(
                SSAVar(f"{lhs.name}_{record}"),
                SSAVar(initial_value),
                type_,
                ctx,
            ))

            new_pod_vars[record] = (f"{lhs.name}_{record}", type_)

        ctx.ssa2pod_var[lhs.name] = new_pod_vars

        return '\n'.join(assignments)

    return translate_assignment_core(lhs.to_core(), rhs.to_core(), is_ff)


def infer_n_repetitions_from_expressions(ground_variables: Set[str],
                                         var2expression: Dict[str, Union[str, Operation]],
                                         condition_var_core: str,
                                         initial_values: Dict[str, int]) -> int:
    """
    Using the information retrieved from all involved expressions in the condition
    (ground_variables, var2expression and condition_var) and the initial assignments
    (initial_args2const), detects how many iterations are performed
    until the condition is reached
    """
    if len(ground_variables) > 1:
        raise NotImplementedError("While condition relies on two expressions to be computed")

    assert len(ground_variables) <= 1, "The while must depend on a linear expression"

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
        initial_value = initial_values[lhs.name]

        if op == "lt":
            compare_func = lambda x: var2expression[lhs.name].constant < x
        else:
            assert op == "le", "Only inequalities are implemented"
            compare_func = lambda x: var2expression[lhs.name].constant <= x

    else:
        assert isinstance(var2expression[rhs.name], FeltConst), \
            "One of the variables must be constant"
        variable = lhs
        initial_value = initial_values[lhs.name]

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
