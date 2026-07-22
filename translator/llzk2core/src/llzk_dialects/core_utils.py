"""
Module for useful methods applies to the classes in core.py
"""
import re
from dataclasses import dataclass
from typing import List, Set, Dict, Union, Optional, Callable, Tuple
from llzk_dialects.core import SSAVar, TranslationContext, Type, Operation
from llzk_dialects.utils import translate_assignment_core, struct_type_name, is_array_type
from llzk_dialects.bool import BoolCmp, BoolBinary
from llzk_dialects.felt import FeltConst, FeltBinary


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
    # Resolve any semantic alias for rhs (e.g. "%14_@out_last" -> "last1.out_last")
    alias = ctx.ssa_to_name.get(rhs.name)
    if alias is not None:
        rhs = SSAVar(alias)

    # Anchored to the outermost type, not a plain substring check: a pod that
    # merely CONTAINS a struct-typed field somewhere inside (e.g.
    # "!pod.type<[@comp: !struct.type<...>, ...]>") is not itself a struct
    # result and must not be treated as one -- that would silently emit a
    # copy of the wrong (Ark_0-shaped) fields and skip pod registration
    # entirely for the actual (pod-shaped) value.
    if type_.name.strip().startswith("!struct.type"):
        llzk_func = f"{struct_type_name(type_.name)}::@compute"
        core_func = ctx.llzk_func2core[llzk_func]
        _, output_args = ctx.core_func2args[core_func]

        # Convert recursively the functions
        return '\n'.join(translate_assignment_core_with_ctx(SSAVar(lhs.name + "_" + out_var),
                                                            SSAVar(rhs.name + "_" + out_var),
                                                            out_type, ctx)
                         for out_var, out_type in output_args)

    is_ff = "array" not in type_.name and "!pod.type" not in type_.name

    if is_ff:
        # Only check constants in case it is a ff
        const = ctx.var2const.get(rhs.name)
        if const is not None:
            ctx.var2const[lhs.name] = const

    # Array of pod/struct (structure-of-arrays): copy each flattened per-field
    # array independently, since there is no single real CORE array to
    # array.copy. A leaf that is itself array-typed needs a full-array copy
    # too (still a single array.copy — its size already accounts for the
    # outer array's element count, from ArrayNew's own flattening).
    #
    # is_array_type (anchored to the start of the string) is required here,
    # not a plain "array" substring check: a PLAIN pod whose OWN fields
    # happen to be arrays (e.g. !pod.type<[@c: !array.type<...>, ...]>) would
    # otherwise be mistaken for an array-of-pod.
    elif is_array_type(type_.name) and ("!pod.type" in type_.name or "!struct.type" in type_.name):
        from llzk_dialects.array import _flatten_container_fields, _container_field_var

        assignments = []
        for field_path, _ in _flatten_container_fields(type_.name, ctx):
            src = _container_field_var(rhs.name, field_path)
            dst = _container_field_var(lhs.name, field_path)
            assignments.append(f"array.copy {src} {dst}")
        return '\n'.join(assignments)

    # Assign pod vars
    elif rhs.name in ctx.ssa2pod_var:
        pod_vars = ctx.ssa2pod_var[rhs.name]
        new_pod_vars = {}
        assignments = []
        for record, (initial_value, type_) in pod_vars.items():
            if not initial_value.startswith("%"):
                # Semantic name (e.g. "mux.c"). Propagate directly without
                # creating an intermediate copy variable.
                new_pod_vars[record] = (initial_value, type_)
            else:
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


@dataclass
class SymbolicSteps:
    """
    A while-loop iteration count that couldn't be reduced to a concrete
    Python int at translation time -- its condition's bound depends on a
    variable that isn't defined anywhere inside the while itself (e.g. an
    enclosing function's own parameter) and whose value isn't known here --
    but that can still be expressed as a Core arithmetic formula, to be
    assigned to a fresh variable and used directly as `repeat`'s operand.

    setup_ops must be translated once, in order, before the repeat statement,
    to compute bound_var's value; bound_var.to_core() is then the bound.
    """
    setup_ops: List[Operation]
    bound_var: SSAVar
    initial_value: int
    op: str  # "lt" or "le"
    variable_is_lhs: bool


def _collect_setup_ops(var: SSAVar,
                       var2expression: Dict[str, Union[str, Operation]],
                       seen: Set[str]) -> List[Operation]:
    """
    Post-order traversal collecting the operations (in dependency order) that
    must be translated once, before a loop starts, to compute `var`'s value --
    used to precompute a while's bound expression when it can't be reduced to
    a concrete Python int. Mirrors construct_function_from_expressions's
    recursion, but collects Operations instead of building a callable. A name
    with no var2expression entry (an external free variable, e.g. an
    enclosing function's own parameter) needs no setup: it's already a valid
    Core identifier.
    """
    if var.name in seen or var.name not in var2expression:
        return []

    seen.add(var.name)
    expression = var2expression[var.name]

    if isinstance(expression, str):
        return _collect_setup_ops(SSAVar(expression), var2expression, seen)

    ops = []
    for operand in expression.operands:
        ops.extend(_collect_setup_ops(operand, var2expression, seen))
    ops.append(expression)
    return ops


def _detect_affine_step(update_func: Callable) -> Optional[int]:
    """
    Probes update_func at two sample points to check whether it's an affine
    x -> x + step recurrence, returning the step if so, None otherwise.
    """
    step = update_func(10) - 10
    if update_func(1000) - 1000 != step:
        return None
    return step


def _collect_free_var_names(var: SSAVar,
                            var2expression: Dict[str, Union[str, Operation]],
                            seen: Set[str]) -> Set[str]:
    """
    Walks var's expression tree (following string aliases/operation operands,
    same recursion shape as construct_function_from_expressions) and returns
    the names with no var2expression entry at all -- external free variables
    referenced by the expression but not defined anywhere inside the while
    itself (e.g. an enclosing function's own parameter).
    """
    if var.name in seen:
        return set()
    seen.add(var.name)

    if var.name not in var2expression:
        return {var.name}

    expression = var2expression[var.name]
    if isinstance(expression, str):
        return _collect_free_var_names(SSAVar(expression), var2expression, seen)

    free = set()
    for operand in expression.operands:
        free.update(_collect_free_var_names(operand, var2expression, seen))
    return free


def infer_n_repetitions_from_expressions(var2expression: Dict[str, Union[str, Operation]],
                                         condition_var_core: str,
                                         initial_values: Dict[str, int],
                                         var2const: Optional[Dict[str, int]] = None
                                         ) -> Union[int, SymbolicSteps]:
    """
    Using the information retrieved from all involved expressions in the condition
    (var2expression and condition_var) and the initial assignments (initial_values),
    detects how many iterations are performed until the condition is reached.

    Handles a condition that is a single BoolCmp directly (see
    _infer_from_comparison), or a bool.and of two BoolCmp sub-conditions: each
    half is inferred independently and the smaller of the two counts is
    returned, since the loop stops as soon as either half first goes false
    (correct regardless of whether the two halves reference the same or
    different loop-carried variables -- each count already fully accounts for
    its own condition's failure point in isolation).
    """
    var2const = var2const or {}

    condition = var2expression[condition_var_core]

    if isinstance(condition, BoolCmp):
        return _infer_from_comparison(condition, var2expression, initial_values, var2const)

    if isinstance(condition, BoolBinary) and condition.op == "bool.and":
        lhs_condition = var2expression[condition.lhs.name]
        rhs_condition = var2expression[condition.rhs.name]
        assert isinstance(lhs_condition, BoolCmp) and isinstance(rhs_condition, BoolCmp), \
            f"For now, a bool.and while condition must combine two BoolCmp: {condition}"

        lhs_steps = _infer_from_comparison(lhs_condition, var2expression, initial_values, var2const)
        rhs_steps = _infer_from_comparison(rhs_condition, var2expression, initial_values, var2const)
        return _combine_min_steps(lhs_steps, rhs_steps)

    raise NotImplementedError(
        f"For now, only BoolCmp or bool.and-of-BoolCmp whiles are handled: {condition}"
    )


def _combine_min_steps(a: Union[int, SymbolicSteps], b: Union[int, SymbolicSteps]) -> Union[int, SymbolicSteps]:
    """
    Combines two independently-inferred while-condition step counts (from the
    two halves of a bool.and) by taking the smaller -- the loop stops as soon
    as either half first goes false.
    """
    if isinstance(a, int) and isinstance(b, int):
        return min(a, b)

    raise NotImplementedError(
        "Combining a bool.and condition where either half's iteration count is "
        "symbolic (not a concrete int) is not supported -- would require emitting "
        "a Core-level conditional to pick the smaller at runtime"
    )


def _infer_from_comparison(initial_comparison: BoolCmp,
                           var2expression: Dict[str, Union[str, Operation]],
                           initial_values: Dict[str, int],
                           var2const: Dict[str, int]) -> Union[int, SymbolicSteps]:
    """
    Infers the number of iterations a while's exit condition allows, given a
    single BoolCmp (one half of a bool.and, or the whole condition).

    The condition's bound may reference, besides the loop-carried variable
    itself, other free variables not defined anywhere inside the while (e.g.
    an enclosing function's own parameter). Those are resolved via var2const
    when known (folded in as constants, same as a literal felt.const); when
    they aren't, the iteration count is instead derived as a SymbolicSteps
    formula, provided the loop variable's own recurrence is a simple +-1
    step.

    The loop-carried variable is identified directly from the condition's own
    operands, via initial_values membership (only ever populated for the
    while's own declared loop-carried arguments) -- not from the leftover set
    SCFWhile._extract_step's backward walk produces, which is unreliable for
    this: when the loop variable's own recurrence collapses entirely to
    constants (e.g. it's unconditionally reset to a literal each iteration,
    rather than incremented), that walk consumes it completely and it never
    survives as a leftover, even though it's still a bona fide loop-carried
    variable.
    """
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

    assert op in ("lt", "le"), "Only inequalities are implemented"

    lhs_is_variable = lhs.name in initial_values
    rhs_is_variable = rhs.name in initial_values

    if lhs_is_variable and rhs_is_variable:
        raise NotImplementedError(
            f"While condition compares two loop-carried variables directly "
            f"('{lhs.name}', '{rhs.name}') -- not supported"
        )
    elif lhs_is_variable:
        variable, bound = lhs, rhs
        variable_is_lhs = True
    elif rhs_is_variable:
        variable, bound = rhs, lhs
        variable_is_lhs = False
    else:
        raise NotImplementedError(
            f"Could not identify the loop-carried variable in the while condition: "
            f"neither '{lhs.name}' nor '{rhs.name}' has a known initial value"
        )

    initial_value = initial_values[variable.name]
    update_func = construct_function_from_expressions(variable, var2expression, set())

    # Resolve any free variable the bound references but that isn't defined
    # anywhere inside the while itself (e.g. an enclosing function's own
    # parameter) via var2const, folding it in as a constant leaf, same as a
    # literal felt.const.
    unresolved_free_vars = set()
    for name in _collect_free_var_names(bound, var2expression, set()):
        if name in var2const:
            var2expression[name] = FeltConst(SSAVar(name), var2const[name])
        else:
            unresolved_free_vars.add(name)

    if not unresolved_free_vars:
        # Every value the bound depends on is now known (either an original
        # literal or a free variable just resolved via var2const above), so
        # it can be evaluated to a concrete int, same as a bare constant.
        bound_func = construct_function_from_expressions(bound, var2expression, set())
        bound_value = bound_func(0)

        if variable_is_lhs:
            compare_func = (lambda x: x < bound_value) if op == "lt" else (lambda x: x <= bound_value)
        else:
            compare_func = (lambda x: bound_value < x) if op == "lt" else (lambda x: bound_value <= x)

        return count_iterations(initial_value, compare_func, update_func)

    # The bound depends on a value that isn't known here (e.g. an enclosing
    # function's own parameter). Fall back to a symbolic Core expression for
    # the step count -- only supported when the loop variable's own update is
    # a simple +-1 per-iteration increment, in the direction required for the
    # loop to actually terminate.
    step = _detect_affine_step(update_func)
    if step is None:
        raise NotImplementedError(
            f"While condition depends on unresolved variable(s) {unresolved_free_vars}, "
            "and the loop variable's update is not a simple constant increment -- "
            "cannot infer a symbolic step count"
        )

    if (variable_is_lhs and step != 1) or (not variable_is_lhs and step != -1):
        raise NotImplementedError(
            f"While condition depends on unresolved variable(s) {unresolved_free_vars} "
            f"with a step of {step} in the {'lhs' if variable_is_lhs else 'rhs'} position -- "
            "only a +-1 step is supported for symbolic step-count inference"
        )

    setup_ops = _collect_setup_ops(bound, var2expression, set())
    return SymbolicSteps(setup_ops, bound, initial_value, op, variable_is_lhs)


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
