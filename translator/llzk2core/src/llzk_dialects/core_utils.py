"""
Module for useful methods applies to the classes in core.py
"""
import re
from contextlib import contextmanager
from dataclasses import dataclass
from typing import List, Set, Dict, Union, Optional, Callable, Tuple, NoReturn
from llzk_dialects.core import SSAVar, TranslationContext, Type, Operation
from llzk_dialects.utils import translate_assignment_core, struct_type_name, is_array_type
from llzk_dialects.bool import BoolCmp, BoolBinary
from llzk_dialects.felt import FeltConst, FeltBinary


# Prime for each finite field llzk2core/circom-llzk/complete_avazar.py can
# target, keyed by the same --prime name complete_avazar.py itself accepts.
# Deliberately duplicated from complete_avazar.py's own PRIMES dict (not
# imported across the repo boundary -- llzk2core is meant to stay a
# self-contained subproject, and complete_avazar.py already only imports
# *from* llzk2core, never the reverse) -- keep the two in sync by hand if
# either changes.
FIELD_PRIMES: Dict[str, int] = {
    "goldilocks": 18446744069414584321,
    "secq256r1": 115792089210356248762697446949407573529996955224253574108868205240008320037127,
    "pallas": 28948022309329048855892746252171976963363056481941560715954679059200803120067,
    "vesta": 28948022309329048855892746252171976963363056481941600130006322964104920678209,
    "bn128": 21888242871839275222246405745257275088548364400416034343698204186575808495617,
    "grumpkin": 21888242871839275222246405745257275088696311157297823662689037894645226208583,
    "bls12377": 25866442601296909401065273369489353353639351283510007695335291307297420126659,
    "bls12381": 52435875175126190479447740508185965837690552500527637822603658699938581184513,
}

# Generous upper bound on the number of iterations a while-loop trip-count
# simulation (count_iterations/iterate_values) will run before giving up --
# far above any real circuit loop, just enough to turn a genuinely
# non-terminating recurrence (a translator bug, or a shape this codebase
# doesn't understand yet) into a fast, clear failure instead of an
# indefinite hang.
_MAX_SIMULATED_ITERATIONS = 1_000_000


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

    # Assign pod vars. Type-driven (anchored on type_ itself), not merely
    # registration-driven: rhs.name may be a perfectly good pod-typed value
    # that simply hasn't been registered in ctx.ssa2pod_var yet -- e.g. a
    # fresh name minted one level up by this very branch's own recursive
    # call (see the `dest` derivation below), which only registers itself
    # AFTER its own recursive translate_assignment_core_with_ctx call
    # returns. Without this, a pod value born mid-recursion that isn't
    # already a registered key would silently fall through to the generic
    # scalar/array-copy fallback at the bottom of this function instead of
    # flattening into its fields -- producing a copy of a name nothing ever
    # allocated as real storage. See DECISIONS.md for why this dispatches
    # on type_ rather than on registration, mirroring the !struct.type
    # branch above.
    elif rhs.name in ctx.ssa2pod_var or type_.name.strip().startswith("!pod.type"):
        if rhs.name not in ctx.ssa2pod_var:
            from llzk_dialects.pod import _register_pod_top_level, _parse_pod_fields
            _register_pod_top_level(ctx, rhs.name, _parse_pod_fields(type_.name))
        pod_vars = ctx.ssa2pod_var[rhs.name]

        # lhs may be a member-backed pod (e.g. an scf.while block arg backing
        # struct member "ark") that has never been registered as its own key
        # yet -- this is its very first assignment (the while's own initial
        # value, or a pod.new record with an explicit initial value). Without
        # this, the loop below would only ever see rhs's shape and derive
        # throwaway "%lhs_record" names, discarding lhs's real (semantic)
        # destination before it's ever created. Reuses rhs's own field types
        # rather than re-parsing type_.name.
        if lhs.name not in ctx.ssa2pod_var and ctx.input_pod_to_member.get(lhs.name):
            from llzk_dialects.pod import _register_pod_top_level
            _register_pod_top_level(
                ctx, lhs.name,
                {record: t for record, (_, t) in pod_vars.items()},
            )

        # Anchored on lhs's OWN pre-existing registration (its real
        # destination), not merely on whether rhs's field happens to be
        # semantic -- otherwise a member-backed lhs with a real semantic
        # destination (e.g. "ark.idx_7") gets silently clobbered by a fresh
        # "%lhs_record" derived name the moment rhs's own value isn't itself
        # semantic (e.g. it traces back to a raw llzk.nondet result).
        existing_lhs_vars = ctx.ssa2pod_var.get(lhs.name, {})
        new_pod_vars = {}
        assignments = []
        for record, (initial_value, type_) in pod_vars.items():
            existing_dest, _ = existing_lhs_vars.get(record, (None, None))
            has_own_dest = existing_dest is not None and not existing_dest.startswith("%")

            if has_own_dest:
                # lhs already has its own semantic destination -- preserve it.
                dest = existing_dest
            elif not initial_value.startswith("%"):
                # Semantic name (e.g. "mux.c"). Propagate directly without
                # creating an intermediate copy variable.
                dest = None
            else:
                dest = f"{lhs.name}_{record}"

            if dest is None:
                new_pod_vars[record] = (initial_value, type_)
            else:
                if dest != initial_value:
                    assignments.append(translate_assignment_core_with_ctx(
                        SSAVar(dest),
                        SSAVar(initial_value),
                        type_,
                        ctx,
                    ))
                new_pod_vars[record] = (dest, type_)

        ctx.ssa2pod_var[lhs.name] = new_pod_vars

        return '\n'.join(a for a in assignments if a)

    return translate_assignment_core(lhs.to_core(), rhs.to_core(), is_ff)


@contextmanager
def scoped_branch_registrations(ctx: TranslationContext, results: List[SSAVar]):
    """
    Scope ctx.ssa_to_name / ctx.ssa2pod_var / ctx.var2const to one mutually-
    exclusive branch of an scf.if (or one scf.execute_region's single body),
    so a branch-local temporary registered while translating this block does
    not leak into a *sibling* branch's translation, nor survive past the
    block once it closes.

    Rationale: valid SSA scoping guarantees a value defined inside one
    branch is never referenced outside it (or by a sibling branch) --
    except for the block's own *declared* results, which are exactly what a
    trailing scf.yield writes into `results`' own component names. Core, on
    the other hand, always emits BOTH of an if's branches as real runtime
    code (SCFIf.to_core never resolves the condition statically), and
    ctx.ssa_to_name/ssa2pod_var/var2const are flat, whole-translation dicts
    with no per-branch scoping of their own -- so a raw LLZK SSA name
    legitimately reused across two mutually-exclusive branches (valid under
    SSA: only one branch executes at runtime) would otherwise silently
    clobber whichever branch's own registration was translated first, by
    the time either that branch is revisited or any code after the
    if/execute_region reads the name back.

    On exit, every key is reverted to whatever it was before this block
    ran, EXCEPT one of `results`' own component names
    (SSAVar.to_core_component, one per n_components), which instead keeps
    its current (just-computed, post-block) value -- that's precisely this
    block's own declared, escaping registration.

    Known limitation: a key that already existed before this block AND is
    directly mutated by some op inside the block (not via one of `results`'
    component names) is reverted to its pre-block value once this block
    exits, even though the mutation wasn't a "new" branch-local temporary.
    Every current writer of these three dicts derives new entries either
    from a fresh (branch-local) SSA name, or, for pod.write into an
    already-registered pod field, from an `lhs.name`-derived key whose
    registered *shape* is independent of which branch performed the write
    -- so this never actually diverges from "let the mutation persist" in
    practice today. If a future op ever needs to mutate a pre-existing key
    with a value that genuinely differs by branch and must survive past
    the if, add its own key to an explicit allow-list here (or pass it in
    via `results`).
    """
    ssa_to_name_before = dict(ctx.ssa_to_name)
    ssa2pod_var_before = dict(ctx.ssa2pod_var)
    var2const_before = dict(ctx.var2const)
    try:
        yield
    finally:
        result_keys = [r.to_core_component(i) for r in results for i in range(r.n_components)]
        for key in result_keys:
            if key in ctx.ssa_to_name:
                ssa_to_name_before[key] = ctx.ssa_to_name[key]
            if key in ctx.ssa2pod_var:
                ssa2pod_var_before[key] = ctx.ssa2pod_var[key]
            if key in ctx.var2const:
                var2const_before[key] = ctx.var2const[key]
        ctx.ssa_to_name.clear()
        ctx.ssa_to_name.update(ssa_to_name_before)
        ctx.ssa2pod_var.clear()
        ctx.ssa2pod_var.update(ssa2pod_var_before)
        ctx.var2const.clear()
        ctx.var2const.update(var2const_before)


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
                                         var2const: Optional[Dict[str, int]] = None,
                                         prime: int = FIELD_PRIMES["goldilocks"]
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

    `prime` is the finite field the while's own arithmetic is defined over --
    threaded down into construct_function_from_expressions so the simulated
    loop-carried variable wraps the same way the real field does (e.g. a
    decrementing counter that goes below 0 becomes prime-1, not a raw
    negative Python int) -- defaults to goldilocks, matching every existing
    example.
    """
    var2const = var2const or {}

    condition = var2expression[condition_var_core]

    if isinstance(condition, BoolCmp):
        return _infer_from_comparison(condition, var2expression, initial_values, var2const, prime)

    if isinstance(condition, BoolBinary) and condition.op == "bool.and":
        lhs_condition = var2expression[condition.lhs.name]
        rhs_condition = var2expression[condition.rhs.name]
        assert isinstance(lhs_condition, BoolCmp) and isinstance(rhs_condition, BoolCmp), \
            f"For now, a bool.and while condition must combine two BoolCmp: {condition}"

        lhs_steps = _infer_from_comparison(lhs_condition, var2expression, initial_values, var2const, prime)
        rhs_steps = _infer_from_comparison(rhs_condition, var2expression, initial_values, var2const, prime)
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


def infer_iteration_sequence_from_expressions(var2expression: Dict[str, Union[str, Operation]],
                                              condition_var_core: str,
                                              initial_values: Dict[str, int],
                                              var2const: Optional[Dict[str, int]] = None,
                                              prime: int = FIELD_PRIMES["goldilocks"]
                                              ) -> Optional[List[int]]:
    """
    Like infer_n_repetitions_from_expressions, but returns the actual
    sequence of values the loop-carried variable visits (one per iteration,
    in order) instead of just the count -- used to attribute each concrete
    call inside an array-of-components population loop to the real array
    index it was called with, rather than assuming sequential 0,1,2,...
    visitation (see struct.py's array-component index-sequence pre-pass).

    Returns None whenever the count itself isn't a concrete int (a
    SymbolicSteps-shaped bound, or -- for a bool.and -- either half not
    reducing to a concrete sequence): there's no way to list values for an
    iteration count only known as a Core-level formula. See
    infer_n_repetitions_from_expressions for `prime`.
    """
    var2const = var2const or {}

    condition = var2expression[condition_var_core]

    if isinstance(condition, BoolCmp):
        return _infer_sequence_from_comparison(condition, var2expression, initial_values, var2const, prime)

    if isinstance(condition, BoolBinary) and condition.op == "bool.and":
        lhs_condition = var2expression[condition.lhs.name]
        rhs_condition = var2expression[condition.rhs.name]
        assert isinstance(lhs_condition, BoolCmp) and isinstance(rhs_condition, BoolCmp), \
            f"For now, a bool.and while condition must combine two BoolCmp: {condition}"

        lhs_seq = _infer_sequence_from_comparison(lhs_condition, var2expression, initial_values, var2const, prime)
        rhs_seq = _infer_sequence_from_comparison(rhs_condition, var2expression, initial_values, var2const, prime)
        if lhs_seq is None or rhs_seq is None:
            return None
        # The loop stops as soon as either half first goes false -- the
        # shorter sequence is the one that actually happened, same
        # reasoning as _combine_min_steps.
        return lhs_seq if len(lhs_seq) <= len(rhs_seq) else rhs_seq

    raise NotImplementedError(
        f"For now, only BoolCmp or bool.and-of-BoolCmp whiles are handled: {condition}"
    )


@dataclass
class _ResolvedRecurrence:
    """
    A while condition's loop-carried variable fully resolved to a concrete
    initial value, per-iteration update function, and continuation
    predicate -- everything needed to either count iterations
    (count_iterations) or list the actual values visited (iterate_values).
    Shared by _infer_from_comparison and _infer_sequence_from_comparison so
    the two can never silently drift apart.
    """
    initial_value: int
    compare_func: Callable[[int], bool]
    update_func: Callable[[int], int]


def _resolve_comparison_recurrence(initial_comparison: BoolCmp,
                                   var2expression: Dict[str, Union[str, Operation]],
                                   initial_values: Dict[str, int],
                                   var2const: Dict[str, int],
                                   prime: int = FIELD_PRIMES["goldilocks"]
                                   ) -> Union[_ResolvedRecurrence, SymbolicSteps]:
    """
    Resolves a single BoolCmp while condition (one half of a bool.and, or the
    whole condition) to either a _ResolvedRecurrence (initial value, update
    function, continuation predicate all concrete) or a SymbolicSteps formula
    (the bound depends on an unresolved free variable, but the loop
    variable's own recurrence is a simple +-1 step). Shared resolution logic
    for both "how many iterations" (_infer_from_comparison) and "what values
    are actually visited" (_infer_sequence_from_comparison) -- see
    _ResolvedRecurrence.

    The condition's bound may reference, besides the loop-carried variable
    itself, other free variables not defined anywhere inside the while (e.g.
    an enclosing function's own parameter). Those are resolved via var2const
    when known (folded in as constants, same as a literal felt.const); when
    they aren't, a SymbolicSteps formula is returned instead, provided the
    loop variable's own recurrence is a simple +-1 step.

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
    # lt/le/gt/ge (inequalities) and eq/ne (equality checks) are handled.
    # eq/ne are symmetric -- no lhs/rhs swap needed, unlike gt/ge normalizing
    # to lt/le -- and only supported here in the concrete-bound branch below
    # (SymbolicSteps stays lt/le-only: no known example needs a symbolic
    # eq/ne formula, and an eq/ne loop's termination isn't a monotonic bound
    # crossing the way lt/le/gt/ge's is).

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

    assert op in ("lt", "le", "eq", "ne"), \
        f"Only inequalities and equality checks are implemented. Operation: {op}"

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
    update_func = construct_function_from_expressions(variable, var2expression, set(), prime)

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
        bound_func = construct_function_from_expressions(bound, var2expression, set(), prime)
        bound_value = bound_func(0)

        if op in ("eq", "ne"):
            # Symmetric: which side is "the variable" doesn't affect the
            # comparison itself, only how it was identified above.
            compare_func = (lambda x: x == bound_value) if op == "eq" else (lambda x: x != bound_value)
        elif variable_is_lhs:
            compare_func = (lambda x: x < bound_value) if op == "lt" else (lambda x: x <= bound_value)
        else:
            compare_func = (lambda x: bound_value < x) if op == "lt" else (lambda x: bound_value <= x)

        return _ResolvedRecurrence(initial_value, compare_func, update_func)

    if op in ("eq", "ne"):
        raise NotImplementedError(
            f"While condition depends on unresolved variable(s) {unresolved_free_vars} "
            f"with an '{op}' predicate -- only a concrete (fully-resolved) bound is "
            "supported for eq/ne; no known example needs a symbolic eq/ne formula"
        )

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


def _infer_from_comparison(initial_comparison: BoolCmp,
                           var2expression: Dict[str, Union[str, Operation]],
                           initial_values: Dict[str, int],
                           var2const: Dict[str, int],
                           prime: int = FIELD_PRIMES["goldilocks"]) -> Union[int, SymbolicSteps]:
    """
    Infers the number of iterations a while's exit condition allows, given a
    single BoolCmp (one half of a bool.and, or the whole condition). See
    _resolve_comparison_recurrence for the shared resolution logic.
    """
    resolved = _resolve_comparison_recurrence(initial_comparison, var2expression, initial_values, var2const, prime)
    if isinstance(resolved, SymbolicSteps):
        return resolved
    return count_iterations(resolved.initial_value, resolved.compare_func, resolved.update_func)


def _infer_sequence_from_comparison(initial_comparison: BoolCmp,
                                    var2expression: Dict[str, Union[str, Operation]],
                                    initial_values: Dict[str, int],
                                    var2const: Dict[str, int],
                                    prime: int = FIELD_PRIMES["goldilocks"]) -> Optional[List[int]]:
    """
    Like _infer_from_comparison, but returns the actual list of values the
    loop-carried variable visits (one per iteration, in order) instead of
    just the count. Returns None when the recurrence isn't fully concrete
    (a SymbolicSteps-shaped bound) -- there's no way to list values for a
    count that's itself only known as a Core-level formula.
    """
    resolved = _resolve_comparison_recurrence(initial_comparison, var2expression, initial_values, var2const, prime)
    if isinstance(resolved, SymbolicSteps):
        return None
    return iterate_values(resolved.initial_value, resolved.compare_func, resolved.update_func)


def construct_function_from_expressions(current_expr: SSAVar,
                                        var2expression: Dict[str, Union[str, Operation]],
                                        traversed: Set[str],
                                        prime: int = FIELD_PRIMES["goldilocks"]) -> Callable:
    """
    Construct a Python callable f(x) -> int that computes current_expr
    in terms of ground_var.

    var2expression values are either:
      - an Operation: call its to_function(), recurse on operands
      - a str: the name of another SSA variable with the same value (alias)

    Every composed operation's result is reduced modulo `prime` (default:
    goldilocks, matching every existing example) -- this is what makes the
    simulation correctly emulate real field arithmetic: a value that would
    wrap in the real field (e.g. a decrementing counter going below 0)
    becomes prime-1, not a raw, ever-decreasing Python int that would never
    equal a wrapped bound like circom's "-1" (see felt.py's FeltBinary/
    FeltUnary/FeltConst, whose own to_function() has no notion of a field
    at all otherwise).
    """
    # Ignore the case where an element has already been traversed (base case)
    if current_expr.name in traversed:
        return lambda x: x

    traversed.add(current_expr.name)
    expression = var2expression[current_expr.name]

    if isinstance(expression, str):
        return construct_function_from_expressions(
            SSAVar(expression), var2expression, traversed, prime
        )

    raw_fn = expression.to_function(prime)
    operand_fns = [
        construct_function_from_expressions(op, var2expression, traversed, prime)
        for op in expression.operands
    ]

    # Use default-arg capture to avoid late-binding closure issues
    if not operand_fns:
        return lambda x, _fn=raw_fn: _fn()
    return lambda x, _fn=raw_fn, _fns=operand_fns: _fn(*[f(x) for f in _fns])


def _too_many_iterations(count: int) -> NoReturn:
    raise RuntimeError(
        f"While-loop trip-count simulation exceeded {_MAX_SIMULATED_ITERATIONS} "
        "iterations without the condition going false -- almost certainly a "
        "non-terminating recurrence (e.g. a predicate/field-arithmetic shape "
        "this codebase doesn't model correctly yet), not a real circuit loop; "
        "failing fast instead of hanging indefinitely."
    )


def count_iterations(initial_value, condition_fn, update_fn):
    value = initial_value
    count = 0
    while condition_fn(value):
        value = update_fn(value)
        count += 1
        if count > _MAX_SIMULATED_ITERATIONS:
            _too_many_iterations(count)
    return count


def iterate_values(initial_value, condition_fn, update_fn) -> List[int]:
    """
    Like count_iterations, but returns the actual sequence of values the
    loop-carried variable takes -- one entry per iteration, in order (the
    value the variable holds *during* that iteration, before its update),
    rather than just how many there are.
    """
    values = []
    value = initial_value
    while condition_fn(value):
        values.append(value)
        value = update_fn(value)
        if len(values) > _MAX_SIMULATED_ITERATIONS:
            _too_many_iterations(len(values))
    return values
