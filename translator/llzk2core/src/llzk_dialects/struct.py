"""
Struct dialect — circuit component definitions and member access.
Prefix: struct.

In LLZK, a 'struct' represents a ZK circuit component. It has named members
(signals/columns) and two special functions: 'compute' (witness generation)
and 'constrain' (constraint emission).

Types:
  StructType — !struct.type<@NameRef<[params]>>

Operations:
  StructMember — struct.member  (declare a named member field inside a struct.def)
  StructNew    — struct.new     (instantiate a struct)
  StructReadm  — struct.readm   (read a member from a struct instance)
  StructWritem — struct.writem  (write a value to a struct member)
  StructDef    — struct.def     (BlockOperation: define a circuit component)
"""

import itertools
import re
from typing import Dict, List, Optional, Tuple, Generator

from llzk_dialects.core import (
    Operation, BlockOperation, SSAVar, GlobalVariable, Type,
    TranslationContext, ParseFn,
)
from llzk_dialects.definitions import Dialect
from llzk_dialects.function import FunctionDef
from llzk_dialects.utils import array_dimensions, split_top_level_commas, struct_type_name
from llzk_dialects.core_utils import translate_assignment_core_with_ctx


def _annotate_function_calls(ops, pod_to_member):
    """
    Walk ops recursively, stamping _member_hint on each FunctionCall whose
    result is immediately stored into a component pod via pod.write/@comp or
    pod.new{@comp=...}.

    A per-body SSA def-map is built at each nesting level so that two sibling
    scf.if branches that both define %16 as a call result are treated as
    distinct Python objects and can carry different hints independently.
    """
    from llzk_dialects.function import FunctionCall
    from llzk_dialects.pod import PodNew, PodWrite

    # SSA def-map for this body level only (not sub-bodies)
    def_map = {}
    for op in ops:
        if op.result is not None:
            def_map[op.result.name] = op

    for op in ops:
        if isinstance(op, PodWrite) and op.record_name.name == "@comp":
            member = pod_to_member.get(op.pod_ref.name)
            if member is not None:
                defining_op = def_map.get(op.value.name)
                if isinstance(defining_op, FunctionCall):
                    defining_op._member_hint = member
        elif isinstance(op, PodNew) and "@comp" in op.init_records:
            member = pod_to_member.get(op._result.name)
            if member is not None:
                defining_op = def_map.get(op.init_records["@comp"].name)
                if isinstance(defining_op, FunctionCall):
                    defining_op._member_hint = member

        for attr in ('body', 'then_body', 'else_body', 'before_body', 'after_body'):
            sub = getattr(op, attr, None)
            if sub:
                _annotate_function_calls(sub, pod_to_member)


def _fold_index_constants(ops):
    """
    Pre-pass constant folder over a single body level: maps SSA names to
    their statically-known integer value, resolving felt.const/arith.constant
    literals through identity casts (cast.toindex/cast.tofelt).

    Used ahead of to_core translation (before ctx.var2const is populated) to
    tell whether an array.read/array.write in an array-of-components loop
    body accesses a specific, compile-time-known component index — see
    _find_array_component_bases.
    """
    from llzk_dialects.felt import FeltConst
    from llzk_dialects.arith import ArithConst, parse_arith_const_value
    from llzk_dialects.cast import CastToIndex, CastToFelt

    const_map = {}
    for op in ops:
        if isinstance(op, FeltConst):
            const_map[op.result.name] = op.constant
        elif isinstance(op, ArithConst):
            const_map[op.result.name] = parse_arith_const_value(op.value)
        elif isinstance(op, (CastToIndex, CastToFelt)):
            value = const_map.get(op.value.name)
            if value is not None:
                const_map[op.result.name] = value
    return const_map


def _walk_for_bulk_copy_nest(ops, iv_stack, target_to_counting):
    """
    Recursively walk a (possibly nested) chain of scf.for loops looking for
    the bulk-copy triple (array.read a counting-pod array; pod.read its
    @comp field; array.write the result into the target array) at every
    level, indexed by ALL enclosing loops' own induction variables in
    outer-to-inner order.

    An N-D array-of-components member's bulk copy nests N scf.for loops,
    one per dimension -- so the triple only actually matches at the
    innermost level, where len(indices) == len(iv_stack) == N. At any
    non-innermost level the triple check simply finds nothing (the index
    count doesn't match yet) and recursion carries on deeper; this reduces
    to exactly the original single-scf.for, single-index behavior when
    there's no nesting at all (iv_stack of length 1).
    """
    from llzk_dialects.scf import SCFFor
    from llzk_dialects.pod import PodRead
    from llzk_dialects.array import ArrayRead, ArrayWrite

    for op in ops:
        if not isinstance(op, SCFFor):
            continue
        ivs = iv_stack + [op.iv]

        # array.read result -> counting array ssa, restricted to reads
        # indexed by every enclosing loop's own induction variable, in order
        comp_reads = {
            inner._result.name: inner.arr_ref.name
            for inner in op.body
            if isinstance(inner, ArrayRead)
            and len(inner.indices) == len(ivs)
            and all(idx.name == iv.name for idx, iv in zip(inner.indices, ivs))
        }
        # pod.read(@comp) result -> counting array ssa
        comp_vals = {}
        for inner in op.body:
            if isinstance(inner, PodRead) and inner.record_name.name == "@comp":
                counting_arr = comp_reads.get(inner.pod_ref.name)
                if counting_arr is not None:
                    comp_vals[inner._result.name] = counting_arr
        for inner in op.body:
            if (isinstance(inner, ArrayWrite) and len(inner.indices) == len(ivs)
                    and all(idx.name == iv.name for idx, iv in zip(inner.indices, ivs))):
                counting_arr = comp_vals.get(inner.rvalue.name)
                if counting_arr is not None:
                    target_to_counting[inner.arr_ref.name] = counting_arr

        # Recurse into this loop's own body to find a nested scf.for
        # continuing the bulk-copy nest one dimension deeper.
        _walk_for_bulk_copy_nest(op.body, ivs, target_to_counting)


def _find_array_component_bases(body):
    """
    Detect array-of-component members: a struct member holding an array of
    subcomponents (e.g. "@last : !array.type<2 x !struct.type<...>>", or,
    for an N-D collection, "!array.type<M,N x !struct.type<...>>") is
    populated, at the end of compute, by a bulk-copy nest of scf.for loops
    (one per dimension) that reads each "counting pod" array element's
    @comp field (the just-computed subcomponent) and writes it into the
    array that is then struct-written into that member.

    Returns a dict mapping the counting-pod array's own SSA name to the
    member's base name (no @), so a later constant-indexed read of that
    counting array (see _build_component_naming_maps) can be attributed to
    a specific component instance, e.g. "last#0" (or "last#0#1" for a 2-D
    collection).
    """
    target_to_counting = {}
    _walk_for_bulk_copy_nest(body, [], target_to_counting)

    array_member_base = {}
    for op in body:
        if (isinstance(op, StructWritem) and op.types
                and "_inputs" not in op.member_name.name
                and "!struct" in op.types[-1].name):
            counting_arr = target_to_counting.get(op.value.name)
            if counting_arr is not None:
                array_member_base[counting_arr] = op.member_name.name[1:]  # strip @
    return array_member_base


def _annotate_array_component_reads(ops, array_member_base, const_map, pod_to_member):
    """
    Recursively scan a body for reads of a counting-pod array that backs an
    array-of-component member (array_member_base, from
    _find_array_component_bases), stamping pod_to_member[read_result] with
    a name for the slot that was read:

      - "{base}#{idx1}#{idx2}#..." (a plain string, one "#idx" segment per
        dimension) when EVERY one of the read's indices resolves to a
        compile-time constant (via a local constant fold — const_map
        carries constants folded in enclosing scopes down into this one,
        without leaking sideways between sibling branches that may reuse
        the same SSA names, e.g. two scf.for loops in the same function
        both using "%arg1" as their induction variable).
      - the bare base name when any index doesn't — the read sits inside a
        genuine runtime loop (e.g. an scf.while's after-body), so there is
        no single instance to name more specifically at translation time
        (any further per-iteration disambiguation is resolved afterwards
        by llzk_cli). A partially-resolved index (some constant, some not)
        still isn't enough to name one specific instance, so it's treated
        the same as fully-unresolved.

    _annotate_function_calls then picks up these entries exactly like the
    scalar-subcomponent ones already in pod_to_member.

    array_member_base is expected to already be fully resolved by the
    caller (_build_component_naming_maps), including every scf.while
    region's own block-arg aliases -- see
    _collect_while_region_array_aliases -- so this function itself stays a
    plain, single-mechanism SSA-identity lookup, matching
    _annotate_input_array_reads' identical division of labor for the
    $inputs-pod case.
    """
    from llzk_dialects.array import ArrayRead

    local_const_map = dict(const_map)
    local_const_map.update(_fold_index_constants(ops))

    for op in ops:
        if isinstance(op, ArrayRead) and op.arr_ref.name in array_member_base:
            base = array_member_base[op.arr_ref.name]
            idx_vals = [local_const_map.get(idx.name) for idx in op.indices]
            if idx_vals and all(v is not None for v in idx_vals):
                pod_to_member[op._result.name] = base + "".join(f"#{v}" for v in idx_vals)
            else:
                pod_to_member[op._result.name] = base

        for attr in ('body', 'then_body', 'else_body', 'before_body', 'after_body'):
            sub = getattr(op, attr, None)
            if sub:
                _annotate_array_component_reads(sub, array_member_base, local_const_map, pod_to_member)


def _trace_to_enclosing_loop(name, loop_stack, def_map, const_map=None):
    """
    Resolve `name` back through cast.toindex/cast.tofelt identity casts and
    constant-offset felt.add hops (using def_map, the SSA definitions
    visible at this point, and const_map, to recognize a hop's already-known
    operand) until it matches one of loop_stack's own induction variable
    (scf.for) or after-region block-arg (scf.while) names. Returns
    (loop, offset) -- offset is the net constant that must be ADDED to the
    matched loop's own raw counter value to get `name`'s actual value (0 for
    the common case of a pure identity chain) -- or (None, 0) if `name`
    can't be resolved to any loop_stack member at all.

    Deliberately does NOT assume positional correspondence between an
    array read's index list and loop_stack's own nesting order -- an
    array's declared dimension order need not match its population loop's
    own nesting order (confirmed via
    arbitrary_traversal_array_components.circom: "components[i][j]" has i,
    array dimension 0, driven by the INNER loop, and j, dimension 1, by
    the OUTER one).

    The felt.add case (confirmed necessary via poseidon3_test_concrete.mlir:
    "sigmaF[nRoundsF\\2 + r][j]" lowers to "felt.add %felt_const_4, %arg5"
    before the cast.toindex, not a bare identity cast) only recognizes a
    single constant operand per hop -- multiplication, subtraction, or any
    other transform is deliberately out of scope (no real example needs it
    yet; see DECISIONS.md).
    """
    from llzk_dialects.scf import SCFFor, SCFWhile
    from llzk_dialects.cast import CastToIndex, CastToFelt
    from llzk_dialects.felt import FeltBinary

    const_map = const_map or {}
    seen = set()
    offset = 0
    while name not in seen:
        seen.add(name)
        for loop in loop_stack:
            if isinstance(loop, SCFFor) and loop.iv.name == name:
                return loop, offset
            if isinstance(loop, SCFWhile) and any(arg.name == name for arg, _ in loop.after_args):
                return loop, offset
        defining_op = def_map.get(name)
        if isinstance(defining_op, (CastToIndex, CastToFelt)):
            name = defining_op.value.name
        elif isinstance(defining_op, FeltBinary) and defining_op._op == "felt.add":
            lhs_val = const_map.get(defining_op.lhs.name)
            rhs_val = const_map.get(defining_op.rhs.name)
            if lhs_val is not None and rhs_val is None:
                offset += lhs_val
                name = defining_op.rhs.name
            elif rhs_val is not None and lhs_val is None:
                offset += rhs_val
                name = defining_op.lhs.name
            else:
                return None, 0
        else:
            return None, 0
    return None, 0


def _loop_own_sequence(loop, const_map):
    """
    The real sequence of values `loop`'s own induction variable /
    after-region block-arg takes across its iterations, in order -- or
    None if it can't be statically determined (a bound that isn't
    resolvable via const_map, or -- for scf.while -- a SymbolicSteps-shaped
    recurrence). const_map is the caller's own pre-pass-time constant fold
    (never real ctx.var2const, which is empty at pre-pass time -- see
    _find_array_component_population_sequences).
    """
    from llzk_dialects.scf import SCFFor, SCFWhile

    if isinstance(loop, SCFFor):
        lb = const_map.get(loop.lb.name)
        ub = const_map.get(loop.ub.name)
        step = const_map.get(loop.step.name, 1)
        if lb is None or ub is None:
            return None
        return list(range(lb, ub, step))

    if isinstance(loop, SCFWhile):
        initial_values = {}
        for block_arg, init_val in loop.init_args:
            value = const_map.get(init_val.name)
            if value is not None:
                initial_values[block_arg.name] = value
        try:
            return loop._extract_index_sequence(initial_values, const_map)
        except (NotImplementedError, KeyError, AssertionError):
            # Best-effort static analysis: any shape _extract_index_sequence
            # doesn't (yet) handle degrades to "can't resolve" rather than
            # aborting the whole translation.
            return None

    return None


def _resolve_population_nest_sequence(write, loop_stack, def_map, const_map):
    """
    For one array-of-components population write (an ArrayWrite into a
    registered counting-pod array, with at least one non-compile-time-
    constant index), resolve each of its indices back to the specific
    enclosing loop that produces it (_trace_to_enclosing_loop -- by SSA
    identity, never by position) and combine the implicated loops' own
    sequences (_loop_own_sequence) into this nest's list of concrete
    index tuples, in ARRAY DIMENSION order (matching the write's own index
    order), with the outer-to-inner loop nesting order determining which
    combination is visited when (true execution order: the outermost
    implicated loop varies slowest).

    A dimension can also be a plain compile-time constant on its own (e.g.
    one dimension fixed by an enclosing scf.if branch while another is
    genuinely loop-driven -- confirmed necessary via
    poseidon3_test_concrete.mlir's "sigmaF[nRoundsF\\2-1][j]"/
    "sigmaF[nRoundsF-1][j]" population sites, where the row is a fixed
    literal and only the column comes from this write's own scf.while):
    such a dimension is excluded from the loop combination entirely and
    gets the same fixed value in every generated tuple.

    Returns None if any index can't be resolved to EITHER a loop_stack
    member OR a plain constant, or if any implicated loop's own sequence
    can't be statically determined.
    """
    dim_to_loop = {}
    dim_to_offset = {}
    dim_to_const = {}
    for dim, idx in enumerate(write.indices):
        loop, offset = _trace_to_enclosing_loop(idx.name, loop_stack, def_map, const_map)
        if loop is not None:
            dim_to_loop[dim] = loop
            dim_to_offset[dim] = offset
            continue
        const_val = const_map.get(idx.name)
        if const_val is None:
            return None
        dim_to_const[dim] = const_val

    # Only the loops actually used to index this array matter for THIS
    # write -- an enclosing loop that doesn't drive any of its indices
    # doesn't need to be resolvable at all. Preserve loop_stack's own
    # outer-to-inner order.
    ordered_loops = [loop for loop in loop_stack if loop in dim_to_loop.values()]

    per_loop_sequence = {}
    for loop in ordered_loops:
        sequence = _loop_own_sequence(loop, const_map)
        if sequence is None:
            return None
        per_loop_sequence[id(loop)] = sequence

    num_dims = len(write.indices)
    nest_tuples = []
    # No loop-driven dimension at all is not a real population write (see
    # this function's own caller: _collect_population_write_candidates only
    # collects writes with at least one non-compile-time-constant index),
    # but degrade to a single fixed-value tuple rather than crashing on an
    # empty itertools.product if it ever happens.
    combos = itertools.product(*(per_loop_sequence[id(loop)] for loop in ordered_loops)) \
        if ordered_loops else [()]
    for combo in combos:
        loop_to_value = dict(zip((id(loop) for loop in ordered_loops), combo))
        nest_tuples.append(tuple(
            dim_to_const[d] if d in dim_to_const
            else loop_to_value[id(dim_to_loop[d])] + dim_to_offset[d]
            for d in range(num_dims)
        ))
    return nest_tuples


def _is_population_write(write, def_map):
    """
    True iff `write` (an ArrayWrite into a registered counting-pod array)
    is a real read-modify-write population write -- its own value traces
    directly back to an ArrayRead of that SAME array -- as opposed to, say,
    the array's own initial fill loop (a fresh pod.new written into every
    slot, with the array never read from at all first). Both shapes are
    ordinary ArrayWrites into the registered array with non-constant
    indices, so the read-modify-write pattern is what actually
    distinguishes "this iteration corresponds to a real @compute call" from
    "this is just allocating backing storage" -- confirmed necessary via
    arbitrary_traversal_array_components_concrete.mlir, whose init loop
    (array.write %array[%arg1, %arg2] = %pod_8, %pod_8 a fresh pod.new) was
    otherwise indistinguishable from a genuine population write and
    produced a spurious extra 30-entry row-major sequence.
    """
    from llzk_dialects.array import ArrayRead

    source = def_map.get(write.rvalue.name)
    return isinstance(source, ArrayRead) and source.arr_ref.name == write.arr_ref.name


def _collect_population_write_candidates(ops, array_member_base, const_map, def_map, out):
    """
    Collect every population-write candidate (ArrayWrite into a registered
    counting-pod array, non-constant indices, _is_population_write)
    reachable from `ops` WITHOUT crossing into a nested scf.for/scf.while
    -- i.e. everything still within the current loop iteration's own
    scope, recursing through scf.if/scf.execute_region nesting (neither of
    which starts a new array dimension). Appends
    (write, const_map_at_that_point, def_map_at_that_point) to `out`, in
    program order.

    More than one candidate can genuinely exist in the same scope: LLZK
    lowers a multi-input-signal component's "ready to call yet?" check to
    fire once per input-signal assignment (@count starts at the input
    count and is decremented each time), each with its own full call +
    array-write scaffolding -- but only the LAST such checkpoint's
    condition is ever true at runtime (count only reaches exactly 0 once,
    after the final signal is assigned). Confirmed via
    arbitrary_traversal_array_components_concrete.mlir's IsZero component
    (2 input signals): both checkpoints structurally qualify, but only the
    second is ever the real one -- the caller keeps only the last entry in
    `out`.
    """
    from llzk_dialects.scf import SCFFor, SCFWhile
    from llzk_dialects.array import ArrayWrite

    local_const_map = dict(const_map)
    local_const_map.update(_fold_index_constants(ops))
    local_def_map = dict(def_map)
    for op in ops:
        if getattr(op, 'result', None) is not None:
            local_def_map[op.result.name] = op

    for op in ops:
        if isinstance(op, (SCFFor, SCFWhile)):
            continue  # starts a new dimension -- handled by the caller separately

        if (isinstance(op, ArrayWrite) and op.arr_ref.name in array_member_base
                and not all(idx.name in local_const_map for idx in op.indices)
                and _is_population_write(op, local_def_map)):
            out.append((op, local_const_map, local_def_map))

        for attr in ('then_body', 'else_body', 'body'):
            sub = getattr(op, attr, None)
            if sub:
                _collect_population_write_candidates(sub, array_member_base, local_const_map,
                                                      local_def_map, out)


def _walk_array_component_population(ops, array_member_base, const_map, loop_stack, def_map, member_nests):
    """
    Recursively find every scf.for/scf.while in `ops` (crossing through
    scf.if/scf.execute_region nesting freely, since neither starts a new
    array dimension), growing loop_stack as each is entered. For each
    loop's own direct body (once entered), collects every population-write
    candidate reachable from it without crossing into a FURTHER nested
    scf.for/scf.while (_collect_population_write_candidates) and keeps only
    the LAST one found -- see that function's own docstring for why more
    than one can exist. Then keeps looking, inside that same body, for a
    further nested loop (the next array dimension).

    member_nests accumulates member_base -> [nest_sequence, ...], one entry
    per distinct population site, in body-encounter order -- which is also
    true execution order, since separate population loop nests for the same
    member (e.g. arbitrary_traversal_array_components.circom's even-index
    and odd-index nests) run strictly sequentially in the source.
    """
    from llzk_dialects.scf import SCFFor, SCFWhile

    local_const_map = dict(const_map)
    local_const_map.update(_fold_index_constants(ops))

    local_def_map = dict(def_map)
    for op in ops:
        if getattr(op, 'result', None) is not None:
            local_def_map[op.result.name] = op

    for op in ops:
        if not isinstance(op, (SCFFor, SCFWhile)):
            for attr in ('then_body', 'else_body', 'body'):
                sub = getattr(op, attr, None)
                if sub:
                    _walk_array_component_population(sub, array_member_base, local_const_map,
                                                     loop_stack, local_def_map, member_nests)
            continue

        next_stack = loop_stack + [op]
        for attr in ('body', 'before_body', 'after_body'):
            sub = getattr(op, attr, None)
            if not sub:
                continue

            candidates = []
            _collect_population_write_candidates(sub, array_member_base, local_const_map,
                                                  local_def_map, candidates)
            if candidates:
                write, write_const_map, write_def_map = candidates[-1]
                member = array_member_base[write.arr_ref.name]
                nest_sequence = _resolve_population_nest_sequence(
                    write, next_stack, write_def_map, write_const_map)
                if nest_sequence is not None:
                    member_nests.setdefault(member, []).append(nest_sequence)

            # Keep looking for a further nested loop (the next dimension)
            # inside this same body.
            _walk_array_component_population(sub, array_member_base, local_const_map,
                                             next_stack, local_def_map, member_nests)


def _find_array_component_population_sequences(body, array_member_base):
    """
    For each array-of-components member (array_member_base) populated
    inside at least one genuinely symbolic loop, computes the real sequence
    of concrete array-index tuples the population loop(s) actually visit,
    in true execution order -- for signal_renaming.py to attribute each
    call in llzk_cli's own SMT-level unrolled trace to the real array index
    it was called with, instead of assuming sequential 0,1,2,... visitation
    (wrong for an N-D member, or any non-row-major traversal order).

    Returns member_base -> List[Tuple[int, ...]], concatenating multiple
    separate population loop nests for the same member (see
    arbitrary_traversal_array_components.circom) in body-encounter order.
    A member with no genuinely-symbolic population site at all, or whose
    population loop's own bound isn't statically resolvable, is simply
    absent from the result -- signal_renaming.py falls back to its
    original counter-based behavior for it in that case.
    """
    member_nests = {}
    _walk_array_component_population(body, array_member_base, {}, [], {}, member_nests)
    return {
        member: [idx_tuple for nest in nests for idx_tuple in nest]
        for member, nests in member_nests.items()
    }


def _is_idx_pod_component_member(type_str: str) -> Optional[Dict[str, Type]]:
    """
    A heterogeneous array-of-components member: a pod whose fields are all
    literal @idx_N records (_is_idx_pod_fields) AND whose field values are
    all !struct.type -- the shape LLZK lowers a Circom collection to when
    each index instantiates a *different* template (so it can't be a real
    !array.type<N x !struct.type<...>>, which requires one shared type).

    Returns the parsed field dict (@idx_N -> struct Type) on a match, else
    None. The all-struct-typed-fields check distinguishes this from the
    member's own "$inputs" companion pod (e.g. "@ark_inputs"), whose @idx_N
    fields are themselves !pod.type, not !struct.type.
    """
    from llzk_dialects.pod import _parse_pod_fields, _is_idx_pod_fields

    if "!pod.type" not in type_str:
        return None
    fields = _parse_pod_fields(type_str)
    if not _is_idx_pod_fields(fields):
        return None
    if not all(t.name.strip().startswith("!struct.type") for t in fields.values()):
        return None
    return fields


def _idx_read_matches_member(result_type: Optional[Type], expected_struct_type: Type) -> bool:
    """
    True iff a pod.read[@idx_N]'s own declared RESULT type corresponds to
    `expected_struct_type` (the struct type @idx_N is declared as on the
    struct.member itself, e.g. "!struct.type<@Ark_0::@Ark_0<[]>>") --
    either directly (the read yields the struct value itself) or through a
    "counting pod" wrapper's own @comp field.

    The wrapped case is what real LLZK output actually uses throughout
    compute: a heterogeneous slot's counting-pod holder is read as a whole
    (pod.read %holder[@idx_N] : ..., !pod.type<[@count: index,
    @comp: !struct.type<@Ark_N::@Ark_N<[]>>, @params: !pod.type<[]>]>) --
    the SAME @count/@comp/@params bookkeeping idiom this codebase already
    uses uniformly for scalar and homogeneous-array subcomponent tracking
    (_find_array_component_bases) -- and it is that read's OWN result which
    a later pod.write[@comp]/pod.new{@comp=...} in the same scope targets,
    not the member's own final declared type (only assembled once, straight
    -line, at the very end of compute, from already-computed @comp values
    -- see _annotate_idx_pod_component_reads).
    """
    if result_type is None:
        return False
    if result_type == expected_struct_type:
        return True
    if "!pod.type" not in result_type.name:
        return False
    from llzk_dialects.pod import _parse_pod_fields
    return _parse_pod_fields(result_type.name).get("@comp") == expected_struct_type


def _annotate_idx_pod_component_reads(ops, idx_pod_member_types, pod_to_member):
    """
    Recursively scan a body for pod.read [@idx_N] of a pod matching one of
    the struct's own heterogeneous array-of-components members
    (idx_pod_member_types, from StructDef.to_core's struct.member scan --
    see _is_idx_pod_component_member), stamping
    pod_to_member[read_result] = "{member}#{N}". That read's result is
    exactly the "counting pod" value a later pod.write[@comp]/
    pod.new{@comp=...} targets, so the existing _annotate_function_calls
    picks this up exactly like the scalar/homogeneous-array cases already
    in pod_to_member -- no change needed there.

    Unlike _annotate_array_component_reads (the homogeneous-array case), no
    constant-folding or scope-copied state is needed: @idx_N is always a
    literal pod field name in the LLZK IR, never a runtime-computed index,
    so there is no "was this index a compile-time constant" question to
    resolve. Matching is instead done purely on each read's own declared
    RESULT type (_idx_read_matches_member), which works uniformly no matter
    which control-flow shape a given read happens to sit inside
    (straight-line unrolled code, a genuine scf.while, or a runtime-index
    scf.if/scf.execute_region dispatch ladder) -- unlike the homogeneous
    case, this never needs to trace an SSA's origin through
    scf.while/scf.if aliasing at all.
    """
    from llzk_dialects.pod import PodRead, _IDX_FIELD_RE, _idx_pod_child_name

    for op in ops:
        if isinstance(op, PodRead) and _IDX_FIELD_RE.match(op.record_name.name):
            for member, fields in idx_pod_member_types.items():
                expected = fields.get(op.record_name.name)
                if expected is not None and _idx_read_matches_member(op.result_type, expected):
                    pod_to_member[op._result.name] = _idx_pod_child_name(
                        member, op.record_name.name)
                    break

        for attr in ('body', 'then_body', 'else_body', 'before_body', 'after_body'):
            sub = getattr(op, attr, None)
            if sub:
                _annotate_idx_pod_component_reads(sub, idx_pod_member_types, pod_to_member)


def _while_flat_result_names(op):
    """
    One scf.while's own results, flattened to their individual Core
    component names ("%421#0", "%421#1", ... or, for a single-component
    result, the bare "%421"), in declaration order. Shared by
    _while_iter_arg_pairs and _while_after_arg_pairs so both derive the
    exact same flattening from op.results, never two independently
    maintained copies of this computation.
    """
    flat_results = []
    for res in op.results:
        for k in range(res.n_components):
            flat_results.append(res.to_core_component(k))
    return flat_results


def _while_iter_arg_pairs(op):
    """
    (flat_result_component_name, (block_arg, init_val)) pairs for one
    scf.while's own iter-args, in declaration order. Shared by
    _build_component_naming_maps's result_to_init construction (top-level
    only) and _collect_while_iter_args (recursive) so both derive the exact
    same pairing from op.results/op.init_args, never two independently
    maintained copies of this computation.
    """
    return list(zip(_while_flat_result_names(op), op.init_args))


def _while_after_arg_pairs(op):
    """
    (flat_result_component_name, after_region_block_arg) pairs for one
    scf.while's own after_args, in declaration order -- the after-region's
    own block-arg names, as distinct from _while_iter_arg_pairs' init_args
    block-args (the before-region's own binder). SCFWhile.parse parses
    these as genuinely separate SSAVar objects (its own block_arg_rename
    unions both name sets rather than assuming they coincide), so a value
    referenced *inside* the after-region body (e.g. a population write)
    must be resolved through this pairing, not init_args'.
    """
    return [(name, arg_var) for name, (arg_var, _type)
            in zip(_while_flat_result_names(op), op.after_args)]


def _collect_while_region_array_aliases(ops, aliases):
    """
    Recursively collect, for every scf.while at any depth, every pair of
    SSA names known to denote the SAME logical loop-carried value at
    different points in its lifetime, as plain (name1, name2) equivalence
    pairs (order doesn't matter -- the caller's fixpoint resolution checks
    both directions):

      - (before-region block-arg, own flattened result name)
      - (before-region block-arg, own init value)
      - (after-region block-arg, own flattened result name)
      - (own flattened result name, own init value)

    The last one is the piece a single-direction, outer-to-inner pass
    (like _collect_while_iter_args' identical $inputs-pod case) can't
    handle: it connects one while's own result DIRECTLY to its own init
    value, which is what lets resolution propagate BACKWARD through a
    chain of SEQUENTIAL, SIBLING while loops -- each one threading the
    same array through as the NEXT one's own init value, not nested one
    inside another at all. Confirmed necessary via poseidon3_new.mlir's
    real "sigmaF" population: its 4 disjoint population sites (mirroring
    poseidon.circom's 4 separate loops over disjoint row ranges) run
    sequentially, each site's own while taking the PREVIOUS site's own
    result as its own init value. Only the LAST site's own result is what
    the post-loop bulk-copy (and so array_member_base) directly registers
    -- the first three sites only resolve by walking this same-result-as-
    next-site's-init-value chain backward, which a single forward pass
    over encounter order cannot do regardless of order (the registered
    identity is discovered LAST, not first).

    Because of this, the caller must resolve these to a FIXPOINT --
    repeatedly propagating a known name to its paired name until nothing
    changes -- rather than the single forward pass _collect_while_iter_args'
    entirely-nested-only case gets away with.
    """
    from llzk_dialects.scf import SCFWhile

    for op in ops:
        if isinstance(op, SCFWhile):
            for flat_name, (before_arg, init_val) in _while_iter_arg_pairs(op):
                aliases.append((before_arg.name, flat_name))
                aliases.append((before_arg.name, init_val.name))
                aliases.append((flat_name, init_val.name))
            for flat_name, after_arg in _while_after_arg_pairs(op):
                aliases.append((after_arg.name, flat_name))

        for attr in ('body', 'then_body', 'else_body', 'before_body', 'after_body'):
            sub = getattr(op, attr, None)
            if sub:
                _collect_while_region_array_aliases(sub, aliases)


def _collect_while_iter_args(ops, while_iter_args):
    """
    Recursively collect every scf.while's own (block_arg_name, init_val_name)
    iter-arg pairs into while_iter_args, at any nesting depth -- not just
    ops' own top level. Appends in outer-to-inner traversal order (an op's
    own pairs before recursing into its sub-bodies), which
    _build_component_naming_maps's single-pass alias-resolution loop
    depends on: a doubly (or deeper) nested scf.while's own block-arg name
    resolves through its immediately enclosing scf.while's
    ALREADY-resolved alias, one level at a time, with no bound on nesting
    depth.

    Without this, a $inputs array/pod threaded through more than one level
    of scf.while (e.g. poseidon3_test_concrete.mlir's "@mixLast$inputs",
    re-carried by an inner scf.while nested inside an outer one) only gets
    its OUTERMOST loop's block-arg aliased -- a read using the inner loop's
    own block-arg name (e.g. "%arg4") never resolves, silently falling back
    to a raw SSA-derived name instead of the semantic "mixLast#0.in".
    """
    from llzk_dialects.scf import SCFWhile

    for op in ops:
        if isinstance(op, SCFWhile):
            for _, (block_arg, init_val) in _while_iter_arg_pairs(op):
                while_iter_args.append((block_arg.name, init_val.name))

        for attr in ('body', 'then_body', 'else_body', 'before_body', 'after_body'):
            sub = getattr(op, attr, None)
            if sub:
                _collect_while_iter_args(sub, while_iter_args)


def _annotate_input_array_reads(ops, ctx, const_map):
    """
    Recursively stamp ArrayRead._semantic_base on every read of a registered
    "$inputs" component array (ctx.input_pod_to_member), mirroring what
    _annotate_array_component_reads does for the counting-pod array side.

    This must use its own scope-safe static constant fold (const_map, built
    the same way as in _annotate_array_component_reads) rather than
    ctx.var2const: SCFFor/SCFWhile deliberately treat their own
    loop-carried variables as a compile-time constant in ctx.var2const for
    structural purposes (see their own to_core), even though the value
    actually varies per iteration. Trusting that here would misattribute a
    genuinely symbolic loop index (e.g. ternary_concrete.mlir's
    Num2Bits_16_325, instantiated inside a real scf.while) to one specific
    instance instead of leaving it as the bare member name — there is no
    single instance to name more specifically at translation time.
    """
    from llzk_dialects.array import ArrayRead

    local_const_map = dict(const_map)
    local_const_map.update(_fold_index_constants(ops))

    for op in ops:
        if isinstance(op, ArrayRead):
            member = ctx.input_pod_to_member.get(op.arr_ref.name)
            if member is not None:
                idx_vals = [local_const_map.get(idx.name) for idx in op.indices]
                if idx_vals and all(v is not None for v in idx_vals):
                    op._semantic_base = member + "".join(f"#{v}" for v in idx_vals)
                else:
                    op._semantic_base = member

        for attr in ('body', 'then_body', 'else_body', 'before_body', 'after_body'):
            sub = getattr(op, attr, None)
            if sub:
                _annotate_input_array_reads(sub, ctx, local_const_map)


def _build_component_naming_maps(body, ctx, idx_pod_member_types=None):
    """
    Pre-pass: scan a compute function body to build naming maps.

    1. ctx.input_pod_to_member — pod_ssa -> member base name
       Used by PodNew so semantic field names like "mux.c" are used instead
       of raw "%pod_0_@c" names.  Traces through scf.while result chains.
       Also consumed by _annotate_input_array_reads, which stamps this same
       base name (plus "_idx" for a constant index) directly onto every
       ArrayRead of such an array — see ArrayRead._semantic_base.

    2. FunctionCall._member_hint — stamped directly on each call node.
       Used by FunctionCall.to_core() so the output is named "n2ba.out"
       instead of "%16_@out".  Per-body SSA def-maps prevent collisions when
       two sibling scf.if branches define the same SSA name.

    Array-of-component members (see _find_array_component_bases) reuse the
    same pod_to_member map from part 2, keyed by a read of the counting-pod
    array — "last_0" (a plain string) for a compile-time-constant index
    (matching a scalar subcomponent's own naming), or the bare base name
    (e.g. "Num2Bits_16_325") when the read sits inside a genuine runtime
    loop (index not constant) — there is no single instance to name more
    specifically at translation time; every call inside such a loop shares
    that one bare name, with any further per-iteration disambiguation
    resolved afterwards by llzk_cli.

    `idx_pod_member_types` (from StructDef.to_core's struct.member scan,
    see _is_idx_pod_component_member) covers a *third*, heterogeneous shape:
    a member whose array-of-components elements don't all share one struct
    type, so LLZK lowers it to a pod with one @idx_N field per index instead
    of a real !array.type. Unlike the other two cases, @idx_N is always a
    compile-time-literal field name (never a genuine runtime index), so it
    is named "{member}#{idx}" unconditionally — see
    _annotate_idx_pod_component_reads.
    """
    from llzk_dialects.scf import SCFWhile
    from llzk_dialects.pod import PodRead

    ctx.input_pod_to_member.clear()
    ctx.ssa_to_name.clear()

    # --- Part 1: $inputs pod mapping ---
    # Build map: while-result component name -> its initial value name.
    # Handles chains like "%1#1" -> "%0#1" -> "%pod_0". Only ever queried
    # (via trace_source, below) from a top-level struct.writem's own value,
    # so this stays top-level-only -- a nested scf.while's result can only
    # reach that top-level value by first being yielded into its enclosing
    # (already top-level, in every case seen so far) while's own result.
    result_to_init = {}
    for op in body:
        if isinstance(op, SCFWhile):
            for comp_name, (_, init_val) in _while_iter_arg_pairs(op):
                result_to_init[comp_name] = init_val.name

    # (block_arg_name, init_val_name) for every scf.while iter_arg, at ANY
    # nesting depth — the block_arg is the name a loop-carried value is
    # known by *inside* the loop body (e.g. "%arg3"), which is what an
    # array.read/write there actually references, as opposed to the
    # init_val name registered above. See _collect_while_iter_args for why
    # this must be recursive, not top-level-only like result_to_init.
    while_iter_args = []
    _collect_while_iter_args(body, while_iter_args)

    def trace_source(name):
        seen = set()
        while name in result_to_init and name not in seen:
            seen.add(name)
            name = result_to_init[name]
        return name

    for op in body:
        if isinstance(op, StructWritem) and op.types and "_inputs" in op.member_name.name:
            member = op.member_name.name  # "@last1_inputs" ($ already converted to _)
            base = member[1:member.index("_inputs")]
            source = trace_source(op.value.name)
            ctx.input_pod_to_member[source] = base

    # A loop body refers to a loop-carried $inputs array by its block-arg
    # name, not the name it was registered under above — alias it too.
    for block_arg_name, init_val_name in while_iter_args:
        base = ctx.input_pod_to_member.get(trace_source(init_val_name))
        if base is not None:
            ctx.input_pod_to_member[block_arg_name] = base

    # Now that ctx.input_pod_to_member is fully populated, stamp every
    # ArrayRead of a registered "$inputs" array with its semantic name.
    _annotate_input_array_reads(body, ctx, {})

    # --- Part 2: annotate FunctionCall objects with their component member name ---
    # Build pod_ssa -> member_name from top-level struct.writem writes.
    pod_comp_read = {}  # read_result_ssa -> pod_ssa
    for op in body:
        if isinstance(op, PodRead) and op.record_name.name == "@comp":
            pod_comp_read[op._result.name] = op.pod_ref.name

    pod_to_member = {}  # pod_ssa -> member_name
    for op in body:
        if (isinstance(op, StructWritem) and op.types
                and "_inputs" not in op.member_name.name
                and "!struct" in op.types[-1].name):
            pod_var = pod_comp_read.get(op.value.name)
            if pod_var is not None:
                pod_to_member[pod_var] = op.member_name.name[1:]  # strip @

    # --- Part 2b: array-of-component members ---
    # A read of a counting-pod array that backs an array-of-component member
    # is named like a scalar subcomponent: "last#0" (one "#idx" segment per
    # dimension) when every index is a compile-time constant, or the bare
    # base name when any isn't (a read inside a genuine runtime loop, e.g.
    # an scf.while's after-body) — see _annotate_array_component_reads.
    array_member_base = _find_array_component_bases(body)
    if array_member_base:
        # A registered counting array is just as often referenced by an
        # enclosing scf.while's own before/after-region block-arg name, or
        # by an EARLIER sibling while's own result (in a sequential chain
        # of population sites each threading the array through as the
        # next site's own init value), as by whatever name it was
        # originally registered under — alias those too. Unlike Part 1's
        # $inputs-pod resolution (a single forward pass suffices there,
        # since it's purely nested-parent-to-nested-child), this needs a
        # genuine fixpoint: _collect_while_region_array_aliases' pairs can
        # require resolving in EITHER direction depending on whether a
        # while sits inside its "source" or is a later sibling of it — see
        # its own docstring. Bounded by the number of distinct names
        # involved (each iteration adds at least one new key or the loop
        # stops), so this always terminates.
        while_array_aliases = []
        _collect_while_region_array_aliases(body, while_array_aliases)
        changed = True
        while changed:
            changed = False
            for name1, name2 in while_array_aliases:
                base1 = array_member_base.get(name1)
                base2 = array_member_base.get(name2)
                if base1 is not None and base2 is None:
                    array_member_base[name2] = base1
                    changed = True
                elif base2 is not None and base1 is None:
                    array_member_base[name1] = base2
                    changed = True

        _annotate_array_component_reads(body, array_member_base, {}, pod_to_member)

    # --- Part 2c: heterogeneous (idx-pod) array-of-component members ---
    # Every pod.read[@idx_N] of a pod matching one of this struct's own
    # idx-pod component members is named "{member}#{idx}" directly — see
    # _annotate_idx_pod_component_reads.
    if idx_pod_member_types:
        _annotate_idx_pod_component_reads(body, idx_pod_member_types, pod_to_member)

    _annotate_function_calls(body, pod_to_member)

    # --- Part 2d: real traversal order for genuinely-symbolic array
    # population, for signal_renaming.py ---
    # A member left at the bare base name by Part 2b (no single
    # compile-time-known instance) still needs *some* way to attribute each
    # concrete call in llzk_cli's own SMT-level unrolled trace back to the
    # real array index it was called with. See
    # _find_array_component_population_sequences.
    array_component_index_sequences = {}
    if array_member_base:
        array_component_index_sequences = _find_array_component_population_sequences(
            body, array_member_base)

    return array_component_index_sequences


class StructMember(Operation):
    """
    Declare a named member field within a struct.def body.

    Syntax: struct.member @sym_name : $type [attr-dict]
    Attributes:
      sym_name (StringAttr)
      type     (TypeAttr)
      column   (UnitAttr, optional) - marks the member as a column
      signal   (UnitAttr, optional) - marks the member as a signal
      llzk.pub (UnitAttr, optional) - marks the member as an out signal
    Valid parent: StructDefOp
    Interfaces: Symbol, SymbolUserOpInterface
    """

    _OPS = {"struct.member"}

    def __init__(self, sym_name: GlobalVariable, member_type: Type,
                 is_column: bool = False, is_signal: bool = False, is_out: bool = False):
        self.sym_name = sym_name
        self.member_type = member_type
        self.is_column = is_column
        self.is_signal = is_signal
        self.is_out = is_out

    def dialect(self) -> Dialect:
        return Dialect("struct")

    @staticmethod
    def match(line: str) -> bool:
        return line.strip().split()[0] in StructMember._OPS

    @classmethod
    def parse(cls, line: str) -> 'StructMember':
        # struct.member @name : !type [{column, signal}]
        pattern = re.compile(
            r"\s*struct\.member\s+(?P<name>@\S+)\s*:\s*(?P<type>[^{]+?)"
            r"(?:\s*\{(?P<attrs>[^}]*)\})?\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse StructMember: {line}")
        attrs = m["attrs"] or ""
        return StructMember(
            GlobalVariable.parse(m["name"]),
            Type.parse(m["type"].strip()),
            is_column="column" in attrs,
            is_signal="signal" in attrs,
            is_out="llzk.pub" in attrs
        )

    @property
    def operands(self) -> List[SSAVar]:
        return []

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        # Basic transformation: just return the variable itself (should not be used
        # in general on their own)
        yield self.sym_name

    def __repr__(self):
        flags = []
        if self.is_column:
            flags.append("column")
        if self.is_signal:
            flags.append("signal")
        flag_str = f" {{{', '.join(flags)}}}" if flags else ""
        return f"StructMember({self.sym_name} : {self.member_type}{flag_str})"


class StructNew(Operation):
    """
    Create a new instance of a struct type.

    Syntax: %result = struct.new : type($result)
    Result: StructType
    Traits: WitnessGen
    """

    _OPS = {"struct.new"}

    def __init__(self, result: SSAVar, result_type: Type):
        self._result = result
        self.result_type = result_type

    def dialect(self) -> Dialect:
        return Dialect("struct")

    @staticmethod
    def match(line: str) -> bool:
        return line.split('=')[-1].strip().split()[0] in StructNew._OPS

    @classmethod
    def parse(cls, line: str) -> 'StructNew':
        pattern = re.compile(
            r"\s*(?P<res>\S+)\s*=\s*struct\.new\s*:\s*(?P<type>.+)\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse StructNew: {line}")
        return StructNew(SSAVar.parse(m["res"]), Type.parse(m["type"].strip()))

    @property
    def result(self):
        return self._result

    @property
    def operands(self) -> List[SSAVar]:
        return []

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        # Does nothing, we do not care about the creation of the struct itself
        yield from ()

    def __repr__(self):
        return f"StructNew({self._result} = struct.new : {self.result_type})"


class StructReadm(Operation):
    """
    Read the value of a named member from a struct instance.

    Syntax: %val = struct.readm $component [@member_name] : type($component), type($val)
    Attributes: member_name (FlatSymbolRefAttr)
    Operand:    component (StructType)
    Result:     valid LLZK type
    """

    _OPS = {"struct.readm"}

    def __init__(self, result: SSAVar, component: SSAVar,
                 member_name: GlobalVariable, types: List[Type]):
        self._result = result
        self.component = component
        self.member_name = member_name
        self.types = types

    def dialect(self) -> Dialect:
        return Dialect("struct")

    @staticmethod
    def match(line: str) -> bool:
        return line.split('=')[-1].strip().split()[0] in StructReadm._OPS

    @classmethod
    def parse(cls, line: str) -> 'StructReadm':
        pattern = re.compile(
            r"\s*(?P<res>\S+)\s*=\s*struct\.readm\s+(?P<comp>\S+)"
            r"\s*\[\s*(?P<mem>@\S+)\s*\]"
            r"(?:\s*:\s*(?P<types>.+))?\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse StructReadm: {line}")
        types = (
            [Type.parse(t.strip()) for t in split_top_level_commas(m["types"])]
            if m["types"] else []
        )
        return StructReadm(SSAVar.parse(m["res"]), SSAVar.parse(m["comp"]),
                           GlobalVariable.parse(m["mem"]), types)

    @property
    def result(self):
        return self._result

    @property
    def operands(self) -> List[SSAVar]:
        return [self.component]

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        # Members of the struct are handled as plain variables. Hence, reading
        # a field just translates to an assignment. However, the variable might be
        # either a field inside the current struct of or another struct (as a subcomponent).
        # Hence, we separate both cases

        # Defined by the current struct: use just the member name (strip @)
        if f"{ctx.current_template}::" in self.types[0].name:
            assigned_var = SSAVar(self.member_name.name[1:])
        else:
            # The variable corresponds to the component name (a SSAVar) after adding the
            # member currently being accessed
            assigned_var = SSAVar(self.component.name + "_" + self.member_name.name)

        result = translate_assignment_core_with_ctx(self._result, assigned_var,
                                                    self.types[-1], ctx)
        if result:
            yield result

    def __repr__(self):
        type_str = '' if not self.types else ' : ' + ', '.join(repr(t) for t in self.types)
        return (f"StructReadm({self._result} = struct.readm "
                f"{self.component}[{self.member_name}]{type_str})")


class StructWritem(Operation):
    """
    Write a value to a named member of a struct instance.

    Syntax: struct.writem $component [@member_name] = $val : type($component), type($val)
    Attributes: member_name (FlatSymbolRefAttr)
    Operands:   component (StructType), val (valid LLZK type)
    Traits: WitnessGen
    """

    _OPS = {"struct.writem"}

    def __init__(self, component: SSAVar, member_name: GlobalVariable,
                 value: SSAVar, types: List[Type]):
        self.component = component
        self.member_name = member_name
        self.value = value
        self.types = types

    def dialect(self) -> Dialect:
        return Dialect("struct")

    @staticmethod
    def match(line: str) -> bool:
        return line.strip().split()[0] in StructWritem._OPS

    @classmethod
    def parse(cls, line: str) -> 'StructWritem':
        pattern = re.compile(
            r"\s*struct\.writem\s+(?P<comp>\S+)"
            r"\s*\[\s*(?P<mem>@\S+)\s*\]"
            r"\s*=\s*(?P<val>\S+)"
            r"(?:\s*:\s*(?P<types>.+))?\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse StructWritem: {line}")
        types = (
            [Type.parse(t.strip()) for t in split_top_level_commas(m["types"])]
            if m["types"] else []
        )
        return StructWritem(SSAVar.parse(m["comp"]),
                            GlobalVariable.parse(m["mem"]),
                            SSAVar.parse(m["val"]), types)

    @property
    def operands(self) -> List[SSAVar]:
        return [self.component, self.value]

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        # Struct-typed members are ignored (subcomponent assignments are not tracked here).
        if "!struct" in self.types[-1].name:
            return

        # Pod input members ($inputs) are tracked via SSA pod variables in compute;
        # no named signal assignment is needed here.
        if "!pod.type" in self.types[-1].name:
            return

        if f"{ctx.current_template}::" in self.types[0].name:
            assigned_var = SSAVar(self.member_name.name[1:])  # plain name, no prefix
        else:
            assigned_var = SSAVar(self.component.name + "_" + self.member_name.name)

        result = translate_assignment_core_with_ctx(assigned_var, self.value, self.types[-1], ctx)
        if result:
            yield result

    def __repr__(self):
        type_str = '' if not self.types else ' : ' + ', '.join(repr(t) for t in self.types)
        return (f"StructWritem(struct.writem {self.component}"
                f"[{self.member_name}] = {self.value}{type_str})")


class StructDef(BlockOperation):
    """
    Define a circuit component (struct) with members and functions.

    Syntax:
      struct.def @StructName {
        struct.member @field : !type
        function.def @constrain(...) { ... }
        function.def @compute(...) { ... }
      }

    The body is parsed recursively using parse_fn and stored as a list of
    Operation instances (mix of StructMember and FunctionDef).

    Attributes: sym_name (StringAttr)
    Traits: SymbolTable, IsolatedFromAbove, SingleBlock
    Valid parents: ModuleOp, TemplateOp
    """

    _OPS = {"struct.def"}

    def __init__(self, sym_name: GlobalVariable, body: List[Operation]):
        self.sym_name = sym_name
        self.body = body

    def dialect(self) -> Dialect:
        return Dialect("struct")

    @staticmethod
    def match(line: str) -> bool:
        return line.strip().split()[0] in StructDef._OPS

    @classmethod
    def parse(cls, lines: List[str], cursor: int,
              parse_fn: ParseFn) -> Tuple['StructDef', int]:
        header = lines[cursor]
        # struct.def @Name {
        pattern = re.compile(r"\s*struct\.def\s+(?P<name>@\S+)\s*\{")
        m = re.match(pattern, header)
        if not m:
            raise ValueError(f"Failed to parse StructDef header: {header}")

        depth = header.count('{') - header.count('}')
        end = cursor
        while depth > 0 and end + 1 < len(lines):
            end += 1
            depth += lines[end].count('{') - lines[end].count('}')

        body = parse_fn(cursor + 1, end)
        return StructDef(GlobalVariable.parse(m["name"]), body), end + 1

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        # Implementation of the definition of a struct. It can have multiple members defined
        # and functions. They are handled as follows:
        #  * Members: members with llzk.pub are assumed out signals, otherwise they are intermediate
        #  * Functions: we just process function @compute.
        # We use isinstance because we need to store the function information in TranslationContext

        compute_op, in_args_with_type, out_args_with_type, _ = self._compute_core_function_info_from_struct()

        # There must be at least one compute
        assert compute_op is not None, "There is no @compute element in the struct"

        # The name to refer to the current function is @poly_template::@struct_def@compute
        # To identify subcalls in subcomponents, we store this convention
        llzk_name = f"{ctx.current_template}::{self.sym_name.name}::@compute"

        # The name we give is just the sym_name
        core_name = self.sym_name.name

        # Assign the information of the name of the function, in/out args to the context information
        ctx.llzk_func2core[llzk_name] = core_name
        ctx.core_func2args[core_name] = in_args_with_type, out_args_with_type
        ctx.current_core_function = core_name

        # Record subcomponent members (struct-typed) for this function.
        # A direct struct member adds one entry; an array-of-structs member
        # expands into one "#i" (or, for an N-D array, "#i1#i2#...") entry
        # per element, 0-indexed per dimension.
        subcomponent_members = {}
        # Heterogeneous array-of-components members: member_name ->
        # {@idx_N: struct Type}, populated below and fed into the naming
        # pre-pass (see _is_idx_pod_component_member).
        idx_pod_member_types: Dict[str, Dict[str, Type]] = {}
        for op in self.body:
            if not isinstance(op, StructMember):
                continue
            type_str = op.member_type.name
            member_name = op.sym_name.name[1:]  # strip leading @
            # Checked first, and unconditionally `continue`s on a match, so
            # this never falls into the "!struct.type" substring check below
            # -- a pod's field textually containing "!struct.type" (as an
            # idx-pod's own @idx_N fields do) would otherwise wrongly match
            # it, per the same anchoring pitfall documented in DECISIONS.md
            # §19/§21/§22.
            idx_fields = _is_idx_pod_component_member(type_str)
            if idx_fields is not None:
                idx_pod_member_types[member_name] = idx_fields
                continue
            if "!struct.type" not in type_str:
                continue
            full_ref = struct_type_name(type_str)
            referred = full_ref.split("::")[-1]
            dims = array_dimensions(type_str)
            if dims:
                for combo in itertools.product(*(range(d) for d in dims)):
                    suffix = "".join(f"#{i}" for i in combo)
                    subcomponent_members[f"{member_name}{suffix}"] = referred
            else:
                subcomponent_members[member_name] = referred
        if subcomponent_members:
            ctx.member_to_struct[core_name] = subcomponent_members

        # Pre-pass: build naming maps so calls use semantic signal names.
        # Also returns, for a member left at its bare name (no single
        # compile-time-known instance), the real array-index traversal
        # order its population loop(s) actually visit -- exported below for
        # signal_renaming.py, since a bare-named call's own concrete
        # instance can only be recovered from llzk_cli's own SMT-level
        # execution trace, not from this translator's emitted .core text.
        array_component_index_sequences = _build_component_naming_maps(
            compute_op.body, ctx, idx_pod_member_types)
        if array_component_index_sequences:
            ctx.array_component_index_sequences[core_name] = array_component_index_sequences

        # After setting the translation, we just need to render the function
        # considering the out arguments we have generated
        yield from compute_op.to_core(ctx)

        # Clear per-function naming maps
        ctx.input_pod_to_member.clear()
        ctx.ssa_to_name.clear()
        ctx.current_core_function = None

    def _compute_core_function_info_from_struct(self) -> Tuple[Operation, List[Tuple[str, Type]], List[Tuple[str, Type]], List[Tuple[str, Type]]]:
        """
        Returns the operation corresponding to @compute, and the input and output arguments
        and the intermediate signals, following the format (var_name, core_type). For instance, [(%a, ff), (%b, arr<3>)].
        """

        # As part of translating a struct, we store the corresponding information of
        # the core function
        in_args_with_type = []
        out_args_with_type = []
        intermediate_signals = []
        compute_op = None

        # We need to obtain the information from the struct
        for operation in self.body:
            if isinstance(operation, StructMember):
                # Only traverse operations that are symbolic
                is_out = operation.is_out
                core_repr, core_type = operation.sym_name.name, operation.member_type

                if is_out:
                    out_args_with_type.append((core_repr, core_type))
                else:
                    intermediate_signals.append((core_repr, core_type))

            # Only consider the @compute function, others are ignored
            elif isinstance(operation, FunctionDef) and operation.sym_name.name == "@compute":
                assert compute_op is None, "There are two @compute functions defined in a struct"
                # We wait for the translation after all the structMembers have been parsed
                # (not sure if the order is guaranteed by construction)
                compute_op = operation

                # The complete in args
                in_args_with_type = operation.in_args

        return compute_op, in_args_with_type, out_args_with_type, intermediate_signals

    def __repr__(self):
        body_str = '\n  '.join(repr(op) for op in self.body)
        return f"StructDef({self.sym_name} {{\n  {body_str}\n}})"


class StructDialect(Dialect):
    """Registry for all struct dialect operations."""

    def __init__(self):
        super().__init__("struct")
        self.register(StructMember)
        self.register(StructNew)
        self.register(StructReadm)
        self.register(StructWritem)
        # StructDef is a BlockOperation; dispatched separately by LLZKParser
        self.register(StructDef)
