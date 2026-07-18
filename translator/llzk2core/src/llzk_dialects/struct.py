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

import re
from typing import List, Optional, Tuple, Generator

from llzk_dialects.core import (
    Operation, BlockOperation, SSAVar, GlobalVariable, Type,
    TranslationContext, ParseFn,
)
from llzk_dialects.definitions import Dialect
from llzk_dialects.function import FunctionDef
from llzk_dialects.utils import split_top_level_commas, struct_type_name
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
    from llzk_dialects.arith import ArithConst
    from llzk_dialects.cast import CastToIndex, CastToFelt

    const_map = {}
    for op in ops:
        if isinstance(op, FeltConst):
            const_map[op.result.name] = op.constant
        elif isinstance(op, ArithConst):
            const_map[op.result.name] = int(op.value)
        elif isinstance(op, (CastToIndex, CastToFelt)):
            value = const_map.get(op.value.name)
            if value is not None:
                const_map[op.result.name] = value
    return const_map


def _find_array_component_bases(body):
    """
    Detect array-of-component members: a struct member holding an array of
    subcomponents (e.g. "@last : !array.type<2 x !struct.type<...>>") is
    populated, at the end of compute, by a bulk-copy scf.for loop that reads
    each "counting pod" array element's @comp field (the just-computed
    subcomponent) and writes it into the array that is then struct-written
    into that member.

    Returns a dict mapping the counting-pod array's own SSA name to the
    member's base name (no @), so a later constant-indexed read of that
    counting array (see _build_component_naming_maps) can be attributed to
    a specific component instance, e.g. "last_0".
    """
    from llzk_dialects.scf import SCFFor
    from llzk_dialects.pod import PodRead
    from llzk_dialects.array import ArrayRead, ArrayWrite

    # target array SSA (the array-of-struct member's value) -> counting array SSA
    target_to_counting = {}
    for op in body:
        if not isinstance(op, SCFFor):
            continue
        # array.read result -> counting array ssa, restricted to reads
        # indexed by this loop's own induction variable
        comp_reads = {
            inner._result.name: inner.arr_ref.name
            for inner in op.body
            if isinstance(inner, ArrayRead)
            and len(inner.indices) == 1 and inner.indices[0].name == op.iv.name
        }
        # pod.read(@comp) result -> counting array ssa
        comp_vals = {}
        for inner in op.body:
            if isinstance(inner, PodRead) and inner.record_name.name == "@comp":
                counting_arr = comp_reads.get(inner.pod_ref.name)
                if counting_arr is not None:
                    comp_vals[inner._result.name] = counting_arr
        for inner in op.body:
            if (isinstance(inner, ArrayWrite) and len(inner.indices) == 1
                    and inner.indices[0].name == op.iv.name):
                counting_arr = comp_vals.get(inner.rvalue.name)
                if counting_arr is not None:
                    target_to_counting[inner.arr_ref.name] = counting_arr

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

      - "{base}_{idx}" when the index resolves to a compile-time constant
        (via a local constant fold — const_map carries constants folded in
        enclosing scopes down into this one, without leaking sideways
        between sibling branches that may reuse the same SSA names, e.g.
        two scf.for loops in the same function both using "%arg1" as their
        induction variable).
      - the bare "{base}" when it doesn't — the read sits inside a genuine
        runtime loop (e.g. an scf.while's after-body), so there is no
        single instance to name; the caller reconstructs per-iteration
        names (e.g. "{base}_0") externally, from a symbolic execution of
        the emitted repeat loop.

    _annotate_function_calls then picks up these entries exactly like the
    scalar-subcomponent ones already in pod_to_member.
    """
    from llzk_dialects.array import ArrayRead

    local_const_map = dict(const_map)
    local_const_map.update(_fold_index_constants(ops))

    for op in ops:
        if (isinstance(op, ArrayRead) and len(op.indices) == 1
                and op.arr_ref.name in array_member_base):
            base = array_member_base[op.arr_ref.name]
            idx_val = local_const_map.get(op.indices[0].name)
            pod_to_member[op._result.name] = f"{base}_{idx_val}" if idx_val is not None else base

        for attr in ('body', 'then_body', 'else_body', 'before_body', 'after_body'):
            sub = getattr(op, attr, None)
            if sub:
                _annotate_array_component_reads(sub, array_member_base, local_const_map, pod_to_member)


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
    instance instead of leaving it as the bare member name.
    """
    from llzk_dialects.array import ArrayRead

    local_const_map = dict(const_map)
    local_const_map.update(_fold_index_constants(ops))

    for op in ops:
        if isinstance(op, ArrayRead) and len(op.indices) == 1:
            member = ctx.input_pod_to_member.get(op.arr_ref.name)
            if member is not None:
                idx_val = local_const_map.get(op.indices[0].name)
                op._semantic_base = f"{member}_{idx_val}" if idx_val is not None else member

        for attr in ('body', 'then_body', 'else_body', 'before_body', 'after_body'):
            sub = getattr(op, attr, None)
            if sub:
                _annotate_input_array_reads(sub, ctx, local_const_map)


def _build_component_naming_maps(body, ctx):
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
    array — "last_0" for a compile-time-constant index (matching a scalar
    subcomponent's own naming), or the bare base name ("Num2Bits_16_325")
    when the read sits inside a genuine runtime loop (index not constant),
    so the caller can later reconstruct per-iteration names externally
    (e.g. "Num2Bits_16_325_0") from a symbolic execution of the repeat loop.
    """
    from llzk_dialects.scf import SCFWhile
    from llzk_dialects.pod import PodRead

    ctx.input_pod_to_member.clear()
    ctx.ssa_to_name.clear()

    # --- Part 1: $inputs pod mapping ---
    # Build map: while-result component name -> its initial value name.
    # Handles chains like "%1#1" -> "%0#1" -> "%pod_0".
    result_to_init = {}
    # (block_arg_name, init_val_name) for every scf.while iter_arg — the
    # block_arg is the name a loop-carried value is known by *inside* the
    # loop body (e.g. "%arg3"), which is what an array.read/write there
    # actually references, as opposed to the init_val name registered below.
    while_iter_args = []
    for op in body:
        if isinstance(op, SCFWhile):
            flat_results = []
            for res in op.results:
                for k in range(res.n_components):
                    flat_results.append(res.to_core_component(k))
            for comp_name, (block_arg, init_val) in zip(flat_results, op.init_args):
                result_to_init[comp_name] = init_val.name
                while_iter_args.append((block_arg.name, init_val.name))

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
    # is named like a scalar subcomponent: "last_0" when the index is a
    # compile-time constant, or the bare base name when it isn't (a read
    # inside a genuine runtime loop, e.g. an scf.while's after-body — there
    # is no single instance to name here, so the caller reconstructs
    # per-iteration names externally).
    array_member_base = _find_array_component_bases(body)
    if array_member_base:
        _annotate_array_component_reads(body, array_member_base, {}, pod_to_member)

    _annotate_function_calls(body, pod_to_member)


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
        # expands into N numbered entries (1-indexed).
        subcomponent_members = {}
        for op in self.body:
            if not isinstance(op, StructMember):
                continue
            type_str = op.member_type.name
            if "!struct.type" not in type_str:
                continue
            member_name = op.sym_name.name[1:]  # strip leading @
            full_ref = struct_type_name(type_str)
            referred = full_ref.split("::")[-1]
            arr_m = re.search(r"!array\.type<\s*(\d+)\s+x\s+!struct\.type<", type_str)
            if arr_m:
                for i in range(1, int(arr_m.group(1)) + 1):
                    subcomponent_members[f"{member_name}{i}"] = referred
            else:
                subcomponent_members[member_name] = referred
        if subcomponent_members:
            ctx.member_to_struct[core_name] = subcomponent_members

        # Pre-pass: build naming maps so calls use semantic signal names
        _build_component_naming_maps(compute_op.body, ctx)

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
