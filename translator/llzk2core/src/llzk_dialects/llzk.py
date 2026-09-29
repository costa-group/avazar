"""
LLZK core dialect — core LLZK-specific constructs.
Prefix: llzk.

Operations:
  LLZKNondet — llzk.nondet (declares an uninitialized / non-deterministic variable)

Top-level wrapper:
  ModuleOp   — represents the 'module attributes {...} { ... }' header; holds
               llzk.lang and llzk.main and owns the top-level body operations.
               Created directly by LLZKParser.parse(), not via dialect dispatch.

Attributes (represented as type annotations, not parsed independently):
  LoopBoundsAttr — #llzk.loopbounds<lower to upper step step>
  PublicAttr     — #llzk.pub  (marks circuit inputs/outputs as public)
"""

import re
from typing import Dict, Iterator, List, Optional, Set, Tuple, TYPE_CHECKING, Generator
from llzk_dialects.core import Operation, SSAVar, Type, TranslationContext, GlobalVariable
from llzk_dialects.definitions import Dialect
from llzk_dialects.utils import is_array_type, array_total_size
from llzk_dialects.core_utils import signature_args, invocation_args

if TYPE_CHECKING:
    pass  # avoid circular imports


def _collect_function_calls(ops: List[Operation]) -> 'Iterator':
    """
    Recursively yield every FunctionCall found in ops, descending into
    nested block bodies the same way scf.py's _collect_result_names does
    (explicit per-class checks for the shapes with more than one body
    list, falling back to a generic 'body' attribute) -- a pure function's
    own call(s) to another pure function may be nested inside scf.if/for/
    while, not just at the top level of its own body.
    """
    from llzk_dialects.function import FunctionCall
    from llzk_dialects.scf import SCFIf, SCFFor, SCFWhile, SCFExecuteRegion

    for op in ops:
        if isinstance(op, FunctionCall):
            yield op
        if isinstance(op, SCFIf):
            yield from _collect_function_calls(op.then_body)
            if op.else_body:
                yield from _collect_function_calls(op.else_body)
        elif isinstance(op, SCFFor):
            yield from _collect_function_calls(op.body)
        elif isinstance(op, SCFWhile):
            yield from _collect_function_calls(op.before_body)
            yield from _collect_function_calls(op.after_body)
        elif isinstance(op, SCFExecuteRegion):
            yield from _collect_function_calls(op.body)
        elif hasattr(op, 'body'):
            yield from _collect_function_calls(op.body)


def _topo_sort_pure_functions(entries: 'List[Tuple["PolyTemplate", str, "FunctionDef"]]') -> 'List["PolyTemplate"]':
    """
    Topologically sort pure-function poly.template's by their own call
    graph (a pure function may call another pure function declared later
    in the source -- e.g. sha256_2_test_concrete.mlir's ssigma1_1 calls
    rrot_8, declared afterwards), so that every callee's def text is
    emitted before any call to it, however many levels deep the chain
    goes.

    entries: (template_op, llzk_name, func_def) triples, in original file
    order. Visits entries in that order and recurses into dependencies
    first (DFS), so a pair with no dependency between them keeps its
    original relative order -- only real forward references cause
    reordering. Raises ValueError on a dependency cycle (mutual recursion
    among pure functions isn't supported).
    """
    name2template = {name: template for template, name, _ in entries}
    name2deps: Dict[str, Set[str]] = {}
    for _template, name, func_def in entries:
        known = set(name2template)
        name2deps[name] = {
            call.callee.name for call in _collect_function_calls(func_def.body)
            if call.callee.name in known
        }

    sorted_names: List[str] = []
    visited: Set[str] = set()
    visiting: Set[str] = set()

    def visit(name: str) -> None:
        if name in visited:
            return
        if name in visiting:
            raise ValueError(
                f"Cycle detected among pure function templates involving {name!r}: "
                "mutual recursion is not supported"
            )
        visiting.add(name)
        for dep in name2deps[name]:
            visit(dep)
        visiting.discard(name)
        visited.add(name)
        sorted_names.append(name)

    for _template, name, _func_def in entries:
        visit(name)

    return [name2template[name] for name in sorted_names]


def _collect_while_loops(ops: List[Operation]) -> 'Iterator':
    """
    Recursively yield every SCFWhile found in ops, same recursive-descent
    shape as _collect_function_calls -- a pure function's own while loop
    may be nested inside an outer scf.if/for/while, not just at the top
    level of its own body.

    scf.for is deliberately not covered here: no real example has a
    for-loop bound depending on a pure function's own parameter (its
    to_core already requires a concrete lb/ub, so that shape would already
    fail loudly rather than silently), and speculative coverage isn't
    warranted (see llzk2core's DECISIONS.md philosophy on this).
    """
    from llzk_dialects.scf import SCFIf, SCFFor, SCFWhile, SCFExecuteRegion

    for op in ops:
        if isinstance(op, SCFWhile):
            yield op
            yield from _collect_while_loops(op.before_body)
            yield from _collect_while_loops(op.after_body)
        elif isinstance(op, SCFIf):
            yield from _collect_while_loops(op.then_body)
            if op.else_body:
                yield from _collect_while_loops(op.else_body)
        elif isinstance(op, SCFFor):
            yield from _collect_while_loops(op.body)
        elif isinstance(op, SCFExecuteRegion):
            yield from _collect_while_loops(op.body)
        elif hasattr(op, 'body'):
            yield from _collect_while_loops(op.body)


def _build_ops_var2expression(ops: List[Operation]) -> 'Dict[str, object]':
    """
    Maps every SSA name defined by a single-result operation in ops (or
    nested inside it, recursing the same way _collect_function_calls does)
    to the operation that defines it -- a flat forward map suitable for
    core_utils.construct_function_from_expressions to walk backward from
    any SSA name used within these ops to the constant (or unresolvable)
    expression that produced it.

    Unlike scf.py's SCFWhile._process_while_variables (which only tracks
    variables transitively relevant to one specific target, discovered via
    a backward prune from a while condition), this maps every op's result
    unconditionally -- appropriate here since the target name (a while's
    own init-arg initial value, or a function.call's own argument) isn't
    known in advance. A multi-result op (e.g. a nested scf.while's own
    result) is deliberately left unmapped: construct_function_from_expressions
    correctly raises a KeyError if such a value is ever referenced
    directly, rather than silently mis-resolving it.
    """
    from llzk_dialects.scf import SCFIf, SCFFor, SCFWhile, SCFExecuteRegion

    var2expression = {}
    for op in ops:
        result = getattr(op, 'result', None)
        if result is not None:
            var2expression[result.name] = op

        if isinstance(op, SCFIf):
            var2expression.update(_build_ops_var2expression(op.then_body))
            if op.else_body:
                var2expression.update(_build_ops_var2expression(op.else_body))
        elif isinstance(op, SCFFor):
            var2expression.update(_build_ops_var2expression(op.body))
        elif isinstance(op, SCFWhile):
            var2expression.update(_build_ops_var2expression(op.before_body))
            var2expression.update(_build_ops_var2expression(op.after_body))
        elif isinstance(op, SCFExecuteRegion):
            var2expression.update(_build_ops_var2expression(op.body))
        elif hasattr(op, 'body'):
            var2expression.update(_build_ops_var2expression(op.body))
    return var2expression


def _resolve_constant(var: SSAVar, var2expression: 'Dict[str, object]') -> Optional[int]:
    """
    Attempts to fold var down to a concrete Python int using the existing
    core_utils.construct_function_from_expressions evaluator (the same one
    while-bound resolution already uses, called with a dummy input since a
    pure-constant expression tree ignores it -- see core_utils.py's own
    `bound_func(0)` convention). Returns None whenever the chain bottoms
    out at something with no var2expression entry (e.g. an array.read, an
    llzk.nondet, or an external parameter with no further alias) or an
    operation with no to_function() implementation -- i.e. "not a
    compile-time constant here", not an error.
    """
    from llzk_dialects.core_utils import construct_function_from_expressions

    try:
        return construct_function_from_expressions(var, var2expression, set())(0)
    except (KeyError, NotImplementedError, AttributeError):
        return None


def _collect_calling_function_defs(module_body: List[Operation]) -> 'List["FunctionDef"]':
    """
    Every FunctionDef in the module that can itself contain a
    function.call: a pure function's own body, plus every struct's
    @compute and @constrain (struct.py's StructDef.body is a flat mix of
    StructMember and FunctionDef children).
    """
    from llzk_dialects.function import FunctionDef
    from llzk_dialects.poly import PolyTemplate
    from llzk_dialects.struct import StructDef

    defs = []
    for operation in module_body:
        if not isinstance(operation, PolyTemplate) or len(operation.body) != 1:
            continue
        child = operation.body[0]
        if isinstance(child, FunctionDef):
            defs.append(child)
        elif isinstance(child, StructDef):
            defs.extend(op for op in child.body if isinstance(op, FunctionDef))
    return defs


def _parametric_params_for_while(while_op: 'SCFWhile', in_arg_names: Set[str]) -> Set[str]:
    """
    A while loop is "loop-bound-parametric" on the subset of in_arg_names
    its own condition transitively references but never defines -- exactly
    the situation core_utils.py's SymbolicSteps fallback already detects,
    specialized to the case where the unresolved name is one of the
    enclosing function's own parameters (rather than some other external
    value core_utils.py can't identify).
    """
    from llzk_dialects.core_utils import _collect_free_var_names

    var2expression, condition_var = while_op._build_while_var_expressions()
    free_names = _collect_free_var_names(condition_var, var2expression, set())
    return free_names & in_arg_names


def _specialize_loop_bound_parametric_pure_functions(
        pure_function_entries: 'List[Tuple["PolyTemplate", str, "FunctionDef"]]',
        module_body: List[Operation], ctx: TranslationContext) -> None:
    """
    For every pure function whose own while-loop bound depends on one of
    its own parameters (e.g. EscalarMulW4Table_0's `arg3 < arg1*4`, "k" =
    arg1 -- escalarmulw4table_concrete.mlir and 6 sibling files), resolves
    every call site across the whole module and, when every one of them
    passes a compile-time-constant value for the relevant parameter(s),
    clones the function body once per distinct constant value/tuple
    actually used, redirecting each call site to its own clone. This lets
    the existing, unmodified concrete-bound resolution in
    core_utils.py's _resolve_comparison_recurrence produce a real integer
    `repeat` count instead of a `SymbolicSteps` formula llzk_cli's own
    symbolic execution can't run (`Variable '%steps_N' is a symbolic`).

    A function is left entirely unspecialized -- today's unchanged
    behavior -- the moment any single call site's relevant argument fails
    to resolve to a concrete int (e.g. pointbits_loopback_concrete.mlir's
    sqrt_0, whose parameter traces back to a genuine runtime witness
    signal, never a constant), or when it has no loop-bound-parametric
    while at all.
    """
    callers = _collect_calling_function_defs(module_body)

    for template, llzk_name, func_def in pure_function_entries:
        in_arg_names = {name for name, _ in func_def.in_args}

        parametric_params: Set[str] = set()
        for while_op in _collect_while_loops(func_def.body):
            parametric_params |= _parametric_params_for_while(while_op, in_arg_names)
        if not parametric_params:
            continue

        # Deterministic order, matching in_args' own declaration order.
        param_order = [name for name, _ in func_def.in_args if name in parametric_params]
        param_index = {name: i for i, (name, _) in enumerate(func_def.in_args)}

        resolved_calls: 'List[Tuple[FunctionCall, Tuple[int, ...]]]' = []
        aborted = False
        for caller in callers:
            calls = [c for c in _collect_function_calls(caller.body) if c.callee.name == llzk_name]
            if not calls:
                continue
            caller_map = _build_ops_var2expression(caller.body)
            for call in calls:
                values = []
                for name in param_order:
                    value = _resolve_constant(call.args[param_index[name]], caller_map)
                    if value is None:
                        aborted = True
                        break
                    values.append(value)
                if aborted:
                    break
                resolved_calls.append((call, tuple(values)))
            if aborted:
                break

        if aborted or not resolved_calls:
            continue

        distinct_value_tuples = sorted({values for _call, values in resolved_calls})
        core_base = func_def.sym_name.name  # e.g. "@EscalarMulW4Table_0"
        arg_display_names = func_def.in_arg_names

        def _clone_name(values: 'Tuple[int, ...]') -> str:
            if len(distinct_value_tuples) == 1:
                return core_base
            suffix = "".join(
                f"__{arg_display_names.get(name, name.lstrip('%'))}{value}"
                for name, value in zip(param_order, values)
            )
            return f"{core_base}{suffix}"

        in_args, out_args = ctx.core_func2args[core_base]
        specializations = []
        value_tuple_to_clone_name = {}
        for values in distinct_value_tuples:
            clone_name = _clone_name(values)
            value_tuple_to_clone_name[values] = clone_name
            seed = dict(zip(param_order, values))
            specializations.append((clone_name, seed))

            clone_llzk_name = f"{template.sym_name.name}::{clone_name}"
            ctx.llzk_func2core[clone_llzk_name] = clone_name
            ctx.core_func2args[clone_name] = (in_args, out_args)

        ctx.pure_function_specializations[llzk_name] = specializations

        for call, values in resolved_calls:
            call.callee = GlobalVariable(f"{template.sym_name.name}::{value_tuple_to_clone_name[values]}")


class ModuleOp:
    """
    Top-level LLZK module.

    Wraps all top-level operations and carries the module-level attributes:
      llzk.lang        — unit attribute marking this as an LLZK program
      llzk.main        — struct type of the circuit entry point

    Syntax of the header line:
      module attributes {llzk.lang, llzk.main = !struct.type<@Name::@Name<[]>>} {

    Created by LLZKParser.parse() when the input starts with 'module'; not
    dispatched through the dialect registration system.
    """

    def __init__(self, lang: bool, main_type: Optional[Type],
                 body: List[Operation]):
        self.lang = lang
        # The struct type that acts as the circuit entry point, or None if absent.
        self.main_type = main_type
        self.body = body

    @classmethod
    def parse_header(cls, header: str) -> 'tuple[bool, Optional[Type]]':
        """
        Extract llzk.lang and llzk.main from a module attributes line.
        Returns (lang_present, main_type_or_None).
        """
        lang = "llzk.lang" in header
        main_type = None
        # llzk.main = <type>, where <type> ends at the next ',' or '}'
        # at the top level (the type itself may contain '<', '>', '[', ']').
        m = re.search(r'llzk\.main\s*=\s*([^,}]+)', header)
        if m:
            main_type = Type.parse(m.group(1).strip())
        return lang, main_type

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        """
        This translates a whole module. It needs to translate the complete body and then add
        the main function to invoke directly the template regarding llzk.main
        """
        # Pre-pass: register every "pure function" template's signature (see
        # poly.py's _register_pure_function) before any body is translated.
        # Unlike struct-to-struct calls (which this codebase already requires
        # to be declared before their callers, matching every prior example),
        # a pure function may be called by a template declared earlier in the
        # file (e.g. escalarmulw4table_concrete.mlir's EscalarMulW4Table_0,
        # translated first, calls pointAdd_1, declared afterwards).
        # Registration only reads the already-fully-parsed FunctionDef itself
        # (signature + its own function.return), with no dependency on any
        # other function being registered first, so a single unordered scan
        # is enough to register every signature.
        #
        # Registering the signature is only enough to make a *call* resolve,
        # though -- it says nothing about the *def*'s own text position in
        # the output. A pure function may also call another pure function
        # declared later in the file (e.g. sha256_2_test_concrete.mlir's
        # ssigma1_1 calls rrot_8, declared afterwards) -- a real,
        # potentially multi-level dependency chain. So every pure-function
        # template is hoisted to the front of the emitted output, in
        # topologically-sorted order (_topo_sort_pure_functions), ahead of
        # every other top-level item (structs etc., which keep their
        # existing relative order -- nothing depends on a pure function's
        # textual position relative to a struct, only on it existing before
        # any call to it).
        from llzk_dialects.poly import PolyTemplate, _register_pure_function
        from llzk_dialects.function import FunctionDef
        from llzk_dialects.global_ import GlobalDef, _register_global_def

        pure_function_entries = []
        for operation in self.body:
            if (isinstance(operation, PolyTemplate) and len(operation.body) == 1
                    and isinstance(operation.body[0], FunctionDef)):
                func_def = operation.body[0]
                _register_pure_function(func_def, operation.sym_name.name, ctx)
                llzk_name = f"{operation.sym_name.name}::{func_def.sym_name.name}"
                pure_function_entries.append((operation, llzk_name, func_def))
            if isinstance(operation, GlobalDef):
                # global.def is only ever a direct child of ModuleOp, and may
                # textually appear AFTER the struct that reads it (module-level
                # symbols, not SSA, don't need to be defined before use) -- see
                # global_.py's _register_global_def docstring.
                _register_global_def(operation, ctx)

        sorted_pure_templates = _topo_sort_pure_functions(pure_function_entries)

        # Specialize any pure function whose own while-loop bound depends
        # on one of its own parameters, when that parameter is a
        # compile-time constant at every one of its call sites (see
        # _specialize_loop_bound_parametric_pure_functions). Runs after
        # topo-sort deliberately: topo-sort orders on the *original*,
        # unspecialized call graph -- a pure function's dependency on
        # another pure function doesn't change just because the callee
        # later gets cloned, and specialization only relabels which
        # concrete def a call site ends up targeting.
        _specialize_loop_bound_parametric_pure_functions(pure_function_entries, self.body, ctx)

        pure_templates = {template for template, _name, _func_def in pure_function_entries}
        emission_order = sorted_pure_templates + [
            operation for operation in self.body if operation not in pure_templates
        ]

        # Yield operation by operation
        for operation in emission_order:
            yield from operation.to_core(ctx)
        yield from self._yield_main_function(ctx)

    def _yield_main_function(self, ctx: TranslationContext) -> Generator[str, None, None]:
        """
        Generates the main function at the end of the core program, that serves
        as the entry point
        """
        # We need to transform the llzk.main argument into the expected format.
        # For instance, '!struct.type<@BinaryAdd_0::@BinaryAdd_0<[]>>' should be
        # transformed to the llzk name @BinaryAdd_0::@BinaryAdd_0::@compute
        possible_components = [component for component in self.main_type.name.split("<") if "::" in component]
        assert len(possible_components) == 1, "Error identifying the main function: " \
                                              "there should be exactly one component with ::"
        llzk_name = possible_components[0] + "::@compute"

        # Finally, yield the main function from the args we have retrieved
        core_function = ctx.llzk_func2core[llzk_name]
        in_args, out_args = ctx.core_func2args[core_function]

        # Strip @ prefix from output arg names (consistent with function body naming)
        plain_out_args = [(n[1:] if n.startswith('@') else n, t) for n, t in out_args]

        # For declaring the main function
        joined_in_args_with_type = signature_args(in_args)
        joined_out_args_with_type = signature_args(plain_out_args)

        # For invoking the function
        joined_in_args = invocation_args(in_args)
        joined_out_args = invocation_args(plain_out_args)

        yield f"""
            def main({joined_in_args_with_type}) -> {joined_out_args_with_type} {{
                call {core_function}({joined_in_args}) to {joined_out_args}
            }}
        """

    def __repr__(self):
        lang_str = "llzk.lang, " if self.lang else ""
        main_str = f"llzk.main = {self.main_type}" if self.main_type else ""
        attrs = lang_str + main_str
        body_str = "\n  ".join(repr(op) for op in self.body)
        return f"ModuleOp(module attributes {{{attrs}}} {{\n  {body_str}\n}})"


class LLZKNondet(Operation):
    """
    Declare an uninitialized (non-deterministic) variable.

    In ZK circuits, a non-deterministic variable is one whose value is
    provided by the prover and must later be constrained to be correct.

    Syntax: %result = llzk.nondet : type($res)
    Result: any valid LLZK type
    Interfaces: OpAsmOpInterface
    """

    _OPS = {"llzk.nondet"}

    def __init__(self, result: SSAVar, result_type: Type):
        self._result = result
        self.result_type = result_type

    def dialect(self) -> Dialect:
        return Dialect("llzk")

    @staticmethod
    def match(line: str) -> bool:
        return line.split('=')[-1].strip().split()[0] in LLZKNondet._OPS

    @classmethod
    def parse(cls, line: str) -> 'LLZKNondet':
        pattern = re.compile(
            r"\s*(?P<res>\S+)\s*=\s*llzk\.nondet\s*:\s*(?P<type>.+)\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse LLZKNondet: {line}")
        return LLZKNondet(SSAVar.parse(m["res"]), Type.parse(m["type"].strip()))

    @property
    def result(self):
        return self._result

    @property
    def operands(self) -> List[SSAVar]:
        return []

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        # A non-deterministic value has no operand to derive an initial value
        # from, so it just gets a defined placeholder (0, or an array of
        # zeros) for downstream code to read before it's actually constrained.
        #
        # Anchored to the outermost type (startswith, not a plain "in"
        # substring check) for the same reason as is_array_type itself: an
        # array of felt (e.g. "!array.type<3 x !felt.type<...>>>") contains
        # "!felt.type" as a substring too, so an unanchored check would wrongly
        # take the scalar branch for it instead of the array one.
        type_name = self.result_type.name
        if type_name.strip().startswith("!felt.type"):
            yield f"{self._result.name} = 0"
        elif is_array_type(type_name):
            array_dim = array_total_size(type_name)
            yield f"array.new {array_dim} {self._result.name}"
        elif type_name.strip().startswith("!pod.type"):
            # A pod-typed nondet value has no operand of its own (unlike
            # pod.new) to derive its fields' values from -- treat every
            # field as if pod.new had been given no initial value for it,
            # recursing through nested pod fields (pod-in-pod) the same way.
            from llzk_dialects.pod import register_and_allocate_pod
            yield from register_and_allocate_pod(ctx, self._result.name, type_name)
        else:
            raise NotImplementedError(
                f"llzk.nondet transformation for not recognized expression: {type_name}"
            )

    def __repr__(self):
        return f"LLZKNondet({self._result} = llzk.nondet : {self.result_type})"


class LLZKDialect(Dialect):
    """Registry for all llzk dialect operations."""

    def __init__(self):
        super().__init__("llzk")
        self.register(LLZKNondet)


