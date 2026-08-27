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
from llzk_dialects.core import Operation, SSAVar, Type, TranslationContext
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


