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
from llzk_dialects.core import Operation, BlockOperation, ParseFn, SSAVar, Type, TranslationContext, GlobalVariable
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

    return _topo_sort_templates(
        [name for _template, name, _func_def in entries], name2template, name2deps,
        "pure function templates", "mutual recursion is not supported")


_STRUCT_TYPE_TEMPLATE_RE = re.compile(r'!struct\.type<(@[^:<>\s]+)::')


def _struct_template_deps(template_name: str, struct_def: 'StructDef',
                          known_template_names: Set[str]) -> Set[str]:
    """
    The other struct templates a struct template depends on: every
    template it names as a subcomponent's own struct type in a member
    declaration (a direct member, an array of components, or an idx-pod's
    own @idx_N fields), plus every template whose @compute/@constrain it
    calls. Either one alone is not enough to be safe -- translating the
    caller's @compute already needs the callee's registered signature at
    the very first pod.new whose type mentions it (array.py's
    _struct_out_args), well before the function.call itself
    (isequal_concrete.mlir's IsEqual_1 -> IsZero_0).

    Self-references (a struct's own type in its own @compute signature,
    struct.new, etc.) and names outside known_template_names are dropped.
    """
    from llzk_dialects.function import FunctionDef
    from llzk_dialects.struct import StructMember

    deps: Set[str] = set()
    for op in struct_def.body:
        if isinstance(op, StructMember):
            deps.update(_STRUCT_TYPE_TEMPLATE_RE.findall(op.member_type.name))
        elif isinstance(op, FunctionDef):
            deps.update(call.callee.name.split("::")[0]
                        for call in _collect_function_calls(op.body))
    deps.discard(template_name)
    return deps & known_template_names


def _topo_sort_struct_templates(entries: 'List[Tuple["PolyTemplate", str, "StructDef"]]') -> 'List["PolyTemplate"]':
    """
    Topologically sort struct poly.template's so that every subcomponent's
    struct is translated (and its def text emitted) before any struct
    using it -- the frontend no longer guarantees callee-first source
    order (e.g. isequal_concrete.mlir declares IsEqual_1 before the IsZero_0
    it instantiates). Same stable DFS as _topo_sort_pure_functions: an
    already-ordered file keeps its exact original order.

    entries: (template_op, template_name, struct_def) triples, in original
    file order.
    """
    name2template = {name: template for template, name, _ in entries}
    known = set(name2template)
    name2deps = {name: _struct_template_deps(name, struct_def, known)
                 for _template, name, struct_def in entries}
    return _topo_sort_templates(
        [name for _template, name, _struct_def in entries], name2template, name2deps,
        "struct templates", "recursive component instantiation is not supported")


def _topo_sort_templates(names_in_order: List[str], name2template: 'Dict[str, "PolyTemplate"]',
                         name2deps: Dict[str, Set[str]], kind: str,
                         cycle_reason: str) -> 'List["PolyTemplate"]':
    """
    Shared DFS behind _topo_sort_pure_functions and
    _topo_sort_struct_templates. Visits names in names_in_order and
    recurses into dependencies first, so a pair with no dependency between
    them keeps its original relative order. Raises ValueError on a cycle.

    A name's own dependencies are visited in source order too, not in
    name2deps' set-iteration order -- str hashing is randomized per
    process, so iterating the set directly would make the emitted order of
    two sibling dependencies differ from one run to the next.
    """
    source_index = {name: i for i, name in enumerate(names_in_order)}
    sorted_names: List[str] = []
    visited: Set[str] = set()
    visiting: Set[str] = set()

    def visit(name: str) -> None:
        if name in visited:
            return
        if name in visiting:
            raise ValueError(
                f"Cycle detected among {kind} involving {name!r}: {cycle_reason}"
            )
        visiting.add(name)
        for dep in sorted(name2deps[name], key=source_index.__getitem__):
            visit(dep)
        visiting.discard(name)
        visited.add(name)
        sorted_names.append(name)

    for name in names_in_order:
        visit(name)

    return [name2template[name] for name in sorted_names]


def _nested_regions(op: Operation) -> List[List[Operation]]:
    """
    The nested op lists (regions) of op, using the same per-class shapes as
    _collect_function_calls (explicit checks for the classes with more than
    one body list, falling back to a generic 'body' attribute).
    """
    from llzk_dialects.scf import SCFIf, SCFFor, SCFWhile, SCFExecuteRegion

    if isinstance(op, SCFIf):
        return [op.then_body] + ([op.else_body] if op.else_body else [])
    if isinstance(op, SCFWhile):
        return [op.before_body, op.after_body]
    if isinstance(op, (SCFFor, SCFExecuteRegion)) or hasattr(op, 'body'):
        return [op.body]
    return []


def _collect_function_defs(ops: List[Operation]) -> 'List["FunctionDef"]':
    """
    Every FunctionDef reachable from the module body: a pure function, a
    struct's @compute/@constrain, wrapped in poly.template or not.
    """
    from llzk_dialects.function import FunctionDef
    from llzk_dialects.poly import PolyTemplate
    from llzk_dialects.struct import StructDef

    defs = []
    for op in ops:
        if isinstance(op, FunctionDef):
            defs.append(op)
        elif isinstance(op, (PolyTemplate, StructDef)):
            defs.extend(_collect_function_defs(op.body))
    return defs


def _is_mutated(name: str, ops: List[Operation]) -> bool:
    """
    Whether the array SSA value `name` may be written to within ops (nested
    regions included): the target of an array.write/array.insert, or --
    conservatively -- an scf.for/scf.while loop-carried initial value, so
    no write can ever reach it through a loop's own block argument.
    """
    from llzk_dialects.array import ArrayWrite, ArrayInsert
    from llzk_dialects.scf import SCFFor, SCFWhile

    for op in ops:
        if isinstance(op, (ArrayWrite, ArrayInsert)) and op.arr_ref.name == name:
            return True
        if isinstance(op, SCFFor) and any(init.name == name for _arg, init in op.iter_args):
            return True
        if isinstance(op, SCFWhile) and any(init.name == name for _arg, init in op.init_args):
            return True
        if any(_is_mutated(name, region) for region in _nested_regions(op)):
            return True
    return False


def _rename_ssa(obj, old: str, new: str, seen: Set[int]) -> None:
    """
    Rename, in place, every SSAVar named `old` reachable from obj (an op,
    or a list/tuple/dict of them), walking each op's attributes generically
    -- so it doesn't depend on every op class's own `operands` property
    being complete, and covers nested regions too. Parsed SSAVars are
    distinct objects per occurrence, so this only touches the uses inside
    obj, never a same-named value elsewhere.
    """
    if isinstance(obj, SSAVar):
        if obj.name == old:
            obj.name = new
        return
    if id(obj) in seen:
        return
    if isinstance(obj, (list, tuple)):
        seen.add(id(obj))
        for item in obj:
            _rename_ssa(item, old, new, seen)
    elif isinstance(obj, dict):
        seen.add(id(obj))
        for item in obj.values():
            _rename_ssa(item, old, new, seen)
    elif isinstance(obj, Operation):
        seen.add(id(obj))
        for item in vars(obj).values():
            _rename_ssa(item, old, new, seen)


def _alias_global_reads(ops: List[Operation], ctx: TranslationContext) -> None:
    """
    For every array global.read in ops (nested regions included) whose
    result is never written to within its own scope -- the ops after it in
    the same block, plus their nested regions (by SSA dominance, a
    same-named value in a sibling region is a different value) -- rename
    every use in that scope to the global's own Core name and mark the read
    `aliased`, so it emits nothing: e.g. `array.read @global_@array_const_0[%i] %3`
    reads the `globals { ... }` entry directly. A read whose result *is*
    written to later (the frontend uses a zero const global as a local
    array's initial value, e.g. poseidon3_test_concrete.mlir's
    `%1 = global.read const @global::@array_const_67`, then filled in a
    loop) is left alone and translated as an explicit copy instead.
    """
    from llzk_dialects.global_ import GlobalRead, _global_ref_core

    for i, op in enumerate(ops):
        if isinstance(op, GlobalRead) and op.name_ref.name in ctx.global2core:
            name = op.result.name
            scope = ops[i + 1:]
            if not _is_mutated(name, scope):
                _rename_ssa(scope, name, _global_ref_core(ctx.global2core[op.name_ref.name]), set())
                op.aliased = True
        for region in _nested_regions(op):
            _alias_global_reads(region, ctx)


class NestedModuleOp(BlockOperation):
    """
    A named module nested inside the top-level module:

      module @global {
        global.def const @array_const_0 : !array.type<72 x !felt.type<"bn128">> = [ ... ]
        ...
      }

    circom-llzk uses it to hold the circuit's constant globals, referenced
    elsewhere as `@global::@array_const_0`. Only global.def bodies are
    supported. Its globals are registered and emitted (in the leading
    `globals { ... }` block) by ModuleOp.to_core, so this op itself emits
    nothing. Not dispatched through a dialect: LLZKParser.parse_body
    special-cases a line starting with `module @`.
    """

    def __init__(self, sym_name: GlobalVariable, body: List[Operation]):
        self.sym_name = sym_name
        self.body = body

    def dialect(self) -> Dialect:
        return Dialect("builtin")

    @staticmethod
    def match(line: str) -> bool:
        return line.strip().startswith("module @")

    @classmethod
    def parse(cls, lines: List[str], cursor: int,
              parse_fn: ParseFn) -> Tuple['NestedModuleOp', int]:
        from llzk_dialects.global_ import GlobalDef

        header = lines[cursor]
        m = re.match(r"\s*module\s+(?P<name>@[^\s{]+)\s*\{", header)
        if not m:
            raise ValueError(f"Failed to parse NestedModuleOp header: {header}")

        depth = header.count('{') - header.count('}')
        end = cursor
        while depth > 0 and end + 1 < len(lines):
            end += 1
            depth += lines[end].count('{') - lines[end].count('}')

        body = parse_fn(cursor + 1, end)
        unsupported = [op for op in body if not isinstance(op, GlobalDef)]
        if unsupported:
            raise NotImplementedError(
                f"Nested module {m['name']} contains {type(unsupported[0]).__name__}: "
                "only global.def is supported inside a nested module"
            )
        return NestedModuleOp(GlobalVariable.parse(m["name"]), body), end + 1

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        yield from ()

    def __repr__(self):
        body_str = '\n  '.join(repr(op) for op in self.body)
        return f"NestedModuleOp({self.sym_name} {{\n  {body_str}\n}})"


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
        # A pure function may be called by a template declared earlier in the
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
        # every other top-level item (nothing depends on a pure function's
        # textual position relative to a struct, only on it existing before
        # any call to it).
        #
        # Struct templates may be forward-referenced too (e.g.
        # isequal_concrete.mlir's IsEqual_1 instantiates IsZero_0, declared
        # afterwards). Unlike a pure function, a struct can't be handled by
        # a signature-only pre-registration: its own translation fills ctx
        # state the caller's translation reads (llzk_func2core,
        # core_func2args, member_to_struct, ...), and its def text must
        # precede any call to it. So struct templates are topologically
        # sorted among themselves (_topo_sort_struct_templates) and put back
        # into the slots struct templates already occupied, leaving every
        # other top-level item where it was -- an already-ordered file is
        # emitted exactly as before. Pure functions never depend on a
        # struct (a circom function can't instantiate a component), so
        # keeping them hoisted ahead of all structs stays correct.
        from llzk_dialects.poly import PolyTemplate, _register_pure_function
        from llzk_dialects.function import FunctionDef
        from llzk_dialects.struct import StructDef
        from llzk_dialects.global_ import GlobalDef, _register_global_def

        pure_function_entries = []
        struct_entries = []
        global_defs = []
        for operation in self.body:
            if (isinstance(operation, PolyTemplate) and len(operation.body) == 1
                    and isinstance(operation.body[0], StructDef)):
                struct_entries.append((operation, operation.sym_name.name, operation.body[0]))
            if (isinstance(operation, PolyTemplate) and len(operation.body) == 1
                    and isinstance(operation.body[0], FunctionDef)):
                func_def = operation.body[0]
                _register_pure_function(func_def, operation.sym_name.name, ctx)
                llzk_name = f"{operation.sym_name.name}::{func_def.sym_name.name}"
                pure_function_entries.append((operation, llzk_name, func_def))
            if isinstance(operation, GlobalDef):
                # A top-level global.def may textually appear AFTER the struct
                # that reads it (module-level symbols, not SSA, don't need to
                # be defined before use) -- see global_.py's
                # _register_global_def docstring.
                _register_global_def(operation, ctx)
                global_defs.append((operation, None))
            if isinstance(operation, NestedModuleOp):
                # Globals nested in `module @mod { ... }`, read as @mod::@x.
                for global_def in operation.body:
                    _register_global_def(global_def, ctx, operation.sym_name.name)
                    global_defs.append((global_def, operation.sym_name.name))

        # Every array global.read whose result is never written to reads the
        # `globals { ... }` entry directly instead of a per-read copy.
        for func_def in _collect_function_defs(self.body):
            _alias_global_reads(func_def.body, ctx)

        sorted_pure_templates = _topo_sort_pure_functions(pure_function_entries)
        sorted_struct_templates = iter(_topo_sort_struct_templates(struct_entries))

        pure_templates = {template for template, _name, _func_def in pure_function_entries}
        struct_templates = {template for template, _name, _struct_def in struct_entries}
        emission_order = sorted_pure_templates + [
            next(sorted_struct_templates) if operation in struct_templates else operation
            for operation in self.body if operation not in pure_templates
        ]

        # Array globals first, once each (a scalar global is inlined at each
        # global.read instead -- see GlobalRead.to_core).
        yield from self._yield_globals(global_defs, ctx)

        # Yield operation by operation
        for operation in emission_order:
            yield from operation.to_core(ctx)
        yield from self._yield_main_function(ctx)

    @staticmethod
    def _yield_globals(global_defs: 'List[Tuple["GlobalDef", Optional[str]]]',
                       ctx: TranslationContext) -> Generator[str, None, None]:
        """
        The leading `globals { @mod_@x: [v0, v1, ...] ... }` block: one entry
        per array global, in declaration order (provisional Core format).
        """
        from llzk_dialects.global_ import _global_ref_name, _global_entry_core

        entries = []
        for global_def, module_name in global_defs:
            ref_name = _global_ref_name(global_def, module_name)
            if ref_name in ctx.global2core:
                entries.append(_global_entry_core(ctx.global2core[ref_name], ctx.global2value[ref_name]))
        if entries:
            yield "globals {"
            yield from entries
            yield "}"

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


