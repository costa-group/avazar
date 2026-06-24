"""
Core base classes for the LLZK parser.

Hierarchy:
  Operation       — base for flat (single-line) ops
  BlockOperation  — base for multi-line ops that contain a body
  TranslationContext — context object passed to to_core(); extend this class
                       (not method signatures) when more translation state is needed
"""
import re
from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from typing import Dict, List, Callable, Tuple, TYPE_CHECKING, Union, Generator, Optional
from llzk_dialects.utils import array_felt_first_dimension


if TYPE_CHECKING:
    from llzk_dialects.definitions import Dialect


class SSAVar:
    """
    SSA variable — the % sigil is included in the name.
    Optional numeric suffix after ':' indicates a multi-result component index.
    """

    def __init__(self, name: str, n_components: int = 1):
        self.name = name
        self.n_components = n_components

    @classmethod
    def parse(cls, ssa_var: str) -> 'SSAVar':
        assert ssa_var[0] == "%", \
            f"Trying to parse a SSAVar with no preceding %: {ssa_var}"
        components = ssa_var.split(":")
        if len(components) == 1:
            return SSAVar(components[0])
        elif len(components) == 2:
            return SSAVar(components[0], int(components[1]))
        else:
            raise ValueError(f"SSA variable has more than one ':': {ssa_var}")

    def to_core(self) -> str:
        # Core needs to introduce a variable for each component.
        # We assume that only a variadic variable (i.e. multiple components)
        # is transformed to core in its declaration
        return self.name if self.n_components == 1 else ','.join([f"{self.name}#{i}" for i in range(self.n_components)])

    def to_core_component(self, i: int) -> str:
        """
        Retrieves the core expresion of a given position if it has n components.
        Otherwise, it works similarly to_core method
        """
        assert i < self.n_components, f"SSA var {self}: trying to access a component " \
                                      f"beyond the number of available components"
        return self.name if self.n_components == 1 else f"{self.name}#{i}"

    def __repr__(self) -> str:
        return self.name if self.n_components == 1 else f"{self.name}:{self.n_components}"

    def __eq__(self, other):
        return (isinstance(other, SSAVar)
                and self.name == other.name
                and self.n_components == other.n_components)


class GlobalVariable:
    """
    Global reference preceded by @ (sigil included in the name).
    Used for function names, struct names, global value names, etc.
    """

    def __init__(self, name: str):
        self.name = name

    @classmethod
    def parse(cls, global_var: str) -> 'GlobalVariable':
        assert global_var[0] == "@", \
            f"Global variable must start with @: {global_var}"
        return GlobalVariable(global_var.replace("$", "_"))

    def __repr__(self):
        return self.name

    def __eq__(self, other):
        return isinstance(other, GlobalVariable) and self.name == other.name


class Type:
    """
    Wrapper around a raw type string (e.g. '!felt.type', '!array.type<...>').
    Full type parsing is deferred to a later phase.
    """

    def __init__(self, type_: str):
        self.name = type_

    @classmethod
    def parse(cls, type_: str) -> 'Type':
        return Type(type_)

    def __repr__(self):
        return self.name

    def to_core(self):
        """
        Transforms a Type into the corresponding declaration in Core
        """
        array_dim = array_felt_first_dimension(self.name)
        if array_dim is not None:
            return f"arr<{array_dim}>"

        elif "!felt.type" in self.name:
            return "ff"

        return None

    def __eq__(self, other):
        return isinstance(other, Type) and self.name == other.name


@dataclass
class TranslationContext:
    """
    Holds all state needed during the to_core() translation pass.

    Design: add fields here — not to method signatures — when more context
    is required (e.g. a type environment, symbol table, field prime spec).
    Existing to_core() implementations are unaffected by new fields they
    don't use.
    """
    # Maps SSA variable names (e.g. '%0') to a constant (if they are constant).
    var2const: Dict[str, int] = field(default_factory=dict)

    # Maps every llzk function to the corresponding core function
    llzk_func2core: Dict[str, str] = field(default_factory=dict)

    # Maps every core function to the in args (tuple[0]) and the out args (tuple[1]).
    # Generated while parsing an object. Every in and out args is of the form
    # [[%a, !array.type<...>], [%b, <!felt.type<...>]], so that invocations to the functions can be generated easily
    core_func2args: Dict[str, Tuple[List[Tuple[str, Type]], List[Tuple[str, Type]]]] = field(default_factory=dict)

    # Current poly.template (if inside any)
    current_template: str = None

    # Current function name in core (if any)
    current_core_function: str = None

    # Current arguments returned by an if/while/for. Useful for "scf.yield" instruction inside a while or an if
    scf_result: List[SSAVar] = field(default_factory=list)

    # Pod variables that have been traversed so far, with the name of their fields
    # and how they are translated
    ssa2pod_var: Dict[str, Dict[str, Tuple[str, Type]]] = field(default_factory=dict)

    # Pre-pass maps built once per compute function, cleared after:
    #   pod_ssa_name -> struct member base name (from @X$inputs writes)
    input_pod_to_member: Dict[str, str] = field(default_factory=dict)
    #   ssa_name -> semantic Core name (e.g. "%13" -> "last1.in1_last")
    ssa_to_name: Dict[str, str] = field(default_factory=dict)

    # Maps each core function name to its subcomponent members:
    #   core_function_name -> {member_name -> referred_struct_name}
    # e.g. {"IsZero_1": {"last1": "lastComponent_0", "last2": "lastComponent_0"}}
    member_to_struct: Dict[str, Dict[str, str]] = field(default_factory=dict)

    # Maps the SSA result name of a no-arg function call to the struct member name
    # that holds that component instance (e.g. "%0" -> "cst" when the result of
    # `call @Constants_3()` ends up as `@cst`). Used by FunctionCall.to_core() only;
    # kept separate from ssa_to_name so struct decomposition doesn't see it.
    struct_result_to_member: Dict[str, str] = field(default_factory=dict)

    # Arrays of non-felt elements: tracks what pod/struct SSA var lives at each index.
    # Populated by array.write, consumed by array.read (no CORE output generated).
    #   array_ssa_name -> {index: pod_ssa_name}
    array_pod_entries: Dict[str, Dict[int, str]] = field(default_factory=dict)

    #   array_ssa_name -> {index: struct_ssa_name}
    array_struct_entries: Dict[str, Dict[int, str]] = field(default_factory=dict)


def _apply_rename(name: str, rename: Dict[str, str]) -> str:
    """Apply a rename dict to an SSA variable name.

    Handles plain names ("%2" -> "%2_aft") and component references
    ("%2#1" -> "%2_aft#1") where only the base name appears in the dict.
    """
    if name in rename:
        return rename[name]
    if '#' in name:
        base, idx = name.rsplit('#', 1)
        if base in rename:
            return rename[base] + '#' + idx
    return name


class Operation(ABC):
    """
    Abstract base for flat (single-line) LLZK operations.

    Subclasses must implement:
      match(line)  — static; True if this line belongs to the op
      parse(line)  — classmethod; parse from a single text line
      dialect()    — return the owning Dialect instance
      to_core(ctx) — translate to core representation string
      __repr__()   — human-readable form
    """

    @abstractmethod
    def dialect(self) -> 'Dialect':
        pass

    @staticmethod
    @abstractmethod
    def match(line: str) -> bool:
        pass

    @classmethod
    @abstractmethod
    def parse(cls, line: str) -> 'Operation':
        raise NotImplementedError

    @abstractmethod
    def to_core(self, ctx: TranslationContext) -> str:
        """
        Translate this operation into its core representation.
        Returns a string (one or more lines) to be written to the output file.
        """
        raise NotImplementedError

    @property
    def result(self) -> Optional['SSAVar']:
        """The single SSA variable this operation defines, or None."""
        return None

    @property
    def op(self) -> str:
        """The operation name string (e.g. 'felt.add', 'arith.constant')."""
        return next(iter(self._OPS))

    @property
    def operands(self) -> List['SSAVar']:
        """The input SSA variable operands of this operation."""
        return []

    def update_variables(self, rename: Dict[str, str]) -> None:
        """Rename SSA variables in-place according to rename. Mutates SSAVar.name directly.

        Also handles component references like %2#1: if %2 is renamed to %2_aft,
        then %2#1 is renamed to %2_aft#1.
        """
        if self.result is not None:
            self.result.name = _apply_rename(self.result.name, rename)
        for operand in self.operands:
            operand.name = _apply_rename(operand.name, rename)


# Type alias used by BlockOperation.parse
ParseFn = Callable[[int, int], List[Operation]]


class BlockOperation(Operation, ABC):
    """
    Abstract base for multi-line LLZK operations that contain a body
    (e.g. struct.def, function.def, scf.if, scf.while).

    The parse() signature is different from flat Operation:
      parse(cls, lines, cursor, parse_fn) -> (op, next_cursor)

    parse_fn is a callback provided by LLZKParser:
      parse_fn(start: int, end: int) -> List[Operation]
    It allows the block op to recursively parse its body without depending
    on the parser directly.

    match() still inspects a single header line.
    """

    @classmethod
    @abstractmethod
    def parse(cls, lines: List[str], cursor: int,
              parse_fn: ParseFn) -> Tuple['BlockOperation', int]:
        raise NotImplementedError

    def update_variables(self, rename: Dict[str, str]) -> None:
        """Rename variables in this op and recurse into self.body."""
        super().update_variables(rename)
        for op in self.body:
            op.update_variables(rename)
