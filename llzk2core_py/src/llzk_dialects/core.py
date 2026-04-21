"""
Core base classes for the LLZK parser.

Hierarchy:
  Operation       — base for flat (single-line) ops
  BlockOperation  — base for multi-line ops that contain a body
  TranslationContext — context object passed to to_core(); extend this class
                       (not method signatures) when more translation state is needed
"""

from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from typing import Dict, List, Callable, Tuple, TYPE_CHECKING

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
        return GlobalVariable(global_var)

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
    # Maps SSA variable names (e.g. '%0') to their core representation names.
    var_map: Dict[str, str] = field(default_factory=dict)

    # Maps every llzk function to the corresponding core function
    llzk_func2core: Dict[str, str] = field(default_factory=dict)

    # Maps every core function to the in args (tuple[0]) and the out args (tuple[1]).
    # Generated while parsing an object. Every in and out args is of the form
    # [[%a, arr<2>], [%b, ff]], so that invocations to the functions can be generated easily
    core_func2args: Dict[str, Tuple[List[Tuple[str, str]], List[Tuple[str, str]]]] = field(default_factory=dict)


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
