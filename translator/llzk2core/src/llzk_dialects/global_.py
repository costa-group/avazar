"""
Global dialect — global value definition and access.
Prefix: global.

Note: module is named global_.py to avoid clashing with the Python builtin 'global'.

Operations:
  GlobalDef   — global.def   (declare a global constant or mutable value)
  GlobalRead  — global.read  (read a global value)
  GlobalWrite — global.write (write to a mutable global value)
"""

import re
from typing import Generator, List, Optional, Union

from llzk_dialects.core import Operation, SSAVar, GlobalVariable, Type, TranslationContext
from llzk_dialects.definitions import Dialect
from llzk_dialects.utils import array_felt_first_dimension, split_top_level_commas, translate_assignment_core


_FELT_CONST_RE = re.compile(r'#felt<const\s*(-?\d+)\s*:')
_TYPED_INT_RE = re.compile(r'(-?\d+)\s*:\s*\S.*')


def _parse_felt_literal(token: str) -> int:
    """
    Parse a single felt-typed literal from a global.def initial value: a
    plain integer ("0", "17"), an attribute-wrapped constant
    (e.g. '#felt<const 42 : <"bn128">> : !felt.type<"bn128">'), or a typed
    integer as nested-module globals use (e.g. '42 : <"bn128">',
    poseidon3_test_concrete.mlir's `module @global`).
    """
    token = token.strip()
    m = _FELT_CONST_RE.search(token)
    if m:
        return int(m.group(1))
    m = _TYPED_INT_RE.fullmatch(token)
    if m:
        return int(m.group(1))
    return int(token)


def _parse_global_value(raw: str) -> Union[int, List[int]]:
    """
    Parse a global.def initial value into either a single int (scalar felt)
    or a flat list of ints (felt array, already row-major flattened as
    emitted by circom-llzk for both uni- and multi-dimensional arrays).
    """
    raw = raw.strip()
    if raw.startswith('['):
        assert raw.endswith(']'), f"Malformed global array literal: {raw}"
        inner = raw[1:-1]
        return [_parse_felt_literal(e) for e in split_top_level_commas(inner) if e.strip()]
    return _parse_felt_literal(raw)


def _global_ref_name(op: 'GlobalDef', module_name: Optional[str]) -> str:
    """
    The name a global.read uses to refer to op: "@mod::@x" for a global
    declared inside a nested `module @mod { ... }` (e.g.
    "@global::@array_const_0", poseidon3_test_concrete.mlir), or the bare
    "@x" for one declared directly in the top-level module.
    """
    if module_name is None:
        return op.sym_name.name
    return f"{module_name}::{op.sym_name.name}"


def _global_core_name(ref_name: str) -> str:
    """
    The Core name of a global array, from its global.read reference name:
    "@global::@array_const_0" -> "@global_@array_const_0". The module
    prefix keeps same-named globals of different modules apart, and the
    leading '@' can never collide with an SSA-derived ('%') Core variable.
    """
    return ref_name.replace("::", "_")


def _global_ref_core(core_name: str) -> str:
    """
    How translated code refers to a global array: the single place every
    global.read (aliased use or explicit copy) gets the spelling from.

    TODO(format): the Core syntax for globals is still provisional -- a read
    may later need a different spelling to mark the value as known at
    symbolic execution time. Change it here only.
    """
    return core_name


def _global_entry_core(core_name: str, values: List[int]) -> str:
    """One `globals { ... }` entry: `@global_@x: [v0, v1, ...]`, row-major flattened."""
    return f"{core_name}: [{', '.join(str(v) for v in values)}]"


def _register_global_def(op: 'GlobalDef', ctx: TranslationContext,
                         module_name: Optional[str] = None) -> None:
    """
    Register a global.def's value in ctx.global2value (and, for an array,
    its Core name in ctx.global2core), keyed by the name global.read uses
    to refer to it. Idempotent (plain dict assignment recomputes the same
    value), so it's safe to call both from a module-level pre-pass
    (registering forward-referenced globals before any body is translated —
    see llzk.py's ModuleOp.to_core) and again, redundantly, from
    GlobalDef.to_core itself.
    """
    ref_name = _global_ref_name(op, module_name)
    value = _parse_global_value(op.initial_value)
    ctx.global2value[ref_name] = value
    if isinstance(value, list):
        ctx.global2core[ref_name] = _global_core_name(ref_name)


class GlobalDef(Operation):
    """
    Declare a global value (constant or mutable) at module level.

    Syntax: global.def [const] $sym_name : $type = $initial_value
    Attributes:
      sym_name      (StringAttr)
      constant      (UnitAttr, optional) — present means immutable
      type          (TypeAttr)
      initial_value (Attribute)
    Valid parent: ModuleOp
    """

    _OPS = {"global.def"}

    def __init__(self, sym_name: GlobalVariable, type_: Type,
                 initial_value: str, is_const: bool = False):
        self.sym_name = sym_name
        self.type_ = type_
        self.initial_value = initial_value
        self.is_const = is_const

    def dialect(self) -> Dialect:
        return Dialect("global")

    @staticmethod
    def match(line: str) -> bool:
        tok = line.strip().split()
        return tok[0] == "global.def" or (len(tok) > 1 and tok[1] == "global.def")

    @classmethod
    def parse(cls, line: str) -> 'GlobalDef':
        # global.def [const] @name : !type = value
        # 'value' may be a plain scalar ("0") or a bracketed, comma-separated
        # list of felt-attribute literals spanning many tokens -- captured
        # greedily (not \S+) so the whole literal is kept.
        pattern = re.compile(
            r"\s*global\.def\s+(?P<const>const\s+)?(?P<sym>@\S+)"
            r"\s*:\s*(?P<type>[^=]+?)\s*=\s*(?P<val>.+)\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse GlobalDef: {line}")
        return GlobalDef(
            GlobalVariable.parse(m["sym"]),
            Type.parse(m["type"].strip()),
            m["val"].strip(),
            is_const=m["const"] is not None,
        )

    @property
    def operands(self) -> List[SSAVar]:
        return []

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        # Nothing is emitted for the def itself: an array global is emitted
        # once, in the module's leading `globals { ... }` block (llzk.py's
        # ModuleOp.to_core), and a scalar is inlined at each global.read.
        # Registration already happened in ModuleOp.to_core's pre-pass (with
        # the enclosing nested module's name, which this op doesn't know).
        yield from ()

    def __repr__(self):
        const_str = "const " if self.is_const else ""
        return (f"GlobalDef(global.def {const_str}{self.sym_name} : "
                f"{self.type_} = {self.initial_value})")


class GlobalRead(Operation):
    """
    Read the value of a global.

    Syntax: %val = global.read @name_ref : type($val)
    Attributes: name_ref (SymbolRefAttr)
    Result: any LLZK type except non-constant types
    Interfaces: GlobalRefOpInterface, MemoryEffectOpInterface (MemoryEffectOpInterface), SymbolUserOpInterface
    """

    _OPS = {"global.read"}

    def __init__(self, result: SSAVar, name_ref: GlobalVariable, result_type: Type,
                 is_const: bool = False):
        self._result = result
        self.name_ref = name_ref
        self.result_type = result_type
        self.is_const = is_const
        # Set by llzk.py's _alias_global_reads when every use of the result
        # was renamed to the global's own Core name (no statement needed).
        self.aliased = False

    def dialect(self) -> Dialect:
        return Dialect("global")

    @staticmethod
    def match(line: str) -> bool:
        return line.split('=')[-1].strip().split()[0] in GlobalRead._OPS

    @classmethod
    def parse(cls, line: str) -> 'GlobalRead':
        pattern = re.compile(
            r"\s*(?P<res>\S+)\s*=\s*global\.read\s+(?P<const>const\s+)?(?P<ref>@\S+)"
            r"\s*:\s*(?P<type>.+)\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse GlobalRead: {line}")
        return GlobalRead(SSAVar.parse(m["res"]),
                          GlobalVariable.parse(m["ref"]),
                          Type.parse(m["type"].strip()),
                          is_const=m["const"] is not None)

    @property
    def result(self):
        return self._result

    @property
    def operands(self) -> List[SSAVar]:
        return []

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        value = ctx.global2value[self.name_ref.name]
        dim = array_felt_first_dimension(self.result_type.name)
        if dim is not None:
            assert isinstance(value, list) and len(value) == dim, (
                f"GlobalRead: global {self.name_ref} holds "
                f"{len(value) if isinstance(value, list) else value} value(s), "
                f"expected {dim} for type {self.result_type}"
            )
            if self.aliased:
                # Every use already refers to the global's Core name.
                return
            # The result is written to later in its scope (e.g. a zero
            # const global used as a local array's initial value), so it
            # needs its own copy -- writing through an alias would change
            # the shared global for every other reader.
            src = _global_ref_core(ctx.global2core[self.name_ref.name])
            yield translate_assignment_core(self._result.to_core(), src, False)
            return

        # A scalar global is never listed in `globals { ... }`: its value is
        # inlined at each read instead.
        ctx.var2const[self._result.name] = value
        yield f"{self._result.to_core()} = {value}"

    def __repr__(self):
        return (f"GlobalRead({self._result} = global.read "
                f"{self.name_ref} : {self.result_type})")


class GlobalWrite(Operation):
    """
    Write a value to a mutable global.

    Syntax: global.write @name_ref = $val : type($val)
    Attributes: name_ref (SymbolRefAttr)
    Operand: val (any LLZK type except non-constant types)
    Traits: WitnessGen
    """

    _OPS = {"global.write"}

    def __init__(self, name_ref: GlobalVariable, value: SSAVar, value_type: Type):
        self.name_ref = name_ref
        self.value = value
        self.value_type = value_type

    def dialect(self) -> Dialect:
        return Dialect("global")

    @staticmethod
    def match(line: str) -> bool:
        return line.strip().split()[0] in GlobalWrite._OPS

    @classmethod
    def parse(cls, line: str) -> 'GlobalWrite':
        pattern = re.compile(
            r"\s*global\.write\s+(?P<ref>@\S+)\s*=\s*(?P<val>\S+)"
            r"\s*:\s*(?P<type>.+)\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse GlobalWrite: {line}")
        return GlobalWrite(GlobalVariable.parse(m["ref"]),
                           SSAVar.parse(m["val"]),
                           Type.parse(m["type"].strip()))

    @property
    def operands(self) -> List[SSAVar]:
        return [self.value]

    def to_core(self, ctx: TranslationContext) -> str:
        # No real example writes a global yet. Once one does, a written
        # (mutable) global can't stay in the shared `globals { ... }` block
        # as-is: it needs a local copy, introduced once per translated
        # function (DECISIONS.md §52).
        raise NotImplementedError(
            f"global.write to {self.name_ref} is not supported yet (mutable globals)"
        )

    def __repr__(self):
        return (f"GlobalWrite(global.write {self.name_ref} = "
                f"{self.value} : {self.value_type})")


class GlobalDialect(Dialect):
    """Registry for all global dialect operations."""

    def __init__(self):
        super().__init__("global")
        self.register(GlobalDef)
        self.register(GlobalRead)
        self.register(GlobalWrite)
