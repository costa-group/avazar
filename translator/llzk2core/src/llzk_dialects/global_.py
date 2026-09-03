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
from llzk_dialects.utils import array_felt_first_dimension, split_top_level_commas


_FELT_CONST_RE = re.compile(r'#felt<const\s*(-?\d+)\s*:')


def _parse_felt_literal(token: str) -> int:
    """
    Parse a single felt-typed literal from a global.def initial value: either
    a plain integer ("0", "17") or an attribute-wrapped constant
    (e.g. '#felt<const 42 : <"bn128">> : !felt.type<"bn128">').
    """
    token = token.strip()
    m = _FELT_CONST_RE.search(token)
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


def _register_global_def(op: 'GlobalDef', ctx: TranslationContext) -> None:
    """
    Register a global.def's value in ctx.global2value so global.read can
    resolve it. Idempotent (plain dict assignment recomputes the same
    value), so it's safe to call both from a module-level pre-pass
    (registering forward-referenced globals before any body is translated —
    see llzk.py's ModuleOp.to_core) and again, redundantly, from
    GlobalDef.to_core itself.
    """
    ctx.global2value[op.sym_name.name] = _parse_global_value(op.initial_value)


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
        # Nothing is emitted for the def itself: the value is only consumed
        # by global.read, which resolves it through ctx.global2value.
        _register_global_def(self, ctx)
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

    def __init__(self, result: SSAVar, name_ref: GlobalVariable, result_type: Type):
        self._result = result
        self.name_ref = name_ref
        self.result_type = result_type

    def dialect(self) -> Dialect:
        return Dialect("global")

    @staticmethod
    def match(line: str) -> bool:
        return line.split('=')[-1].strip().split()[0] in GlobalRead._OPS

    @classmethod
    def parse(cls, line: str) -> 'GlobalRead':
        pattern = re.compile(
            r"\s*(?P<res>\S+)\s*=\s*global\.read\s+(?P<ref>@\S+)"
            r"\s*:\s*(?P<type>.+)\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse GlobalRead: {line}")
        return GlobalRead(SSAVar.parse(m["res"]),
                          GlobalVariable.parse(m["ref"]),
                          Type.parse(m["type"].strip()))

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
            yield f"array.new {dim} {self._result.to_core()}"
            for i, elem in enumerate(value):
                yield f"array.write {elem} {self._result.to_core()}[{i}]"
            return

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
        # TODO: implement core translation
        raise NotImplementedError

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
