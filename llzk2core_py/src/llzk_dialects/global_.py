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
from typing import Optional

from src.llzk_dialects.core import Operation, SSAVar, GlobalVariable, Type, TranslationContext
from src.llzk_dialects.definitions import Dialect


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
        pattern = re.compile(
            r"\s*global\.def\s+(?P<const>const\s+)?(?P<sym>@\S+)"
            r"\s*:\s*(?P<type>\S+)\s*=\s*(?P<val>\S+)\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse GlobalDef: {line}")
        return GlobalDef(
            GlobalVariable.parse(m["sym"]),
            Type.parse(m["type"]),
            m["val"],
            is_const=m["const"] is not None,
        )

    def to_core(self, ctx: TranslationContext) -> str:
        # TODO: implement core translation
        raise NotImplementedError

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
    Interfaces: GlobalRefOpInterface, SymbolUserOpInterface
    """

    _OPS = {"global.read"}

    def __init__(self, result: SSAVar, name_ref: GlobalVariable, result_type: Type):
        self.result = result
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
            r"\s*:\s*(?P<type>\S+)\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse GlobalRead: {line}")
        return GlobalRead(SSAVar.parse(m["res"]),
                          GlobalVariable.parse(m["ref"]),
                          Type.parse(m["type"]))

    def to_core(self, ctx: TranslationContext) -> str:
        # TODO: implement core translation
        raise NotImplementedError

    def __repr__(self):
        return (f"GlobalRead({self.result} = global.read "
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
            r"\s*:\s*(?P<type>\S+)\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse GlobalWrite: {line}")
        return GlobalWrite(GlobalVariable.parse(m["ref"]),
                           SSAVar.parse(m["val"]),
                           Type.parse(m["type"]))

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
