"""
Cast dialect — type conversion operations between felt, index, and bool.
Prefix: cast.

Operations:
  CastToFelt  — cast.tofelt  (i1 or index → felt)
  CastToIndex — cast.toindex (felt → index)
"""

import re

from llzk_dialects.core import Operation, SSAVar, Type, TranslationContext
from llzk_dialects.definitions import Dialect


class CastToFelt(Operation):
    """
    Convert an integer (i1 or index) into a field element.

    Syntax: %result = cast.tofelt $value : type($value)
    Operand: value (i1 or index)
    Result:  felt type
    """

    _OPS = {"cast.tofelt"}

    def __init__(self, result: SSAVar, value: SSAVar, src_type: Type):
        self.result = result
        self.value = value
        self.src_type = src_type

    def dialect(self) -> Dialect:
        return Dialect("cast")

    @staticmethod
    def match(line: str) -> bool:
        return line.split('=')[-1].strip().split()[0] in CastToFelt._OPS

    @classmethod
    def parse(cls, line: str) -> 'CastToFelt':
        pattern = re.compile(
            r"\s*(?P<res>\S+)\s*=\s*cast\.tofelt\s+(?P<val>\S+)"
            r"\s*:\s*(?P<type>.+)\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse CastToFelt: {line}")
        return CastToFelt(SSAVar.parse(m["res"]),
                          SSAVar.parse(m["val"]),
                          Type.parse(m["type"].strip()))

    def to_core(self, ctx: TranslationContext) -> str:
        # Casting does nothing because CORE does not distinguish between felt and int
        yield from ()

    def __repr__(self):
        return f"CastToFelt({self.result} = cast.tofelt({self.value} : {self.src_type}))"


class CastToIndex(Operation):
    """
    Convert a field element into an index value.

    Syntax: %result = cast.toindex $value
    Operand: value (felt type)
    Result:  index
    """

    _OPS = {"cast.toindex"}

    def __init__(self, result: SSAVar, value: SSAVar, src_type: Type = None):
        self.result = result
        self.value = value
        self.src_type = src_type

    def dialect(self) -> Dialect:
        return Dialect("cast")

    @staticmethod
    def match(line: str) -> bool:
        return line.split('=')[-1].strip().split()[0] in CastToIndex._OPS

    @classmethod
    def parse(cls, line: str) -> 'CastToIndex':
        pattern = re.compile(
            r"\s*(?P<res>\S+)\s*=\s*cast\.toindex\s+(?P<val>\S+)"
            r"(?:\s*:\s*(?P<type>.+))?\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse CastToIndex: {line}")
        type_opt = Type.parse(m["type"].strip()) if m["type"] else None
        return CastToIndex(SSAVar.parse(m["res"]), SSAVar.parse(m["val"]), type_opt)

    def to_core(self, ctx: TranslationContext) -> str:
        # Casting does nothing because CORE does not distinguish between felt and int
        yield from ()

    def __repr__(self):
        type_str = f" : {self.src_type}" if self.src_type else ""
        return f"CastToIndex({self.result} = cast.toindex({self.value}{type_str}))"


class CastDialect(Dialect):
    """Registry for all cast dialect operations."""

    def __init__(self):
        super().__init__("cast")
        self.register(CastToFelt)
        self.register(CastToIndex)
