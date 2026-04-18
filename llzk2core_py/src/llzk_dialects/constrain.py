"""
Constrain dialect — constraint emission operations.
Prefix: constrain.

Operations:
  ConstrainEq — constrain.eq  (equality constraint between two values)
  ConstrainIn — constrain.in  (containment constraint: value in array)
"""

import re
from typing import List

from llzk_dialects.core import Operation, SSAVar, Type, TranslationContext
from llzk_dialects.definitions import Dialect


class ConstrainEq(Operation):
    """
    Emit an equality constraint: lhs == rhs.

    Syntax: constrain.eq $lhs, $rhs : type($lhs)
    Operands: lhs, rhs (any LLZK type except struct/string)
    No result — this is a constraint emission, not a computation.
    Traits: Commutative, ConstraintGen
    """

    _OPS = {"constrain.eq"}

    def __init__(self, lhs: SSAVar, rhs: SSAVar, types: List[Type]):
        self.lhs = lhs
        self.rhs = rhs
        self.types = types

    def dialect(self) -> Dialect:
        return Dialect("constrain")

    @staticmethod
    def match(line: str) -> bool:
        return line.strip().split()[0] in ConstrainEq._OPS

    @classmethod
    def parse(cls, line: str) -> 'ConstrainEq':
        pattern = re.compile(
            r"\s*constrain\.eq\s+(?P<lhs>\S+)\s*,\s*(?P<rhs>\S+)"
            r"(?:\s*:\s*(?P<types>\S.*\S))?\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse ConstrainEq: {line}")
        types = (
            [Type.parse(t.strip()) for t in m["types"].split(",")]
            if m["types"] else []
        )
        return ConstrainEq(SSAVar.parse(m["lhs"]), SSAVar.parse(m["rhs"]), types)

    def to_core(self, ctx: TranslationContext) -> str:
        # TODO: implement core translation
        raise NotImplementedError

    def __repr__(self):
        type_str = ('' if not self.types
                    else ' : ' + ', '.join(repr(t) for t in self.types))
        return f"ConstrainEq(constrain.eq({self.lhs}, {self.rhs}){type_str})"


class ConstrainIn(Operation):
    """
    Emit a containment constraint: lhs is an element of rhs array.

    Syntax: constrain.in $lhs, $rhs : type($lhs), type($rhs)
    Operands: lhs (scalar), rhs (n-dimensional array)
    No result — constraint emission only.
    Traits: ConstraintGen
    """

    _OPS = {"constrain.in"}

    def __init__(self, lhs: SSAVar, rhs: SSAVar, types: List[Type]):
        self.lhs = lhs
        self.rhs = rhs
        self.types = types

    def dialect(self) -> Dialect:
        return Dialect("constrain")

    @staticmethod
    def match(line: str) -> bool:
        return line.strip().split()[0] in ConstrainIn._OPS

    @classmethod
    def parse(cls, line: str) -> 'ConstrainIn':
        pattern = re.compile(
            r"\s*constrain\.in\s+(?P<lhs>\S+)\s*,\s*(?P<rhs>\S+)"
            r"(?:\s*:\s*(?P<types>\S.*\S))?\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse ConstrainIn: {line}")
        types = (
            [Type.parse(t.strip()) for t in m["types"].split(",")]
            if m["types"] else []
        )
        return ConstrainIn(SSAVar.parse(m["lhs"]), SSAVar.parse(m["rhs"]), types)

    def to_core(self, ctx: TranslationContext) -> str:
        # TODO: implement core translation
        raise NotImplementedError

    def __repr__(self):
        type_str = ('' if not self.types
                    else ' : ' + ', '.join(repr(t) for t in self.types))
        return f"ConstrainIn(constrain.in({self.lhs}, {self.rhs}){type_str})"


class ConstrainDialect(Dialect):
    """Registry for all constrain dialect operations."""

    def __init__(self):
        super().__init__("constrain")
        self.register(ConstrainEq)
        self.register(ConstrainIn)
