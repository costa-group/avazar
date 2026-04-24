"""
Felt dialect — finite field element operations.
Prefix: felt.

Operations are grouped by arity:
  FeltConst  — felt.const  (constant literal)
  FeltUnary  — felt.bit_not, felt.inv, felt.neg
  FeltBinary — felt.add, felt.bit_and, felt.bit_or, felt.bit_xor, felt.div,
               felt.mul, felt.pow, felt.shl, felt.shr, felt.sintdiv,
               felt.smod, felt.sub, felt.uintdiv, felt.umod
"""

import re
from typing import List, Generator

from llzk_dialects.core import Operation, SSAVar, Type, TranslationContext
from llzk_dialects.definitions import Dialect


class FeltConst(Operation):
    """
    Field element constant.

    Syntax: %result = felt.const $value
    Example: %c = felt.const 42
    """

    _OPS = {"felt.const"}

    def __init__(self, variable: SSAVar, constant: int,
                 result_type: Type = None):
        self.result = variable
        self.constant = constant
        self.result_type = result_type

    def dialect(self) -> Dialect:
        return Dialect("felt")

    @staticmethod
    def match(line: str) -> bool:
        return line.split('=')[-1].strip().split()[0] in FeltConst._OPS

    @classmethod
    def parse(cls, line: str) -> 'FeltConst':
        pattern = re.compile(
            r"\s*(?P<res>\S+)\s*=\s*felt\.const\s+(?P<value>\S+)"
            r"(?:\s*:\s*(?P<type>.+))?\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse FeltConst: {line}")
        type_opt = Type.parse(m["type"].strip()) if m["type"] else None
        return FeltConst(SSAVar.parse(m["res"]), int(m["value"]), type_opt)

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        # Introducing constants is as easy as an assignment
        yield f"{self.result.to_core()} = {self.constant}"

    def __repr__(self):
        type_str = f" : {self.result_type}" if self.result_type else ""
        return f"FeltConst({self.result} = {self.constant}{type_str})"


class FeltUnary(Operation):
    """
    Unary field element operations.

    Syntax: %result = <op> $operand [: type($operand)]
    Ops: felt.bit_not, felt.inv, felt.neg
    """

    _OPS = {"felt.bit_not", "felt.inv", "felt.neg"}

    def __init__(self, variable: SSAVar, op: str,
                 operand: SSAVar, types: List[Type]):
        self.result = variable
        self.op = op
        self.operand = operand
        self.types = types

    def dialect(self) -> Dialect:
        return Dialect("felt")

    @staticmethod
    def match(line: str) -> bool:
        return line.split('=')[-1].strip().split()[0] in FeltUnary._OPS

    @classmethod
    def parse(cls, line: str) -> 'FeltUnary':
        pattern = re.compile(
            r"\s*(?P<res>\S+)\s*=\s*(?P<op>\S+)\s+(?P<operand>\S+)"
            r"(?:\s*:\s*(?P<types>\S.*\S))?\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse FeltUnary: {line}")
        types = (
            [Type.parse(t.strip()) for t in m["types"].split(",")]
            if m["types"] else []
        )
        assert m["op"] in FeltUnary._OPS, \
            f"Unary operation in Felt not recognised: {m['op']}. Expression: {line}"
        return FeltUnary(SSAVar.parse(m["res"]), m["op"],
                         SSAVar.parse(m["operand"]), types)

    def to_core(self, ctx: TranslationContext) -> str:
        # Unary operations are translated into an assignment
        yield f"{self.result.to_core()} = {self.op} {self.operand.to_core()}"

    def __repr__(self):
        type_str = ('' if not self.types
                    else ' : ' + ', '.join(repr(t) for t in self.types))
        return f"FeltUnary({self.result} = {self.op}({self.operand}){type_str})"


class FeltBinary(Operation):
    """
    Binary field element operations.

    Syntax: %result = <op> $lhs, $rhs [: type($lhs), type($rhs)]
    Ops: felt.add, felt.bit_and, felt.bit_or, felt.bit_xor, felt.div,
         felt.mul, felt.pow, felt.shl, felt.shr, felt.sintdiv,
         felt.smod, felt.sub, felt.uintdiv, felt.umod
    """

    _OPS = {
        "felt.add", "felt.bit_and", "felt.bit_or", "felt.bit_xor",
        "felt.div", "felt.mul", "felt.pow", "felt.shl", "felt.shr",
        "felt.sintdiv", "felt.smod", "felt.sub", "felt.uintdiv", "felt.umod",
    }

    def __init__(self, variable: SSAVar, op: str,
                 lhs: SSAVar, rhs: SSAVar, types: List[Type]):
        self.result = variable
        self.op = op
        self.lhs = lhs
        self.rhs = rhs
        self.types = types

    def dialect(self) -> Dialect:
        return Dialect("felt")

    @staticmethod
    def match(line: str) -> bool:
        return line.split('=')[-1].strip().split()[0] in FeltBinary._OPS

    @classmethod
    def parse(cls, line: str) -> 'FeltBinary':
        pattern = re.compile(
            r"\s*(?P<res>\S+)\s*=\s*(?P<op>\S+)\s+(?P<lhs>\S+)\s*,\s*(?P<rhs>\S+)"
            r"(?:\s*:\s*(?P<types>\S.*\S))?\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse FeltBinary: {line}")
        types = (
            [Type.parse(t.strip()) for t in m["types"].split(",")]
            if m["types"] else []
        )
        assert m["op"] in FeltBinary._OPS, \
            f"Binary operation in Felt not recognised: {m['op']}. Expression: {line}"
        return FeltBinary(SSAVar.parse(m["res"]), m["op"],
                          SSAVar.parse(m["lhs"]), SSAVar.parse(m["rhs"]), types)

    def to_core(self, ctx: TranslationContext) -> str:
        # Just return the name of the function applied to the arguments
        yield f"{self.result.to_core()} = {self.op} {self.lhs.to_core()} {self.rhs.to_core()}"

    def __repr__(self):
        type_str = ('' if not self.types
                    else ' : ' + ', '.join(repr(t) for t in self.types))
        return f"FeltBinary({self.result} = {self.op}({self.lhs}, {self.rhs})){type_str}"


class FeltDialect(Dialect):
    """Registry for all felt dialect operations."""

    def __init__(self):
        super().__init__("felt")
        self.register(FeltConst)
        self.register(FeltUnary)
        self.register(FeltBinary)
