"""
Arith dialect — standard MLIR integer arithmetic (used inside LLZK).
Prefix: arith.

Operations:
  ArithConst  — arith.constant (integer or index constant)
  ArithBinary — arith.addi, arith.subi, arith.muli,
                arith.divsi, arith.divui, arith.remsi, arith.remui,
                arith.andi, arith.ori, arith.xori,
                arith.shli, arith.shrsi, arith.shrui,
                arith.maxsi, arith.maxui, arith.minsi, arith.minui
  ArithCmpi   — arith.cmpi (integer comparison with predicate)
  ArithCast   — arith.extsi, arith.extui, arith.trunci,
                arith.index_cast, arith.index_castui
"""

import re
from typing import List, Generator

from llzk_dialects.core import Operation, SSAVar, Type, TranslationContext
from llzk_dialects.definitions import Dialect

# Valid predicate strings for arith.cmpi
CMPI_PREDICATES = {"eq", "ne", "slt", "sle", "sgt", "sge", "ult", "ule", "ugt", "uge"}


def parse_arith_const_value(value: str) -> int:
    """
    Parse an arith.constant's literal value string into an int. Boolean
    constants are spelled 'true'/'false' rather than an integer literal (Core
    has no boolean type, so they become 1/0); anything else is a plain int.
    """
    mapped = {"true": 1, "false": 0}.get(value)
    return int(value) if mapped is None else mapped


class ArithConst(Operation):
    """
    Integer, index, or boolean (i1) constant.

    Syntax: %result = arith.constant $value [: $type]
    Examples:
      %c = arith.constant 42 : i32
      %n = arith.constant 0 : index
      %true = arith.constant true
    A boolean constant ('true'/'false') carries no type annotation at all in
    real MLIR output; it implicitly means i1.
    Attribute: value (IntegerAttr)
    Result:    integer, index, or i1 type
    """

    _OPS = {"arith.constant"}

    def __init__(self, result: SSAVar, value: str, result_type: Type):
        self._result = result
        # Stored as string to preserve the literal form (e.g. '-1', 'true').
        self.value = value
        self.result_type = result_type

    def dialect(self) -> Dialect:
        return Dialect("arith")

    @staticmethod
    def match(line: str) -> bool:
        return line.split('=')[-1].strip().split()[0] in ArithConst._OPS

    @classmethod
    def parse(cls, line: str) -> 'ArithConst':
        # %r = arith.constant <value> [: <type>]
        pattern = re.compile(
            r"\s*(?P<res>\S+)\s*=\s*arith\.constant\s+(?P<val>\S+)"
            r"(?:\s*:\s*(?P<type>.+))?\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse ArithConst: {line}")
        type_str = m["type"].strip() if m["type"] else "i1"
        return ArithConst(SSAVar.parse(m["res"]), m["val"], Type.parse(type_str))

    @property
    def result(self):
        return self._result

    @property
    def operands(self) -> List[SSAVar]:
        return []

    def to_core(self, ctx: TranslationContext) -> str:
        value = parse_arith_const_value(self.value)
        ctx.var2const[self._result.name] = value
        yield f"{self._result.to_core()} = {value}"

    def __repr__(self):
        return f"ArithConst({self._result} = arith.constant {self.value} : {self.result_type})"


class ArithBinary(Operation):
    """
    Binary integer arithmetic and bitwise operations.

    Syntax: %result = <op> %lhs, %rhs : $type
    Operands: lhs, rhs (same integer type)
    Result:   same integer type
    """

    _OPS = {
        "arith.addi", "arith.subi", "arith.muli",
        "arith.divsi", "arith.divui", "arith.remsi", "arith.remui",
        "arith.andi", "arith.ori", "arith.xori",
        "arith.shli", "arith.shrsi", "arith.shrui",
        "arith.maxsi", "arith.maxui", "arith.minsi", "arith.minui",
    }

    _OPS2CORE = {
        "arith.addi": "felt.add",
        "arith.subi": "felt.sub",
        "arith.muli": "felt.mul",
        "arith.divsi": "arith.divui",
        "arith.divui": "arith.divui",
        "arith.andi": "bit.and",
        "arith.ori": "bit.or",
        "arith.xori": "bit.xor",
        "arith.shli": "bit.shl",
        "arith.shrsi": "bit.shr",
        "arith.shrui": "bit.shr",
    }

    def __init__(self, result: SSAVar, op: str, lhs: SSAVar, rhs: SSAVar,
                 operand_type: Type):
        self._result = result
        self._op = op
        self.lhs = lhs
        self.rhs = rhs
        self.operand_type = operand_type

    def dialect(self) -> Dialect:
        return Dialect("arith")

    @staticmethod
    def match(line: str) -> bool:
        return line.split('=')[-1].strip().split()[0] in ArithBinary._OPS

    @classmethod
    def parse(cls, line: str) -> 'ArithBinary':
        # %r = arith.addi %a, %b : i32
        pattern = re.compile(
            r"\s*(?P<res>\S+)\s*=\s*(?P<op>\S+)"
            r"\s+(?P<lhs>\S+)\s*,\s*(?P<rhs>\S+)"
            r"\s*:\s*(?P<type>.+)\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse ArithBinary: {line}")
        assert m["op"] in ArithBinary._OPS, \
            f"Binary arith operation not recognised: {m['op']}"
        return ArithBinary(SSAVar.parse(m["res"]), m["op"],
                           SSAVar.parse(m["lhs"]), SSAVar.parse(m["rhs"]),
                           Type.parse(m["type"].strip()))

    @property
    def result(self):
        return self._result

    @property
    def op(self):
        return self._op

    @property
    def operands(self) -> List[SSAVar]:
        return [self.lhs, self.rhs]

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        core_op = self._OPS2CORE.get(self._op)
        if core_op is None:
            raise NotImplementedError(f"Operation {self._op} not currently implemented")
        yield f"{self._result.to_core()} = {core_op} {self.lhs.to_core()} {self.rhs.to_core()}"

    def __repr__(self):
        return (f"ArithBinary({self._result} = {self._op}"
                f"({self.lhs}, {self.rhs}) : {self.operand_type})")


class ArithCmpi(Operation):
    """
    Integer comparison.

    Syntax: %result = arith.cmpi <predicate>, %lhs, %rhs : $type
    Predicate: eq | ne | slt | sle | sgt | sge | ult | ule | ugt | uge
    Operands:  lhs, rhs (same integer type)
    Result:    i1
    """

    _OPS = {"arith.cmpi"}

    _PRED2CORE = {"eq": "bool.eq", "ne": "bool.neq", "lt": "bool.lt",
                  "le": "bool.ge", "gt": "bool.gt", "ge": "bool.ge"}

    def __init__(self, result: SSAVar, predicate: str,
                 lhs: SSAVar, rhs: SSAVar, operand_type: Type):
        self._result = result
        self.predicate = predicate
        self.lhs = lhs
        self.rhs = rhs
        self.operand_type = operand_type

    def dialect(self) -> Dialect:
        return Dialect("arith")

    @staticmethod
    def match(line: str) -> bool:
        return line.split('=')[-1].strip().split()[0] in ArithCmpi._OPS

    @classmethod
    def parse(cls, line: str) -> 'ArithCmpi':
        # %r = arith.cmpi eq, %a, %b : i32
        pattern = re.compile(
            r"\s*(?P<res>\S+)\s*=\s*arith\.cmpi\s+(?P<pred>\w+)"
            r"\s*,\s*(?P<lhs>\S+)\s*,\s*(?P<rhs>\S+)"
            r"\s*:\s*(?P<type>.+)\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse ArithCmpi: {line}")
        assert m["pred"] in CMPI_PREDICATES, \
            f"Unknown arith.cmpi predicate: {m['pred']}"
        return ArithCmpi(SSAVar.parse(m["res"]), m["pred"],
                         SSAVar.parse(m["lhs"]), SSAVar.parse(m["rhs"]),
                         Type.parse(m["type"].strip()))

    @property
    def result(self):
        return self._result

    @property
    def operands(self) -> List[SSAVar]:
        return [self.lhs, self.rhs]

    def to_core(self, ctx: TranslationContext) -> str:
        core_op = self._PRED2CORE.get(self.predicate)
        if core_op is None:
            raise NotImplementedError(f"Predicate {self.predicate} not currently implemented in {self}")
        yield f"{self._result.to_core()} = {core_op} {self.lhs.to_core()} {self.rhs.to_core()}"

    def __repr__(self):
        return (f"ArithCmpi({self._result} = arith.cmpi {self.predicate}"
                f"({self.lhs}, {self.rhs}) : {self.operand_type})")


class ArithCast(Operation):
    """
    Integer extension, truncation, and index conversion.

    Syntax: %result = <op> %operand : $src_type to $dst_type
    Examples:
      %r = arith.extsi %a : i32 to i64
      %r = arith.trunci %a : i64 to i32
      %r = arith.index_cast %a : i32 to index
    Operand: any integer or index type
    Result:  any integer or index type
    """

    _OPS = {"arith.extsi", "arith.extui", "arith.trunci",
            "arith.index_cast", "arith.index_castui"}

    def __init__(self, result: SSAVar, op: str, operand: SSAVar,
                 src_type: Type, dst_type: Type):
        self._result = result
        self._op = op
        self.operand = operand
        self.src_type = src_type
        self.dst_type = dst_type

    def dialect(self) -> Dialect:
        return Dialect("arith")

    @staticmethod
    def match(line: str) -> bool:
        return line.split('=')[-1].strip().split()[0] in ArithCast._OPS

    @classmethod
    def parse(cls, line: str) -> 'ArithCast':
        # %r = arith.extsi %a : i32 to i64
        pattern = re.compile(
            r"\s*(?P<res>\S+)\s*=\s*(?P<op>\S+)"
            r"\s+(?P<operand>\S+)"
            r"\s*:\s*(?P<src>.+?)\s+to\s+(?P<dst>.+)\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse ArithCast: {line}")
        assert m["op"] in ArithCast._OPS, \
            f"Arith cast operation not recognised: {m['op']}"
        return ArithCast(SSAVar.parse(m["res"]), m["op"],
                         SSAVar.parse(m["operand"]),
                         Type.parse(m["src"].strip()), Type.parse(m["dst"].strip()))

    @property
    def result(self):
        return self._result

    @property
    def op(self):
        return self._op

    @property
    def operands(self) -> List[SSAVar]:
        return [self.operand]

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        # TODO: implement core translation
        raise NotImplementedError

    def __repr__(self):
        return (f"ArithCast({self._result} = {self._op}"
                f"({self.operand} : {self.src_type} to {self.dst_type}))")


class ArithDialect(Dialect):
    """Registry for all arith dialect operations."""

    def __init__(self):
        super().__init__("arith")
        self.register(ArithConst)
        self.register(ArithBinary)
        self.register(ArithCmpi)
        self.register(ArithCast)
