"""
Bool dialect — boolean logic and comparison operations.
Prefix: bool.

Operations:
  BoolAnd    — bool.and    (logical AND, commutative)
  BoolOr     — bool.or     (logical OR,  commutative)
  BoolXor    — bool.xor    (logical XOR, commutative)
  BoolNot    — bool.not    (logical NOT)
  BoolCmp    — bool.cmp    (field element comparison: eq/ne/lt/le/gt/ge)
  BoolAssert — bool.assert (runtime assertion with optional message)
"""

import re
from typing import Callable, List, Optional, Generator

from llzk_dialects.core import Operation, SSAVar, Type, TranslationContext
from llzk_dialects.definitions import Dialect

# Valid predicate strings for bool.cmp
FELT_CMP_PREDICATES = {"eq", "ne", "lt", "le", "gt", "ge"}


class BoolBinary(Operation):
    """
    Binary boolean operations (bool.and, bool.or, bool.xor).

    Syntax: %result = <op> $lhs, $rhs
    Operands: lhs, rhs (i1 or type variable)
    Result:   i1
    """

    _OPS = {"bool.and", "bool.or", "bool.xor"}

    def __init__(self, result: SSAVar, op: str, lhs: SSAVar, rhs: SSAVar,
                 types: List[Type] = None):
        self._result = result
        self._op = op
        self.lhs = lhs
        self.rhs = rhs
        self.types = types or []

    def dialect(self) -> Dialect:
        return Dialect("bool")

    @staticmethod
    def match(line: str) -> bool:
        return line.split('=')[-1].strip().split()[0] in BoolBinary._OPS

    @classmethod
    def parse(cls, line: str) -> 'BoolBinary':
        pattern = re.compile(
            r"\s*(?P<res>\S+)\s*=\s*(?P<op>\S+)\s+(?P<lhs>\S+)\s*,\s*(?P<rhs>\S+)"
            r"(?:\s*:\s*(?P<types>\S.*\S))?\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse BoolBinary: {line}")
        assert m["op"] in BoolBinary._OPS, \
            f"Binary bool operation not recognised: {m['op']}. Expression: {line}"
        types = (
            [Type.parse(t.strip()) for t in m["types"].split(",")]
            if m["types"] else []
        )
        return BoolBinary(SSAVar.parse(m["res"]), m["op"],
                          SSAVar.parse(m["lhs"]), SSAVar.parse(m["rhs"]), types)

    @property
    def result(self):
        return self._result

    @property
    def op(self):
        return self._op

    @property
    def operands(self) -> List[SSAVar]:
        return [self.lhs, self.rhs]

    _BINARY_FNS: dict = {
        "bool.and": lambda a, b: 1 if (a and b) else 0,
        "bool.or":  lambda a, b: 1 if (a or b) else 0,
        "bool.xor": lambda a, b: 1 if (bool(a) != bool(b)) else 0,
    }

    def to_function(self, prime: Optional[int] = None) -> Callable[[int, int], int]:
        # Boolean, not felt-typed -- always 0/1, regardless of any field's
        # prime; accepts the parameter only for interface uniformity with
        # construct_function_from_expressions' generic to_function(prime) call.
        return self._BINARY_FNS[self._op]

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        yield f"{self._result.to_core()} = {self._op} {self.lhs.to_core()} {self.rhs.to_core()}"

        # Fold into ctx.var2const (as 1/0, matching arith.constant true/false's
        # convention) when both operands are already known -- lets a
        # compound (bool.and/or/xor) scf.if condition become decidable too.
        lhs_val = ctx.var2const.get(self.lhs.name)
        rhs_val = ctx.var2const.get(self.rhs.name)
        if lhs_val is not None and rhs_val is not None:
            ctx.var2const[self._result.name] = self.to_function()(lhs_val, rhs_val)

    def __repr__(self):
        return f"BoolBinary({self._result} = {self._op}({self.lhs}, {self.rhs}))"


class BoolNot(Operation):
    """
    Logical NOT operator.

    Syntax: %result = bool.not $operand
    Operand: i1 or type variable
    Result:  i1
    """

    _OPS = {"bool.not"}

    def __init__(self, result: SSAVar, operand: SSAVar):
        self._result = result
        self.operand = operand

    def dialect(self) -> Dialect:
        return Dialect("bool")

    @staticmethod
    def match(line: str) -> bool:
        return line.split('=')[-1].strip().split()[0] in BoolNot._OPS

    @classmethod
    def parse(cls, line: str) -> 'BoolNot':
        pattern = re.compile(
            r"\s*(?P<res>\S+)\s*=\s*bool\.not\s+(?P<operand>\S+)\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse BoolNot: {line}")
        return BoolNot(SSAVar.parse(m["res"]), SSAVar.parse(m["operand"]))

    @property
    def result(self):
        return self._result

    @property
    def operands(self) -> List[SSAVar]:
        return [self.operand]

    def to_function(self, prime: Optional[int] = None) -> Callable[[int], int]:
        # Boolean, not felt-typed -- see BoolBinary.to_function.
        return lambda a: 1 if not a else 0

    def to_core(self, ctx: TranslationContext) -> str:
        yield f"{self._result.to_core()} = bool.not {self.operand.to_core()}"

        operand_val = ctx.var2const.get(self.operand.name)
        if operand_val is not None:
            ctx.var2const[self._result.name] = self.to_function()(operand_val)

    def __repr__(self):
        return f"BoolNot({self._result} = bool.not({self.operand}))"


class BoolCmp(Operation):
    """
    Compare two field element values.

    Syntax: %result = bool.cmp <predicate>($lhs, $rhs)
    Predicate: eq | ne | lt | le | gt | ge   (FeltCmpPredicateAttr)
    Operands:  lhs, rhs (felt type)
    Result:    i1
    """

    _OPS = {"bool.cmp"}
    _PRED2CORE = {"eq": "bool.eq", "ne": "bool.neq", "lt": "bool.lt",
                  "le": "bool.ge", "gt": "bool.gt", "ge": "bool.ge"}

    def __init__(self, result: SSAVar, predicate: str,
                 lhs: SSAVar, rhs: SSAVar, types: List[Type] = None):
        self._result = result
        self.predicate = predicate
        self.lhs = lhs
        self.rhs = rhs
        self.types = types or []

    def dialect(self) -> Dialect:
        return Dialect("bool")

    @staticmethod
    def match(line: str) -> bool:
        return line.split('=')[-1].strip().split()[0] in BoolCmp._OPS

    @classmethod
    def parse(cls, line: str) -> 'BoolCmp':
        # %result = bool.cmp eq(%lhs, %rhs) [: type, type]
        pattern = re.compile(
            r"\s*(?P<res>\S+)\s*=\s*bool\.cmp\s+(?P<pred>\w+)"
            r"\s*\(\s*(?P<lhs>\S+)\s*,\s*(?P<rhs>\S+)\s*\)"
            r"(?:\s*:\s*(?P<types>.+))?\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse BoolCmp: {line}")
        assert m["pred"] in FELT_CMP_PREDICATES, \
            f"Unknown bool.cmp predicate: {m['pred']}. Expression: {line}"
        types = (
            [Type.parse(t.strip()) for t in m["types"].split(",")]
            if m["types"] else []
        )
        return BoolCmp(SSAVar.parse(m["res"]), m["pred"],
                       SSAVar.parse(m["lhs"]), SSAVar.parse(m["rhs"]), types)

    @property
    def result(self):
        return self._result

    @property
    def operands(self) -> List[SSAVar]:
        return [self.lhs, self.rhs]

    _PRED_FNS: dict = {
        "eq": lambda a, b: 1 if a == b else 0,
        "ne": lambda a, b: 1 if a != b else 0,
        "lt": lambda a, b: 1 if a < b else 0,
        "le": lambda a, b: 1 if a <= b else 0,
        "gt": lambda a, b: 1 if a > b else 0,
        "ge": lambda a, b: 1 if a >= b else 0,
    }

    def to_function(self, prime: Optional[int] = None) -> Callable[[int, int], int]:
        # Compares two already-resolved felt values (via ctx.var2const,
        # which FeltBinary/FeltUnary now always store correctly reduced
        # modulo the prime) and returns 0/1 -- no further prime-awareness
        # needed here; accepts the parameter only for interface uniformity
        # with construct_function_from_expressions' generic to_function(prime).
        return self._PRED_FNS[self.predicate]

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        # TODO: implement core translation
        yield f"{self._result.to_core()} = {self._PRED2CORE[self.predicate]} {self.rhs.to_core()} {self.lhs.to_core()}"

        # Fold into ctx.var2const (1/0) when both operands are already known
        # -- this is what lets an scf.if's condition become decidable at
        # translation time, which in turn lets its result be folded too
        # (see SCFIf.to_core), and transitively lets a nested loop's bound
        # resolve once an enclosing loop's induction variable is concrete.
        lhs_val = ctx.var2const.get(self.lhs.name)
        rhs_val = ctx.var2const.get(self.rhs.name)
        if lhs_val is not None and rhs_val is not None:
            ctx.var2const[self._result.name] = self.to_function()(lhs_val, rhs_val)

    def __repr__(self):
        type_str = '' if not self.types else ' : ' + ', '.join(repr(t) for t in self.types)
        return (f"BoolCmp({self._result} = bool.cmp {self.predicate}"
                f"({self.lhs}, {self.rhs}){type_str})")


class BoolAssert(Operation):
    """
    Assertion operation — halts execution if condition is false.

    Syntax: bool.assert $condition [, $msg]
    Operand: condition (i1)
    Attribute: msg (StringAttr, optional)
    No result.
    """

    _OPS = {"bool.assert"}

    def __init__(self, condition: SSAVar, msg: Optional[str] = None):
        self.condition = condition
        self.msg = msg

    def dialect(self) -> Dialect:
        return Dialect("bool")

    @staticmethod
    def match(line: str) -> bool:
        return line.strip().split()[0] in BoolAssert._OPS

    @classmethod
    def parse(cls, line: str) -> 'BoolAssert':
        # bool.assert %cond
        # bool.assert %cond, "message"
        pattern = re.compile(
            r"\s*bool\.assert\s+(?P<cond>\S+)"
            r"(?:\s*,\s*(?P<msg>\".*\"))?\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse BoolAssert: {line}")
        return BoolAssert(SSAVar.parse(m["cond"]), m["msg"])

    @property
    def operands(self) -> List[SSAVar]:
        return [self.condition]

    def to_core(self, ctx: TranslationContext) -> str:
        # Ignore llzk asserts
        yield from ()

    def __repr__(self):
        msg_str = f', {self.msg}' if self.msg else ''
        return f"BoolAssert(bool.assert({self.condition}{msg_str}))"


class BoolDialect(Dialect):
    """Registry for all bool dialect operations."""

    def __init__(self):
        super().__init__("bool")
        self.register(BoolBinary)
        self.register(BoolNot)
        self.register(BoolCmp)
        self.register(BoolAssert)
