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
from typing import Callable, List, Generator, Optional

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
        self._result = variable
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

    @property
    def result(self):
        return self._result

    @property
    def operands(self) -> List[SSAVar]:
        return []

    def to_function(self, prime: Optional[int] = None) -> Callable[[], int]:
        c = self.constant if prime is None else self.constant % prime
        return lambda: c

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        # Introducing constants is as easy as an assignment
        ctx.var2const[self._result.name] = self.constant % ctx.prime
        yield f"{self._result.to_core()} = {self.constant}"

    def __repr__(self):
        type_str = f" : {self.result_type}" if self.result_type else ""
        return f"FeltConst({self._result} = {self.constant}{type_str})"


class FeltUnary(Operation):
    """
    Unary field element operations.

    Syntax: %result = <op> $operand [: type($operand)]
    Ops: felt.bit_not, felt.inv, felt.neg
    """

    _OPS = {"felt.bit_not", "felt.inv", "felt.neg"}

    _OPS2CORE = {"felt.bit_not": "bit.not"}

    def __init__(self, variable: SSAVar, op: str,
                 operand: SSAVar, types: List[Type]):
        self._result = variable
        self._op = op
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

    @property
    def result(self):
        return self._result

    @property
    def op(self):
        return self._op

    @property
    def operands(self) -> List[SSAVar]:
        return [self.operand]

    # Prime-agnostic (matches this codebase's behavior before field-aware
    # simulation existed) -- used when to_function() is called with no
    # prime. felt.inv here is a placeholder, not a real modular inverse: it
    # was never given the modulus it needs.
    _UNARY_FNS: dict = {
        "felt.neg": lambda x: -x,
        "felt.bit_not": lambda x: ~x,
        "felt.inv": lambda x: 1 // x,
    }

    # Genuine field arithmetic, reduced modulo the prime when one is given
    # -- felt.bit_not is deliberately excluded, same reasoning as
    # FeltBinary._FIELD_ARITHMETIC_OPS (a bitwise op on the value's
    # underlying bit pattern, not field arithmetic).
    _FIELD_ARITHMETIC_OPS = {"felt.neg", "felt.inv"}

    def to_function(self, prime: Optional[int] = None) -> Callable[[int], int]:
        if self._op not in self._UNARY_FNS:
            raise NotImplementedError(f"to_function not implemented for {self._op}")
        if prime is None or self._op not in self._FIELD_ARITHMETIC_OPS:
            return self._UNARY_FNS[self._op]
        if self._op == "felt.inv":
            # Real modular inverse via Fermat's little theorem (every field
            # in core_utils.FIELD_PRIMES is prime) -- 1 // x was never
            # correct, just never previously given the modulus to be. x == 0
            # has no inverse; raise the same ZeroDivisionError a real
            # division-by-zero would, so callers' existing guards still work.
            def _inv(x: int, _p=prime) -> int:
                if x % _p == 0:
                    raise ZeroDivisionError("felt.inv of 0 has no modular inverse")
                return pow(x, _p - 2, _p)
            return _inv
        fn = self._UNARY_FNS[self._op]
        return lambda x, _fn=fn, _p=prime: _fn(x) % _p

    def to_core(self, ctx: TranslationContext) -> str:
        # Unary operations are translated into an assignment
        yield f"{self._result.to_core()} = {self._OPS2CORE.get(self._op, self._op)} {self.operand.to_core()}"

        # If the operand is already a known compile-time constant, fold this
        # operation too -- needed so a chain of arithmetic rooted at an outer
        # loop's induction variable (only known once that loop is unrolled)
        # keeps resolving to a concrete int all the way through to a nested
        # loop's bound. Guarded: this may be evaluated inside a branch of an
        # scf.if that's dead for the current concrete iteration (Core always
        # translates both branches), so a guarded felt.inv-by-zero etc. must
        # not crash translation -- just skip the fold.
        operand_val = ctx.var2const.get(self.operand.name)
        if operand_val is not None:
            try:
                ctx.var2const[self._result.name] = self.to_function(ctx.prime)(operand_val)
            except (ZeroDivisionError, ArithmeticError):
                pass

    def __repr__(self):
        type_str = ('' if not self.types
                    else ' : ' + ', '.join(repr(t) for t in self.types))
        return f"FeltUnary({self._result} = {self._op}({self.operand}){type_str})"


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

    _OPS2CORE = {
        "felt.shr": "bit.shr", "felt.shl": "bit.shl",
        "felt.bit_and": "bit.and", "felt.bit_or": "bit.or",
        "felt.bit_xor": "bit.xor", "felt.uintdiv": "felt.uidiv",
        "felt.umod": "felt.uimod"
    }

    def __init__(self, variable: SSAVar, op: str,
                 lhs: SSAVar, rhs: SSAVar, types: List[Type]):
        self._result = variable
        self._op = op
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
        assert m["op"] in cls._OPS, \
            f"Binary operation in Felt not recognised: {m['op']}. Expression: {line}"
        return cls(SSAVar.parse(m["res"]), m["op"],
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

    # Genuine field arithmetic (reduced modulo the field's prime when one is
    # given -- see to_function). felt.uintdiv/sintdiv/shl/shr/umod/smod/
    # bit_and/bit_or/bit_xor are deliberately excluded: those are integer/
    # bitwise operations on a felt-typed value's underlying bit pattern
    # (e.g. bit-extraction loops via felt.shr/felt.bit_and), not field
    # arithmetic -- reducing them modulo the field's prime would be wrong,
    # not just unnecessary.
    _FIELD_ARITHMETIC_OPS = {"felt.add", "felt.sub", "felt.mul", "felt.div", "felt.pow"}

    _BINARY_FNS: dict = {
        "felt.add":     lambda x, y: x + y,
        "felt.sub":     lambda x, y: x - y,
        "felt.mul":     lambda x, y: x * y,
        "felt.div":     lambda x, y: x // y,
        "felt.uintdiv": lambda x, y: x // y,
        "felt.sintdiv": lambda x, y: int(x / y),
        "felt.pow":     lambda x, y: x ** y,
        "felt.shl":     lambda x, y: x << y,
        "felt.shr":     lambda x, y: x >> y,
        "felt.umod":    lambda x, y: x % y,
        "felt.smod":    lambda x, y: x % y,
        "felt.bit_and": lambda x, y: x & y,
        "felt.bit_or":  lambda x, y: x | y,
        "felt.bit_xor": lambda x, y: x ^ y,
    }

    def to_function(self, prime: Optional[int] = None) -> Callable[[int, int], int]:
        fn = self._BINARY_FNS.get(self._op)
        if fn is None:
            raise NotImplementedError(f"to_function not implemented for {self._op}")
        if prime is None or self._op not in self._FIELD_ARITHMETIC_OPS:
            return fn
        if self._op == "felt.pow":
            # Python's 3-arg pow is modular exponentiation -- computes
            # x**y % prime without ever materializing x**y itself, which for
            # a large y (routine in field arithmetic, e.g. sqrt_0's
            # Tonelli-Shanks residue checks) would otherwise be an
            # astronomically large intermediate bigint.
            return lambda x, y, _p=prime: pow(x, y, _p)
        return lambda x, y, _fn=fn, _p=prime: _fn(x, y) % _p

    def to_core(self, ctx: TranslationContext) -> str:
        # Just return the name of the function applied to the arguments
        yield f"{self._result.to_core()} = {self._OPS2CORE.get(self._op, self._op)} {self.lhs.to_core()} {self.rhs.to_core()}"

        # Fold into a compile-time constant when both operands already are
        # one -- see FeltUnary.to_core's comment for why this matters (tied
        # nested loops) and why the guard is needed (dead-branch division).
        lhs_val = ctx.var2const.get(self.lhs.name)
        rhs_val = ctx.var2const.get(self.rhs.name)
        if lhs_val is not None and rhs_val is not None:
            try:
                ctx.var2const[self._result.name] = self.to_function(ctx.prime)(lhs_val, rhs_val)
            except (ZeroDivisionError, ArithmeticError):
                pass

    def __repr__(self):
        type_str = ('' if not self.types
                    else ' : ' + ', '.join(repr(t) for t in self.types))
        return f"FeltBinary({self._result} = {self._op}({self.lhs}, {self.rhs})){type_str}"



class FeltDialect(Dialect):
    """Registry for all felt dialect operations."""

    def __init__(self):
        super().__init__("felt")
        self.register(FeltConst)
        self.register(FeltUnary)
        self.register(FeltBinary)
