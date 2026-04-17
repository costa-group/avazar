"""
LLZK core dialect — core LLZK-specific constructs.
Prefix: llzk.

Operations:
  LLZKNondet — llzk.nondet (declares an uninitialized / non-deterministic variable)

Attributes (represented as type annotations, not parsed independently):
  LoopBoundsAttr — #llzk.loopbounds<lower to upper step step>
  PublicAttr     — #llzk.pub  (marks circuit inputs/outputs as public)
"""

import re

from src.llzk_dialects.core import Operation, SSAVar, Type, TranslationContext
from src.llzk_dialects.definitions import Dialect


class LLZKNondet(Operation):
    """
    Declare an uninitialized (non-deterministic) variable.

    In ZK circuits, a non-deterministic variable is one whose value is
    provided by the prover and must later be constrained to be correct.

    Syntax: %result = llzk.nondet : type($res)
    Result: any valid LLZK type
    Interfaces: OpAsmOpInterface
    """

    _OPS = {"llzk.nondet"}

    def __init__(self, result: SSAVar, result_type: Type):
        self.result = result
        self.result_type = result_type

    def dialect(self) -> Dialect:
        return Dialect("llzk")

    @staticmethod
    def match(line: str) -> bool:
        return line.split('=')[-1].strip().split()[0] in LLZKNondet._OPS

    @classmethod
    def parse(cls, line: str) -> 'LLZKNondet':
        pattern = re.compile(
            r"\s*(?P<res>\S+)\s*=\s*llzk\.nondet\s*:\s*(?P<type>\S+)\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse LLZKNondet: {line}")
        return LLZKNondet(SSAVar.parse(m["res"]), Type.parse(m["type"]))

    def to_core(self, ctx: TranslationContext) -> str:
        # TODO: implement core translation
        raise NotImplementedError

    def __repr__(self):
        return f"LLZKNondet({self.result} = llzk.nondet : {self.result_type})"


class LLZKDialect(Dialect):
    """Registry for all llzk dialect operations."""

    def __init__(self):
        super().__init__("llzk")
        self.register(LLZKNondet)
