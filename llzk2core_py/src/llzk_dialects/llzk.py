"""
LLZK core dialect — core LLZK-specific constructs.
Prefix: llzk.

Operations:
  LLZKNondet — llzk.nondet (declares an uninitialized / non-deterministic variable)

Top-level wrapper:
  ModuleOp   — represents the 'module attributes {...} { ... }' header; holds
               llzk.lang and llzk.main and owns the top-level body operations.
               Created directly by LLZKParser.parse(), not via dialect dispatch.

Attributes (represented as type annotations, not parsed independently):
  LoopBoundsAttr — #llzk.loopbounds<lower to upper step step>
  PublicAttr     — #llzk.pub  (marks circuit inputs/outputs as public)
"""

import re
from typing import List, Optional, TYPE_CHECKING

from llzk_dialects.core import Operation, SSAVar, Type, TranslationContext
from llzk_dialects.definitions import Dialect

if TYPE_CHECKING:
    pass  # avoid circular imports


class ModuleOp:
    """
    Top-level LLZK module.

    Wraps all top-level operations and carries the module-level attributes:
      llzk.lang        — unit attribute marking this as an LLZK program
      llzk.main        — struct type of the circuit entry point

    Syntax of the header line:
      module attributes {llzk.lang, llzk.main = !struct.type<@Name::@Name<[]>>} {

    Created by LLZKParser.parse() when the input starts with 'module'; not
    dispatched through the dialect registration system.
    """

    def __init__(self, lang: bool, main_type: Optional[Type],
                 body: List[Operation]):
        self.lang = lang
        # The struct type that acts as the circuit entry point, or None if absent.
        self.main_type = main_type
        self.body = body

    @classmethod
    def parse_header(cls, header: str) -> 'tuple[bool, Optional[Type]]':
        """
        Extract llzk.lang and llzk.main from a module attributes line.
        Returns (lang_present, main_type_or_None).
        """
        lang = "llzk.lang" in header
        main_type = None
        # llzk.main = <type>, where <type> ends at the next ',' or '}'
        # at the top level (the type itself may contain '<', '>', '[', ']').
        m = re.search(r'llzk\.main\s*=\s*([^,}]+)', header)
        if m:
            main_type = Type.parse(m.group(1).strip())
        return lang, main_type

    def to_core(self, ctx: TranslationContext) -> str:
        # TODO: implement core translation
        raise NotImplementedError

    def __repr__(self):
        lang_str = "llzk.lang, " if self.lang else ""
        main_str = f"llzk.main = {self.main_type}" if self.main_type else ""
        attrs = lang_str + main_str
        body_str = "\n  ".join(repr(op) for op in self.body)
        return f"ModuleOp(module attributes {{{attrs}}} {{\n  {body_str}\n}})"


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
