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
from typing import List, Optional, TYPE_CHECKING, Generator

from llzk_dialects.core import Operation, SSAVar, Type, TranslationContext
from llzk_dialects.definitions import Dialect
from llzk_dialects.function import FunctionDef
from llzk_dialects.utils import invocation_args, signature_args, array_felt_first_dimension

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

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        """
        This translates a whole module. It needs to translate the complete body and then add
        the main function to invoke directly the template regarding llzk.main
        """
        # Yield operation by operation
        for operation in self.body:
            yield from operation.to_core(ctx)
        yield from self._yield_main_function(ctx)

    def _yield_main_function(self, ctx: TranslationContext) -> Generator[str, None, None]:
        """
        Generates the main function at the end of the core program, that serves
        as the entry point
        """
        # We need to transform the llzk.main argument into the expected format.
        # For instance, '!struct.type<@BinaryAdd_0::@BinaryAdd_0<[]>>' should be
        # transformed to the llzk name @BinaryAdd_0::@BinaryAdd_0::@compute
        possible_components = [component for component in self.main_type.name.split("<") if "::" in component]
        assert len(possible_components) == 1, "Error identifying the main function: " \
                                              "there should be exactly one component with ::"
        llzk_name = possible_components[0] + "::@compute"

        # Finally, yield the main function from the args we have retrieved
        core_function = ctx.llzk_func2core[llzk_name]
        in_args, out_args = ctx.core_func2args[core_function]

        # For declaring the main function
        joined_in_args_with_type = signature_args(in_args)
        joined_out_args_with_type = signature_args(out_args)

        # For invoking the function
        joined_in_args = invocation_args(in_args)
        joined_out_args = invocation_args(out_args)

        yield f"""
            def main({joined_in_args_with_type}) -> {joined_out_args_with_type} {{
                call {core_function}({joined_in_args}) to {joined_out_args}
            }}
        """

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
            r"\s*(?P<res>\S+)\s*=\s*llzk\.nondet\s*:\s*(?P<type>.+)\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse LLZKNondet: {line}")
        return LLZKNondet(SSAVar.parse(m["res"]), Type.parse(m["type"].strip()))

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        # Initializes value. In our case, it is only relevant for arrays,
        # but for finite elements, we initialize it to zero
        # TODO: ask Albert?
        array_dim = array_felt_first_dimension(self.result_type.name)
        if array_dim is not None:
            yield f"array.new {array_dim} {self.result.name}"
        elif "!felt.type" in self.result_type.name:
            yield f"{self.result.name} = 0"
        else:
            raise ValueError(f"llzk.nondet transformation for not recognized expression: {self.result_type.name}")

    def __repr__(self):
        return f"LLZKNondet({self.result} = llzk.nondet : {self.result_type})"


class LLZKDialect(Dialect):
    """Registry for all llzk dialect operations."""

    def __init__(self):
        super().__init__("llzk")
        self.register(LLZKNondet)
