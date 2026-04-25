"""
Struct dialect — circuit component definitions and member access.
Prefix: struct.

In LLZK, a 'struct' represents a ZK circuit component. It has named members
(signals/columns) and two special functions: 'compute' (witness generation)
and 'constrain' (constraint emission).

Types:
  StructType — !struct.type<@NameRef<[params]>>

Operations:
  StructMember — struct.member  (declare a named member field inside a struct.def)
  StructNew    — struct.new     (instantiate a struct)
  StructReadm  — struct.readm   (read a member from a struct instance)
  StructWritem — struct.writem  (write a value to a struct member)
  StructDef    — struct.def     (BlockOperation: define a circuit component)
"""

import re
from typing import List, Optional, Tuple, Generator

from llzk_dialects.core import (
    Operation, BlockOperation, SSAVar, GlobalVariable, Type,
    TranslationContext, ParseFn,
)
from llzk_dialects.definitions import Dialect
from llzk_dialects.function import FunctionDef
from llzk_dialects.utils import translate_assignment_core

class StructMember(Operation):
    """
    Declare a named member field within a struct.def body.

    Syntax: struct.member @sym_name : $type [attr-dict]
    Attributes:
      sym_name (StringAttr)
      type     (TypeAttr)
      column   (UnitAttr, optional) - marks the member as a column
      signal   (UnitAttr, optional) - marks the member as a signal
      llzk.pub (UnitAttr, optional) - marks the member as an out signal
    Valid parent: StructDefOp
    Interfaces: Symbol, SymbolUserOpInterface
    """

    _OPS = {"struct.member"}

    def __init__(self, sym_name: GlobalVariable, member_type: Type,
                 is_column: bool = False, is_signal: bool = False, is_out: bool = False):
        self.sym_name = sym_name
        self.member_type = member_type
        self.is_column = is_column
        self.is_signal = is_signal
        self.is_out = is_out

    def dialect(self) -> Dialect:
        return Dialect("struct")

    @staticmethod
    def match(line: str) -> bool:
        return line.strip().split()[0] in StructMember._OPS

    @classmethod
    def parse(cls, line: str) -> 'StructMember':
        # struct.member @name : !type [{column, signal}]
        pattern = re.compile(
            r"\s*struct\.member\s+(?P<name>@\S+)\s*:\s*(?P<type>[^{]+?)"
            r"(?:\s*\{(?P<attrs>[^}]*)\})?\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse StructMember: {line}")
        attrs = m["attrs"] or ""
        return StructMember(
            GlobalVariable.parse(m["name"]),
            Type.parse(m["type"].strip()),
            is_column="column" in attrs,
            is_signal="signal" in attrs,
            is_out="llzk.pub" in attrs
        )

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        # Basic transformation: just return the variable itself (should not be used
        # in general on their own)
        yield self.sym_name

    def __repr__(self):
        flags = []
        if self.is_column:
            flags.append("column")
        if self.is_signal:
            flags.append("signal")
        flag_str = f" {{{', '.join(flags)}}}" if flags else ""
        return f"StructMember({self.sym_name} : {self.member_type}{flag_str})"


class StructNew(Operation):
    """
    Create a new instance of a struct type.

    Syntax: %result = struct.new : type($result)
    Result: StructType
    Traits: WitnessGen
    """

    _OPS = {"struct.new"}

    def __init__(self, result: SSAVar, result_type: Type):
        self.result = result
        self.result_type = result_type

    def dialect(self) -> Dialect:
        return Dialect("struct")

    @staticmethod
    def match(line: str) -> bool:
        return line.split('=')[-1].strip().split()[0] in StructNew._OPS

    @classmethod
    def parse(cls, line: str) -> 'StructNew':
        pattern = re.compile(
            r"\s*(?P<res>\S+)\s*=\s*struct\.new\s*:\s*(?P<type>.+)\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse StructNew: {line}")
        return StructNew(SSAVar.parse(m["res"]), Type.parse(m["type"].strip()))

    def introduced_var(self):
        return self.result

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        # Does nothing, we do not care about the creation of the struct itself
        yield from ()

    def __repr__(self):
        return f"StructNew({self.result} = struct.new : {self.result_type})"


class StructReadm(Operation):
    """
    Read the value of a named member from a struct instance.

    Syntax: %val = struct.readm $component [@member_name] : type($component), type($val)
    Attributes: member_name (FlatSymbolRefAttr)
    Operand:    component (StructType)
    Result:     valid LLZK type
    """

    _OPS = {"struct.readm"}

    def __init__(self, result: SSAVar, component: SSAVar,
                 member_name: GlobalVariable, types: List[Type]):
        self.result = result
        self.component = component
        self.member_name = member_name
        self.types = types

    def dialect(self) -> Dialect:
        return Dialect("struct")

    @staticmethod
    def match(line: str) -> bool:
        return line.split('=')[-1].strip().split()[0] in StructReadm._OPS

    @classmethod
    def parse(cls, line: str) -> 'StructReadm':
        pattern = re.compile(
            r"\s*(?P<res>\S+)\s*=\s*struct\.readm\s+(?P<comp>\S+)"
            r"\s*\[\s*(?P<mem>@\S+)\s*\]"
            r"(?:\s*:\s*(?P<types>.+))?\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse StructReadm: {line}")
        types = (
            [Type.parse(t.strip()) for t in m["types"].split(",")]
            if m["types"] else []
        )
        return StructReadm(SSAVar.parse(m["res"]), SSAVar.parse(m["comp"]),
                           GlobalVariable.parse(m["mem"]), types)

    def introduced_var(self):
        return self.result

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        # Members of the struct are handled as plain variables. Hence, reading
        # a field just translates to an assignment
        yield f"{self.result.name} = {self.member_name.name}"

    def __repr__(self):
        type_str = '' if not self.types else ' : ' + ', '.join(repr(t) for t in self.types)
        return (f"StructReadm({self.result} = struct.readm "
                f"{self.component}[{self.member_name}]{type_str})")


class StructWritem(Operation):
    """
    Write a value to a named member of a struct instance.

    Syntax: struct.writem $component [@member_name] = $val : type($component), type($val)
    Attributes: member_name (FlatSymbolRefAttr)
    Operands:   component (StructType), val (valid LLZK type)
    Traits: WitnessGen
    """

    _OPS = {"struct.writem"}

    def __init__(self, component: SSAVar, member_name: GlobalVariable,
                 value: SSAVar, types: List[Type]):
        self.component = component
        self.member_name = member_name
        self.value = value
        self.types = types

    def dialect(self) -> Dialect:
        return Dialect("struct")

    @staticmethod
    def match(line: str) -> bool:
        return line.strip().split()[0] in StructWritem._OPS

    @classmethod
    def parse(cls, line: str) -> 'StructWritem':
        pattern = re.compile(
            r"\s*struct\.writem\s+(?P<comp>\S+)"
            r"\s*\[\s*(?P<mem>@\S+)\s*\]"
            r"\s*=\s*(?P<val>\S+)"
            r"(?:\s*:\s*(?P<types>.+))?\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse StructWritem: {line}")
        types = (
            [Type.parse(t.strip()) for t in m["types"].split(",")]
            if m["types"] else []
        )
        return StructWritem(SSAVar.parse(m["comp"]),
                            GlobalVariable.parse(m["mem"]),
                            SSAVar.parse(m["val"]), types)

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        # Members of the struct are handled as plain variables. Hence, writing
        # a field just translates to an assignment
        yield translate_assignment_core(self.member_name.name, self.value.to_core(), "array" not in self.types[1].name)

    def __repr__(self):
        type_str = '' if not self.types else ' : ' + ', '.join(repr(t) for t in self.types)
        return (f"StructWritem(struct.writem {self.component}"
                f"[{self.member_name}] = {self.value}{type_str})")


class StructDef(BlockOperation):
    """
    Define a circuit component (struct) with members and functions.

    Syntax:
      struct.def @StructName {
        struct.member @field : !type
        function.def @constrain(...) { ... }
        function.def @compute(...) { ... }
      }

    The body is parsed recursively using parse_fn and stored as a list of
    Operation instances (mix of StructMember and FunctionDef).

    Attributes: sym_name (StringAttr)
    Traits: SymbolTable, IsolatedFromAbove, SingleBlock
    Valid parents: ModuleOp, TemplateOp
    """

    _OPS = {"struct.def"}

    def __init__(self, sym_name: GlobalVariable, body: List[Operation]):
        self.sym_name = sym_name
        self.body = body

    def dialect(self) -> Dialect:
        return Dialect("struct")

    @staticmethod
    def match(line: str) -> bool:
        return line.strip().split()[0] in StructDef._OPS

    @classmethod
    def parse(cls, lines: List[str], cursor: int,
              parse_fn: ParseFn) -> Tuple['StructDef', int]:
        header = lines[cursor]
        # struct.def @Name {
        pattern = re.compile(r"\s*struct\.def\s+(?P<name>@\S+)\s*\{")
        m = re.match(pattern, header)
        if not m:
            raise ValueError(f"Failed to parse StructDef header: {header}")

        depth = header.count('{') - header.count('}')
        end = cursor
        while depth > 0 and end + 1 < len(lines):
            end += 1
            depth += lines[end].count('{') - lines[end].count('}')

        body = parse_fn(cursor + 1, end)
        return StructDef(GlobalVariable.parse(m["name"]), body), end + 1

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        # Implementation of the definition of a struct. It can have multiple members defined
        # and functions. They are handled as follows:
        #  * Members: members with llzk.pub are assumed out signals, otherwise they are intermediate
        #  * Functions: we just process function @compute.
        # We use isinstance because we need to store the function information in TranslationContext

        compute_op, in_args_with_type, out_args_with_type, _ = self._compute_core_function_info_from_struct()

        # There must be at least one compute
        assert compute_op is not None, "There is no @compute element in the struct"

        # The name to refer to the current function is @poly_template::@struct_def@compute
        # To identify subcalls in subcomponents, we store this convention
        llzk_name = f"{ctx.current_template}::{self.sym_name.name}::@compute"

        # The name we give is just the sym_name
        core_name = self.sym_name.name

        # Assign the information of the name of the function, in/out args to the context information
        ctx.llzk_func2core[llzk_name] = core_name
        ctx.core_func2args[core_name] = in_args_with_type, out_args_with_type
        ctx.current_core_function = core_name

        # After setting the translation, we just need to render the function
        # considering the out arguments we have generated
        yield from compute_op.to_core(ctx)

        # Set again to None to avoid inconsistencies in the future
        ctx.current_core_function = None

    def _compute_core_function_info_from_struct(self) -> Tuple[Operation, List[Tuple[str, str]], List[Tuple[str, str]], List[Tuple[str, str]]]:
        """
        Returns the operation corresponding to @compute, and the input and output arguments
        and the intermediate signals, following the format (var_name, core_type). For instance, [(%a, ff), (%b, arr<3>)].
        """

        # As part of translating a struct, we store the corresponding information of
        # the core function
        in_args_with_type = []
        out_args_with_type = []
        intermediate_signals = []
        compute_op = None

        # We need to obtain the information from the struct
        for operation in self.body:
            if isinstance(operation, StructMember):
                # Only traverse operations that are symbolic
                is_out = operation.is_out
                core_repr, core_type = operation.sym_name.name, operation.member_type.to_core()

                if is_out:
                    out_args_with_type.append((core_repr, core_type))
                else:
                    intermediate_signals.append((core_repr, core_type))

            # Only consider the @compute function, others are ignored
            elif isinstance(operation, FunctionDef) and operation.sym_name.name == "@compute":
                assert compute_op is None, "There are two @compute functions defined in a struct"
                # We wait for the translation after all the structMembers have been parsed
                # (not sure if the order is guaranteed by construction)
                compute_op = operation

                # The complete in args
                in_args_with_type = operation.in_args

        return compute_op, in_args_with_type, out_args_with_type, in_args_with_type

    def __repr__(self):
        body_str = '\n  '.join(repr(op) for op in self.body)
        return f"StructDef({self.sym_name} {{\n  {body_str}\n}})"


class StructDialect(Dialect):
    """Registry for all struct dialect operations."""

    def __init__(self):
        super().__init__("struct")
        self.register(StructMember)
        self.register(StructNew)
        self.register(StructReadm)
        self.register(StructWritem)
        # StructDef is a BlockOperation; dispatched separately by LLZKParser
        self.register(StructDef)
