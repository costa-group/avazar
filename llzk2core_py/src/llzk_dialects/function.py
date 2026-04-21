"""
Function dialect — function definition, calls, and returns.
Prefix: function.

Operations:
  FunctionDef    — function.def    (BlockOperation: defines a function with a body)
  FunctionCall   — function.call   (call a named function)
  FunctionReturn — function.return (return from a function, optionally with values)
"""

import re
from typing import List, Optional, Tuple, Generator

from llzk_dialects.core import (
    Operation, BlockOperation, SSAVar, GlobalVariable, Type,
    TranslationContext, ParseFn,
)
from llzk_dialects.definitions import Dialect
from llzk_dialects.utils import invocation_args, signature_args


class FunctionReturn(Operation):
    """
    Return from a function, optionally carrying result values.

    Syntax: function.return [($operands : type($operands))?]
    Operands: operands (variadic valid LLZK type, optional)
    Traits: Terminator, ReturnLike
    """

    _OPS = {"function.return"}

    def __init__(self, operands: List[SSAVar], types: List[Type]):
        self.operands = operands
        self.types = types

    def dialect(self) -> Dialect:
        return Dialect("function")

    @staticmethod
    def match(line: str) -> bool:
        return line.strip().split()[0] in FunctionReturn._OPS

    @classmethod
    def parse(cls, line: str) -> 'FunctionReturn':
        # function.return
        # function.return %v0, %v1 : !felt.type, !felt.type
        pattern = re.compile(
            r"\s*function\.return"
            r"(?:\s+(?P<ops>[^:]+)\s*:\s*(?P<types>.+))?\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse FunctionReturn: {line}")
        operands = (
            [SSAVar.parse(o.strip()) for o in m["ops"].split(",") if o.strip()]
            if m["ops"] else []
        )
        types = (
            [Type.parse(t.strip()) for t in m["types"].split(",")]
            if m["types"] else []
        )
        return FunctionReturn(operands, types)

    def to_core(self, ctx: TranslationContext) -> str:
        # Returns does nothing, as the returned arguments
        #  are specified in the signature
        yield from ()

    def __repr__(self):
        if not self.operands:
            return "FunctionReturn(function.return)"
        ops_str = ', '.join(repr(o) for o in self.operands)
        type_str = ' : ' + ', '.join(repr(t) for t in self.types) if self.types else ''
        return f"FunctionReturn(function.return {ops_str}{type_str})"


class FunctionCall(Operation):
    """
    Call a named function.

    Syntax: [%results,* =] function.call @callee($argOperands) : functional-type(...)
    Operands:  argOperands (variadic valid LLZK type), mapOperands (variadic index)
    Results:   variadic valid LLZK type
    Attributes: callee (SymbolRefAttr), templateParams (ArrayAttr, optional)
    Interfaces: CallOpInterface, SymbolUserOpInterface
    """

    _OPS = {"function.call"}

    def __init__(self, results: List[SSAVar], callee: GlobalVariable,
                 args: List[SSAVar], func_type: Optional[str]):
        self.results = results
        self.callee = callee
        self.args = args
        # func_type stores the raw functional-type string for now
        self.func_type = func_type

    def dialect(self) -> Dialect:
        return Dialect("function")

    @staticmethod
    def match(line: str) -> bool:
        # The call may or may not have a result assignment
        return "function.call" in line

    @classmethod
    def parse(cls, line: str) -> 'FunctionCall':
        # [%r0, %r1 =] function.call @fn(%a0, %a1) : (type) -> (type)
        pattern = re.compile(
            r"\s*(?:(?P<res>[^=]+?)\s*=\s*)?function\.call\s+(?P<callee>@\S+)"
            r"\s*\(\s*(?P<args>[^)]*)\s*\)"
            r"(?:\s*:\s*(?P<ftype>.+))?\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse FunctionCall: {line}")
        results = (
            [SSAVar.parse(r.strip()) for r in m["res"].split(",") if r.strip()]
            if m["res"] else []
        )
        args = (
            [SSAVar.parse(a.strip()) for a in m["args"].split(",") if a.strip()]
            if m["args"] else []
        )
        return FunctionCall(results, GlobalVariable.parse(m["callee"]),
                            args, m["ftype"])

    def to_core(self, ctx: TranslationContext) -> str:
        # TODO: implement core translation
        raise NotImplementedError

    def __repr__(self):
        res_str = (', '.join(repr(r) for r in self.results) + ' = ') if self.results else ''
        args_str = ', '.join(repr(a) for a in self.args)
        return f"FunctionCall({res_str}function.call {self.callee}({args_str}))"


class FunctionDef(BlockOperation):
    """
    Define a function with a typed signature and a body.

    Syntax:
      function.def @sym_name($arg0: type0, ...) -> (ret_type0, ...) {
        <body operations>
      }

    The body is parsed recursively using parse_fn and stored as a list of
    Operation instances.

    Attributes: sym_name (StringAttr), function_type (TypeAttr)
    Traits: IsolatedFromAbove, AffineScope, AutomaticAllocationScope
    Valid parents: ModuleOp, StructDefOp, TemplateOp
    """

    _OPS = {"function.def"}

    def __init__(self, sym_name: GlobalVariable, signature: str,
                 body: List[Operation]):
        self.sym_name = sym_name
        # signature stores the raw argument/return-type string for now
        self.signature = signature
        self.body = body

        # In arguments to from function definitions
        self._in_args = None

    def dialect(self) -> Dialect:
        return Dialect("function")

    @staticmethod
    def match(line: str) -> bool:
        return line.strip().split()[0] in FunctionDef._OPS

    @classmethod
    def parse(cls, lines: List[str], cursor: int,
              parse_fn: ParseFn) -> Tuple['FunctionDef', int]:
        header = lines[cursor]
        # function.def @name(args) [-> (rets)]? {
        pattern = re.compile(
            r"\s*function\.def\s+(?P<name>@[^\s(]+)"
            r"(?P<sig>[^{]*)\{"
        )
        m = re.match(pattern, header)
        if not m:
            raise ValueError(f"Failed to parse FunctionDef header: {header}")

        # Find matching closing brace
        depth = header.count('{') - header.count('}')
        end = cursor
        while depth > 0 and end + 1 < len(lines):
            end += 1
            depth += lines[end].count('{') - lines[end].count('}')

        body = parse_fn(cursor + 1, end)
        return (
            FunctionDef(GlobalVariable.parse(m["name"]), m["sig"].strip(), body),
            end + 1,
        )

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        # Translating a function assumes that the output (and input) information
        # is already stored in the context. This is because CORE does not exactly
        # share the same signature (in particular, out_args are public struct members).
        core_name = ctx.current_core_function
        in_args, out_args = ctx.core_func2args[core_name]

        signature_in = signature_args(in_args)
        signature_out = signature_args(out_args)

        # We start with the declaration of the function and the args
        yield f"def {core_name}({signature_in}) -> {signature_out} {{\n"

        for operation in self.body:
            yield from operation.to_core(ctx)
            yield '\n'

        # Closing the function
        yield f"}}\n\n"


    @property
    def in_args(self) -> List[Tuple[str, str]]:
        """
        Generates the in_args from the signature
        (e.g "(%arg0: !array.type<2 x !felt.type<"bn128">>, %arg1: !array.type<2 x !felt.type<"bn128">>)
              -> !struct.type<@BinaryAdd_0::@BinaryAdd_0<[]>> attributes" converts to
              [(%arg0, !array.type<2 x !felt.type<"bn128">>), (%arg1: !array.type<2 x !felt.type<"bn128">>)]
              )
        """
        if self._in_args is None:
            arg_inside_parentheses = self.signature.split("->")[0].strip()
            # Skip the ()
            args_with_types = arg_inside_parentheses[1:-1].split(', ')
            _in_args = []
            for arg in args_with_types:
                split_args = arg.split(":")
                # We need to transform the arguments to core
                _in_args.append((split_args[0].strip(), Type.parse(split_args[1].strip()).to_core()))
            self._in_args = _in_args
        return self._in_args

    @property
    def out_args(self) -> List[Tuple[str, str]]:
        raise NotImplementedError

    def __repr__(self):
        body_str = '\n  '.join(repr(op) for op in self.body)
        return f"FunctionDef({self.sym_name}{self.signature} {{\n  {body_str}\n}})"


class FunctionDialect(Dialect):
    """Registry for all function dialect operations."""

    def __init__(self):
        super().__init__("function")
        self.register(FunctionReturn)
        self.register(FunctionCall)
        # FunctionDef is a BlockOperation; dispatched separately by LLZKParser
        self.register(FunctionDef)
