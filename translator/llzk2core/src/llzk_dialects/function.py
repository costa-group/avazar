"""
Function dialect — function definition, calls, and returns.
Prefix: function.

Operations:
  FunctionDef    — function.def    (BlockOperation: defines a function with a body)
  FunctionCall   — function.call   (call a named function)
  FunctionReturn — function.return (return from a function, optionally with values)
"""

import re
from typing import List, Optional, Tuple, Dict, Generator

from llzk_dialects.core import (
    Operation, BlockOperation, SSAVar, GlobalVariable, Type,
    TranslationContext, ParseFn,
)
from llzk_dialects.definitions import Dialect
from llzk_dialects.core_utils import signature_args
from llzk_dialects.utils import split_top_level_commas


def _parse_in_arg(arg: str) -> Tuple[str, str, str]:
    """
    Splits a single argument declaration (e.g.
    '%arg0: !array.type<2,2 x !felt.type<"bn128">> {function.arg_name = "in", llzk.pub}')
    into (name, type_str, attrs_str). attrs_str is '' when there's no
    trailing attribute dict. The dict is found by scanning from the end of
    the string (tracking brace depth) rather than just splitting on '{', so
    a multi-attribute dict — whose own comma would otherwise be mistaken for
    an argument separator by a naive split — is correctly recognised and
    stripped from the type instead of leaking into it.
    """
    arg = arg.strip()
    name, _, rest = arg.partition(":")
    rest = rest.strip()
    attrs = ""
    if rest.endswith("}"):
        depth = 0
        for i in range(len(rest) - 1, -1, -1):
            if rest[i] == '}':
                depth += 1
            elif rest[i] == '{':
                depth -= 1
                if depth == 0:
                    attrs = rest[i + 1:-1]
                    rest = rest[:i].strip()
                    break
    return name.strip(), rest, attrs


class FunctionReturn(Operation):
    """
    Return from a function, optionally carrying result values.

    Syntax: function.return [($operands : type($operands))?]
    Operands: operands (variadic valid LLZK type, optional)
    Traits: Terminator, ReturnLike
    """

    _OPS = {"function.return"}

    def __init__(self, operands: List[SSAVar], types: List[Type]):
        self._operands = operands
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

    @property
    def operands(self) -> List[SSAVar]:
        return self._operands

    def to_core(self, ctx: TranslationContext) -> str:
        # Returns does nothing, as the returned arguments
        #  are specified in the signature
        yield from ()

    def __repr__(self):
        if not self._operands:
            return "FunctionReturn(function.return)"
        ops_str = ', '.join(repr(o) for o in self._operands)
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
        self.func_type = func_type
        # Set by the pre-pass in _build_component_naming_maps; None until then.
        self._member_hint: Optional[str] = None

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

    @property
    def result(self) -> Optional[SSAVar]:
        return self.results[0] if self.results else None

    @property
    def operands(self) -> List[SSAVar]:
        return list(self.args)

    def to_core(self, ctx: TranslationContext) -> str:
        # Resolve argument SSA vars to semantic names where available
        args = ','.join(ctx.ssa_to_name.get(arg.name, arg.to_core()) for arg in self.args)
        core_func = ctx.llzk_func2core[self.callee.name]
        _, out_args = ctx.core_func2args[core_func]

        assert len(self.results) == 1, "A function call must return a single result: the template itself. " \
                                       "But {self.results} is returned instead"
        result = self.results[0]

        member = self._member_hint

        if member:
            out_var_names = []
            for out_arg, _ in out_args:
                out_name = f"{member}.{out_arg[1:]}"  # strip @ from out_arg
                ctx.ssa_to_name[f"{result.name}_{out_arg}"] = out_name
                out_var_names.append(out_name)
        else:
            out_var_names = [f"{result.name}_{out_arg}" for out_arg, _ in out_args]

        yield f"call {core_func}({args}) to {','.join(out_var_names)}"

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
        self._in_arg_names = None

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
        name_pattern = re.compile(r"\s*function\.def\s+(?P<name>@[^\s(]+)")
        m = re.match(name_pattern, header)
        if not m:
            raise ValueError(f"Failed to parse FunctionDef header: {header}")

        # The signature (args, return type, attributes) may itself contain
        # balanced '{...}' groups — a per-argument attribute dict (e.g.
        # "%arg0: !type {llzk.pub}") or a trailing "attributes {...}" clause
        # — before the function body's own opening brace. A naive "stop at
        # the first '{'" search would truncate the signature right at the
        # first such group, silently dropping any argument declared after
        # it. Track a bracket stack instead: every '{' is pushed, every '}'
        # pops its match, and whatever's left unmatched at the end of the
        # line is the body's real opening brace.
        stack = []
        for i in range(m.end(), len(header)):
            ch = header[i]
            if ch == '{':
                stack.append(i)
            elif ch == '}' and stack:
                stack.pop()
        if not stack:
            raise ValueError(f"Failed to find function body opening brace: {header}")
        body_brace = stack[-1]
        sig = header[m.end():body_brace]

        # Find matching closing brace
        depth = header.count('{') - header.count('}')
        end = cursor
        while depth > 0 and end + 1 < len(lines):
            end += 1
            depth += lines[end].count('{') - lines[end].count('}')

        body = parse_fn(cursor + 1, end)
        return (
            FunctionDef(GlobalVariable.parse(m["name"]), sig.strip(), body),
            end + 1,
        )

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        # Translating a function assumes that the output (and input) information
        # is already stored in the context. This is because CORE does not exactly
        # share the same signature (in particular, out_args are public struct members).
        core_name = ctx.current_core_function
        in_args, out_args = ctx.core_func2args[core_name]

        ctx.param_arg_names.update(self.in_arg_names)

        signature_in = signature_args(in_args)
        signature_out = ', '.join(f"{arg[1:]}: {type_.to_core()}" for arg, type_ in out_args)

        # We start with the declaration of the function and the args
        yield f"def {core_name}({signature_in}) -> {signature_out} {{\n"

        for operation in self.body:
            yield from operation.to_core(ctx)
            yield '\n'

        # Closing the function
        yield f"}}\n\n"


    @property
    def in_args(self) -> List[Tuple[str, Type]]:
        """
        Generates the in_args from the signature
        (e.g "(%arg0: !array.type<2 x !felt.type<"bn128">>, %arg1: !array.type<2 x !felt.type<"bn128">>)
              -> !struct.type<@BinaryAdd_0::@BinaryAdd_0<[]>> attributes" converts to
              [(%arg0, !array.type<2 x !felt.type<"bn128">>), (%arg1: !array.type<2 x !felt.type<"bn128">>)]
              )
        """
        if self._in_args is None:
            arg_inside_parentheses = self.signature.split("->")[0].strip()
            # Skip the (); split_top_level_commas (not a naive ', ' split) so
            # a comma inside an argument's own attribute dict — e.g.
            # "{function.arg_name = \"in\", llzk.pub}" — isn't mistaken for
            # an argument separator.
            args_with_types = [
                arg for arg in split_top_level_commas(arg_inside_parentheses[1:-1]) if arg.strip() != ""
            ]
            _in_args = []
            for arg in args_with_types:
                name, type_str, _ = _parse_in_arg(arg)
                _in_args.append((name, Type.parse(type_str)))
            self._in_args = _in_args
        return self._in_args

    @property
    def in_arg_names(self) -> Dict[str, str]:
        """
        Maps each input parameter's SSA name to its 'function.arg_name'
        attribute value, when present (e.g. "%arg0" -> "c"), parsed from the
        same raw signature text as in_args. Parameters without this
        attribute are omitted.
        """
        if self._in_arg_names is None:
            arg_inside_parentheses = self.signature.split("->")[0].strip()
            args_with_types = [
                arg for arg in split_top_level_commas(arg_inside_parentheses[1:-1]) if arg.strip() != ""
            ]
            result = {}
            for arg in args_with_types:
                name, _, attrs = _parse_in_arg(arg)
                m = re.search(r'function\.arg_name\s*=\s*"([^"]*)"', attrs)
                if m:
                    result[name] = m.group(1)
            self._in_arg_names = result
        return self._in_arg_names

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
