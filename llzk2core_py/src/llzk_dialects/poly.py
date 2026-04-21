"""
Poly dialect — polymorphic / templated constructs.
Prefix: poly.

Operations:
  PolyApplyMap     — poly.applymap     (evaluate an AffineMap over index operands)
  PolyReadConst    — poly.read_const   (read a struct template parameter value)
  PolyUnifiableCast— poly.unifiable_cast (cast between two unifiable types)
  PolyParam        — poly.param        (declare a parameter inside a poly.template)
  PolyYield        — poly.yield        (yield a value from a poly.expr body)
  PolyExpr         — poly.expr         (BlockOperation: named expression in a template)
  PolyTemplate     — poly.template     (BlockOperation: define a polymorphic template)

Types:
  TypeVarType — !poly.tvar<nameRef>  (placeholder for a template type parameter)
"""

import re
from typing import List, Optional, Tuple, Generator

from llzk_dialects.core import (
    Operation, BlockOperation, SSAVar, GlobalVariable, Type,
    TranslationContext, ParseFn,
)
from llzk_dialects.definitions import Dialect


class PolyApplyMap(Operation):
    """
    Evaluate an AffineMap over a set of index operands.

    Syntax: %result = poly.applymap ($mapOperands) [$numDims] $map
    Operands: mapOperands (variadic index)
    Result:   index
    Attributes: map (AffineMapAttr), numDims (IntegerAttr)
    """

    _OPS = {"poly.applymap"}

    def __init__(self, result: SSAVar, operands: List[SSAVar],
                 num_dims: int, affine_map: str):
        self.result = result
        self.operands = operands
        self.num_dims = num_dims
        self.affine_map = affine_map

    def dialect(self) -> Dialect:
        return Dialect("poly")

    @staticmethod
    def match(line: str) -> bool:
        return line.split('=')[-1].strip().split()[0] in PolyApplyMap._OPS

    @classmethod
    def parse(cls, line: str) -> 'PolyApplyMap':
        # %r = poly.applymap (%op0, %op1) [2] affine_map<...>
        pattern = re.compile(
            r"\s*(?P<res>\S+)\s*=\s*poly\.applymap"
            r"\s*\(\s*(?P<ops>[^)]*)\s*\)"
            r"\s*\[\s*(?P<ndims>\d+)\s*\]"
            r"\s*(?P<map>.+)\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse PolyApplyMap: {line}")
        ops = [SSAVar.parse(o.strip()) for o in m["ops"].split(",") if o.strip()]
        return PolyApplyMap(SSAVar.parse(m["res"]), ops,
                            int(m["ndims"]), m["map"].strip())

    def to_core(self, ctx: TranslationContext) -> str:
        # TODO: implement core translation
        raise NotImplementedError

    def __repr__(self):
        ops_str = ', '.join(repr(o) for o in self.operands)
        return (f"PolyApplyMap({self.result} = poly.applymap"
                f"({ops_str})[{self.num_dims}] {self.affine_map})")


class PolyReadConst(Operation):
    """
    Read the value of a struct template parameter (compile-time constant).

    Syntax: %val = poly.read_const @const_name : type($val)
    Attributes: const_name (FlatSymbolRefAttr)
    Result:     integral, felt, or typevar type
    """

    _OPS = {"poly.read_const"}

    def __init__(self, result: SSAVar, const_name: GlobalVariable,
                 result_type: Type):
        self.result = result
        self.const_name = const_name
        self.result_type = result_type

    def dialect(self) -> Dialect:
        return Dialect("poly")

    @staticmethod
    def match(line: str) -> bool:
        return line.split('=')[-1].strip().split()[0] in PolyReadConst._OPS

    @classmethod
    def parse(cls, line: str) -> 'PolyReadConst':
        pattern = re.compile(
            r"\s*(?P<res>\S+)\s*=\s*poly\.read_const\s+(?P<name>@\S+)"
            r"\s*:\s*(?P<type>.+)\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse PolyReadConst: {line}")
        return PolyReadConst(SSAVar.parse(m["res"]),
                             GlobalVariable.parse(m["name"]),
                             Type.parse(m["type"].strip()))

    def to_core(self, ctx: TranslationContext) -> str:
        # TODO: implement core translation
        raise NotImplementedError

    def __repr__(self):
        return (f"PolyReadConst({self.result} = poly.read_const "
                f"{self.const_name} : {self.result_type})")


class PolyUnifiableCast(Operation):
    """
    Cast between two unifiable types (e.g. concrete type ↔ type variable).

    Syntax: %result = poly.unifiable_cast $input : type($input) -> type($result)
    Operand: input (valid LLZK type)
    Result:  valid LLZK type
    """

    _OPS = {"poly.unifiable_cast"}

    def __init__(self, result: SSAVar, input_val: SSAVar,
                 input_type: Type, result_type: Type):
        self.result = result
        self.input_val = input_val
        self.input_type = input_type
        self.result_type = result_type

    def dialect(self) -> Dialect:
        return Dialect("poly")

    @staticmethod
    def match(line: str) -> bool:
        return line.split('=')[-1].strip().split()[0] in PolyUnifiableCast._OPS

    @classmethod
    def parse(cls, line: str) -> 'PolyUnifiableCast':
        # %r = poly.unifiable_cast %input : !in_type -> !out_type
        pattern = re.compile(
            r"\s*(?P<res>\S+)\s*=\s*poly\.unifiable_cast\s+(?P<inp>\S+)"
            r"\s*:\s*(?P<intype>.+?)\s*->\s*(?P<outtype>.+)\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse PolyUnifiableCast: {line}")
        return PolyUnifiableCast(SSAVar.parse(m["res"]), SSAVar.parse(m["inp"]),
                                 Type.parse(m["intype"].strip()), Type.parse(m["outtype"].strip()))

    def to_core(self, ctx: TranslationContext) -> str:
        # TODO: implement core translation
        raise NotImplementedError

    def __repr__(self):
        return (f"PolyUnifiableCast({self.result} = poly.unifiable_cast "
                f"{self.input_val} : {self.input_type} -> {self.result_type})")


class PolyParam(Operation):
    """
    Declare a parameter of a polymorphic template.

    Syntax: poly.param @sym_name [: $type_opt]
    Attributes: sym_name (StringAttr), type_opt (TypeAttr, optional)
    Valid parent: TemplateOp
    """

    _OPS = {"poly.param"}

    def __init__(self, sym_name: GlobalVariable, type_opt: Optional[Type]):
        self.sym_name = sym_name
        self.type_opt = type_opt

    def dialect(self) -> Dialect:
        return Dialect("poly")

    @staticmethod
    def match(line: str) -> bool:
        return line.strip().split()[0] in PolyParam._OPS

    @classmethod
    def parse(cls, line: str) -> 'PolyParam':
        pattern = re.compile(
            r"\s*poly\.param\s+(?P<name>@\S+)"
            r"(?:\s*:\s*(?P<type>.+?))?\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse PolyParam: {line}")
        type_opt = Type.parse(m["type"].strip()) if m["type"] else None
        return PolyParam(GlobalVariable.parse(m["name"]), type_opt)

    def to_core(self, ctx: TranslationContext) -> str:
        # TODO: implement core translation
        raise NotImplementedError

    def __repr__(self):
        type_str = f" : {self.type_opt}" if self.type_opt else ""
        return f"PolyParam(poly.param {self.sym_name}{type_str})"


class PolyYield(Operation):
    """
    Yield a value from a poly.expr body, acting as its terminator.

    Syntax: poly.yield $val : type($val)
    Operand: val (integral, felt, or typevar type)
    Traits: Terminator, ReturnLike
    Valid parent: TemplateExprOp (poly.expr body)
    """

    _OPS = {"poly.yield"}

    def __init__(self, value: SSAVar, value_type: Type):
        self.value = value
        self.value_type = value_type

    def dialect(self) -> Dialect:
        return Dialect("poly")

    @staticmethod
    def match(line: str) -> bool:
        return line.strip().split()[0] in PolyYield._OPS

    @classmethod
    def parse(cls, line: str) -> 'PolyYield':
        pattern = re.compile(
            r"\s*poly\.yield\s+(?P<val>\S+)\s*:\s*(?P<type>.+)\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse PolyYield: {line}")
        return PolyYield(SSAVar.parse(m["val"]), Type.parse(m["type"].strip()))

    def to_core(self, ctx: TranslationContext) -> str:
        # TODO: implement core translation
        raise NotImplementedError

    def __repr__(self):
        return f"PolyYield(poly.yield {self.value} : {self.value_type})"


class PolyExpr(BlockOperation):
    """
    Declare a named compile-time expression inside a poly.template.

    Syntax:
      poly.expr @sym_name {
        <body — must end with poly.yield>
      }

    The body is parsed recursively and stored as a list of Operations.
    Attributes: sym_name (StringAttr)
    Traits: IsolatedFromAbove, SingleBlock, NoRegionArguments
    Valid parent: TemplateOp (poly.template)
    """

    _OPS = {"poly.expr"}

    def __init__(self, sym_name: GlobalVariable, body: List[Operation]):
        self.sym_name = sym_name
        self.body = body

    def dialect(self) -> Dialect:
        return Dialect("poly")

    @staticmethod
    def match(line: str) -> bool:
        return line.strip().split()[0] in PolyExpr._OPS

    @classmethod
    def parse(cls, lines: List[str], cursor: int,
              parse_fn: ParseFn) -> Tuple['PolyExpr', int]:
        header = lines[cursor]
        pattern = re.compile(r"\s*poly\.expr\s+(?P<name>@\S+)\s*\{")
        m = re.match(pattern, header)
        if not m:
            raise ValueError(f"Failed to parse PolyExpr header: {header}")

        depth = header.count('{') - header.count('}')
        end = cursor
        while depth > 0 and end + 1 < len(lines):
            end += 1
            depth += lines[end].count('{') - lines[end].count('}')

        body = parse_fn(cursor + 1, end)
        return PolyExpr(GlobalVariable.parse(m["name"]), body), end + 1

    def to_core(self, ctx: TranslationContext) -> str:
        # TODO: implement core translation
        raise NotImplementedError

    def __repr__(self):
        body_str = '\n  '.join(repr(op) for op in self.body)
        return f"PolyExpr({self.sym_name} {{\n  {body_str}\n}})"


class PolyTemplate(BlockOperation):
    """
    Define a polymorphic template that can contain poly.param, poly.expr,
    struct.def, and function.def children.

    Syntax:
      poly.template @TemplateName {
        poly.param @P
        poly.expr @e { ... }
        struct.def @S { ... }
      }

    The body is parsed recursively using parse_fn.
    Attributes: sym_name (StringAttr)
    Traits: SymbolTable, IsolatedFromAbove, SingleBlock
    Valid parent: ModuleOp
    """

    _OPS = {"poly.template"}

    def __init__(self, sym_name: GlobalVariable, body: List[Operation]):
        self.sym_name = sym_name
        self.body = body

    def dialect(self) -> Dialect:
        return Dialect("poly")

    @staticmethod
    def match(line: str) -> bool:
        return line.strip().split()[0] in PolyTemplate._OPS

    @classmethod
    def parse(cls, lines: List[str], cursor: int,
              parse_fn: ParseFn) -> Tuple['PolyTemplate', int]:
        header = lines[cursor]
        pattern = re.compile(r"\s*poly\.template\s+(?P<name>@\S+)\s*\{")
        m = re.match(pattern, header)
        if not m:
            raise ValueError(f"Failed to parse PolyTemplate header: {header}")

        depth = header.count('{') - header.count('}')
        end = cursor
        while depth > 0 and end + 1 < len(lines):
            end += 1
            depth += lines[end].count('{') - lines[end].count('}')

        body = parse_fn(cursor + 1, end)
        return PolyTemplate(GlobalVariable.parse(m["name"]), body), end + 1

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        # Translation to core. Assumes there is only one struct defined inside the body.
        # Otherwise, it raises an Error so that the example can be studied in more detail.
        assert len(self.body) == 1, "PolyTemplate in module poly.py assumes there is only one struct to translate"

        # Assign the current poly template to the context
        ctx.current_template = self.sym_name.name

        # Although it is just one element, we iterate for completeness just in case
        for struct_element in self.body:
            yield from struct_element.to_core(ctx)


    def __repr__(self):
        body_str = '\n  '.join(repr(op) for op in self.body)
        return f"PolyTemplate({self.sym_name} {{\n  {body_str}\n}})"


class PolyDialect(Dialect):
    """Registry for all poly dialect operations."""

    def __init__(self):
        super().__init__("poly")
        self.register(PolyApplyMap)
        self.register(PolyReadConst)
        self.register(PolyUnifiableCast)
        self.register(PolyParam)
        self.register(PolyYield)
        # Block ops dispatched separately by LLZKParser
        self.register(PolyExpr)
        self.register(PolyTemplate)
