"""
Array dialect — N-dimensional array creation and access operations.
Prefix: array.

Types:
  ArrayType — !array.type<elementType, dim0 x dim1 x ... x elementType>

Operations:
  ArrayNew     — array.new     (create a new array, optionally with elements)
  ArrayRead    — array.read    (read a scalar element by indices)
  ArrayWrite   — array.write   (write a scalar element by indices)
  ArrayExtract — array.extract (read a sub-array by partial indices)
  ArrayInsert  — array.insert  (write a sub-array by partial indices)
  ArrayLen     — array.len     (return the length of a dimension)
"""

import re
from typing import List, Optional

from llzk_dialects.core import Operation, SSAVar, Type, TranslationContext
from llzk_dialects.definitions import Dialect


def _parse_index_list(raw: Optional[str]) -> List[SSAVar]:
    """Parse a bracket-enclosed, comma-separated list of SSA index variables."""
    if not raw:
        return []
    return [SSAVar.parse(v.strip()) for v in raw.split(",") if v.strip()]


class ArrayNew(Operation):
    """
    Create a new array, optionally initialised with element values.

    Syntax: %result = array.new [: ($elements)?] : type($result)
    Example (empty):    %a = array.new : !array.type<index, 4 x index>
    Example (elements): %a = array.new : (%x, %y) : !array.type<index, 2 x index>
    Operands: elements (variadic), mapOperands (variadic index, for affine shapes)
    Result:   n-dimensional array
    """

    _OPS = {"array.new"}

    def __init__(self, result: SSAVar, elements: List[SSAVar], result_type: Type):
        self.result = result
        self.elements = elements
        self.result_type = result_type

    def dialect(self) -> Dialect:
        return Dialect("array")

    @staticmethod
    def match(line: str) -> bool:
        return line.split('=')[-1].strip().split()[0] in ArrayNew._OPS

    @classmethod
    def parse(cls, line: str) -> 'ArrayNew':
        # %r = array.new : !type
        # %r = array.new : (%e0, %e1) : !type
        pattern = re.compile(
            r"\s*(?P<res>\S+)\s*=\s*array\.new"
            r"(?:\s*:\s*\(\s*(?P<elems>[^)]*)\s*\))?"
            r"\s*:\s*(?P<type>.+)\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse ArrayNew: {line}")
        elements = (
            [SSAVar.parse(e.strip()) for e in m["elems"].split(",") if e.strip()]
            if m["elems"] else []
        )
        return ArrayNew(SSAVar.parse(m["res"]), elements, Type.parse(m["type"].strip()))

    def to_core(self, ctx: TranslationContext) -> str:
        # TODO: implement core translation
        raise NotImplementedError

    def __repr__(self):
        elem_str = f" : ({', '.join(repr(e) for e in self.elements)})" if self.elements else ""
        return f"ArrayNew({self.result} = array.new{elem_str} : {self.result_type})"


class ArrayRead(Operation):
    """
    Read a scalar element from an array by a full set of indices.

    Syntax: %result = array.read $arr_ref [$indices] : type($arr_ref), type($result)
    Operands: arr_ref (n-dimensional array), indices (variadic index)
    Result:   valid array element type
    """

    _OPS = {"array.read"}

    def __init__(self, result: SSAVar, arr_ref: SSAVar,
                 indices: List[SSAVar], types: List[Type]):
        self.result = result
        self.arr_ref = arr_ref
        self.indices = indices
        self.types = types

    def dialect(self) -> Dialect:
        return Dialect("array")

    @staticmethod
    def match(line: str) -> bool:
        return line.split('=')[-1].strip().split()[0] in ArrayRead._OPS

    @classmethod
    def parse(cls, line: str) -> 'ArrayRead':
        # %r = array.read %arr [%i0, %i1] : !array.type<...>, !felt.type
        pattern = re.compile(
            r"\s*(?P<res>\S+)\s*=\s*array\.read\s+(?P<arr>\S+)"
            r"\s*\[\s*(?P<idx>[^\]]*)\s*\]"
            r"(?:\s*:\s*(?P<types>.+))?\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse ArrayRead: {line}")
        indices = _parse_index_list(m["idx"])
        types = (
            [Type.parse(t.strip()) for t in m["types"].split(",")]
            if m["types"] else []
        )
        return ArrayRead(SSAVar.parse(m["res"]), SSAVar.parse(m["arr"]),
                         indices, types)

    def to_core(self, ctx: TranslationContext) -> str:
        # TODO: implement core translation
        raise NotImplementedError

    def __repr__(self):
        idx_str = ', '.join(repr(i) for i in self.indices)
        type_str = '' if not self.types else ' : ' + ', '.join(repr(t) for t in self.types)
        return f"ArrayRead({self.result} = array.read {self.arr_ref}[{idx_str}]{type_str})"


class ArrayWrite(Operation):
    """
    Write a scalar element into an array by a full set of indices.

    Syntax: array.write $arr_ref [$indices] = $rvalue : type($arr_ref), type($rvalue)
    Operands: arr_ref, indices (variadic index), rvalue
    No result.
    """

    _OPS = {"array.write"}

    def __init__(self, arr_ref: SSAVar, indices: List[SSAVar],
                 rvalue: SSAVar, types: List[Type]):
        self.arr_ref = arr_ref
        self.indices = indices
        self.rvalue = rvalue
        self.types = types

    def dialect(self) -> Dialect:
        return Dialect("array")

    @staticmethod
    def match(line: str) -> bool:
        return line.strip().split()[0] in ArrayWrite._OPS

    @classmethod
    def parse(cls, line: str) -> 'ArrayWrite':
        # array.write %arr [%i0] = %val : !array.type<...>, !felt.type
        pattern = re.compile(
            r"\s*array\.write\s+(?P<arr>\S+)"
            r"\s*\[\s*(?P<idx>[^\]]*)\s*\]"
            r"\s*=\s*(?P<rval>\S+)"
            r"(?:\s*:\s*(?P<types>.+))?\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse ArrayWrite: {line}")
        indices = _parse_index_list(m["idx"])
        types = (
            [Type.parse(t.strip()) for t in m["types"].split(",")]
            if m["types"] else []
        )
        return ArrayWrite(SSAVar.parse(m["arr"]), indices,
                          SSAVar.parse(m["rval"]), types)

    def to_core(self, ctx: TranslationContext) -> str:
        # TODO: implement core translation
        raise NotImplementedError

    def __repr__(self):
        idx_str = ', '.join(repr(i) for i in self.indices)
        type_str = '' if not self.types else ' : ' + ', '.join(repr(t) for t in self.types)
        return f"ArrayWrite(array.write {self.arr_ref}[{idx_str}] = {self.rvalue}{type_str})"


class ArrayExtract(Operation):
    """
    Read a sub-array from a multi-dimensional array (partial index set).

    Syntax: %result = array.extract $arr_ref [$indices] : type($arr_ref)
    Operands: arr_ref (n-dimensional array), indices (variadic index, partial)
    Result:   n-dimensional array (lower rank than arr_ref)
    """

    _OPS = {"array.extract"}

    def __init__(self, result: SSAVar, arr_ref: SSAVar,
                 indices: List[SSAVar], arr_type: Type):
        self.result = result
        self.arr_ref = arr_ref
        self.indices = indices
        self.arr_type = arr_type

    def dialect(self) -> Dialect:
        return Dialect("array")

    @staticmethod
    def match(line: str) -> bool:
        return line.split('=')[-1].strip().split()[0] in ArrayExtract._OPS

    @classmethod
    def parse(cls, line: str) -> 'ArrayExtract':
        pattern = re.compile(
            r"\s*(?P<res>\S+)\s*=\s*array\.extract\s+(?P<arr>\S+)"
            r"\s*\[\s*(?P<idx>[^\]]*)\s*\]"
            r"\s*:\s*(?P<type>.+)\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse ArrayExtract: {line}")
        return ArrayExtract(SSAVar.parse(m["res"]), SSAVar.parse(m["arr"]),
                            _parse_index_list(m["idx"]), Type.parse(m["type"].strip()))

    def to_core(self, ctx: TranslationContext) -> str:
        # TODO: implement core translation
        raise NotImplementedError

    def __repr__(self):
        idx_str = ', '.join(repr(i) for i in self.indices)
        return (f"ArrayExtract({self.result} = array.extract "
                f"{self.arr_ref}[{idx_str}] : {self.arr_type})")


class ArrayInsert(Operation):
    """
    Write a sub-array into a multi-dimensional array (partial index set).

    Syntax: array.insert $arr_ref [$indices] = $rvalue : type($arr_ref), type($rvalue)
    Operands: arr_ref, indices (variadic, partial), rvalue (sub-array)
    No result.
    """

    _OPS = {"array.insert"}

    def __init__(self, arr_ref: SSAVar, indices: List[SSAVar],
                 rvalue: SSAVar, types: List[Type]):
        self.arr_ref = arr_ref
        self.indices = indices
        self.rvalue = rvalue
        self.types = types

    def dialect(self) -> Dialect:
        return Dialect("array")

    @staticmethod
    def match(line: str) -> bool:
        return line.strip().split()[0] in ArrayInsert._OPS

    @classmethod
    def parse(cls, line: str) -> 'ArrayInsert':
        pattern = re.compile(
            r"\s*array\.insert\s+(?P<arr>\S+)"
            r"\s*\[\s*(?P<idx>[^\]]*)\s*\]"
            r"\s*=\s*(?P<rval>\S+)"
            r"(?:\s*:\s*(?P<types>.+))?\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse ArrayInsert: {line}")
        types = (
            [Type.parse(t.strip()) for t in m["types"].split(",")]
            if m["types"] else []
        )
        return ArrayInsert(SSAVar.parse(m["arr"]), _parse_index_list(m["idx"]),
                           SSAVar.parse(m["rval"]), types)

    def to_core(self, ctx: TranslationContext) -> str:
        # TODO: implement core translation
        raise NotImplementedError

    def __repr__(self):
        idx_str = ', '.join(repr(i) for i in self.indices)
        type_str = '' if not self.types else ' : ' + ', '.join(repr(t) for t in self.types)
        return f"ArrayInsert(array.insert {self.arr_ref}[{idx_str}] = {self.rvalue}{type_str})"


class ArrayLen(Operation):
    """
    Return the length of a specific dimension of an array.

    Syntax: %length = array.len $arr_ref, $dim : type($arr_ref)
    Operands: arr_ref (n-dimensional array), dim (index — dimension number)
    Result:   index (the length)
    """

    _OPS = {"array.len"}

    def __init__(self, result: SSAVar, arr_ref: SSAVar,
                 dim: SSAVar, arr_type: Type):
        self.result = result
        self.arr_ref = arr_ref
        self.dim = dim
        self.arr_type = arr_type

    def dialect(self) -> Dialect:
        return Dialect("array")

    @staticmethod
    def match(line: str) -> bool:
        return line.split('=')[-1].strip().split()[0] in ArrayLen._OPS

    @classmethod
    def parse(cls, line: str) -> 'ArrayLen':
        pattern = re.compile(
            r"\s*(?P<res>\S+)\s*=\s*array\.len\s+(?P<arr>\S+)"
            r"\s*,\s*(?P<dim>\S+)"
            r"\s*:\s*(?P<type>.+)\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse ArrayLen: {line}")
        return ArrayLen(SSAVar.parse(m["res"]), SSAVar.parse(m["arr"]),
                        SSAVar.parse(m["dim"]), Type.parse(m["type"].strip()))

    def to_core(self, ctx: TranslationContext) -> str:
        # TODO: implement core translation
        raise NotImplementedError

    def __repr__(self):
        return (f"ArrayLen({self.result} = array.len "
                f"{self.arr_ref}, {self.dim} : {self.arr_type})")


class ArrayDialect(Dialect):
    """Registry for all array dialect operations."""

    def __init__(self):
        super().__init__("array")
        self.register(ArrayNew)
        self.register(ArrayRead)
        self.register(ArrayWrite)
        self.register(ArrayExtract)
        self.register(ArrayInsert)
        self.register(ArrayLen)
