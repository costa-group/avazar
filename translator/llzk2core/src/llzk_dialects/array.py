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
from typing import List, Optional, Generator

from llzk_dialects.core import Operation, SSAVar, Type, TranslationContext
from llzk_dialects.definitions import Dialect
from llzk_dialects.utils import array_felt_first_dimension, array_felt_dimensions, split_top_level_commas
from llzk_dialects.pod import _parse_pod_fields


def _lin_var(base: str, n_dims: int) -> str:
    """Name for the final linearised index variable derived from base."""
    return f"{base}_lin"


def _linearise_indices(indices: List[SSAVar], dims: List[int], base: str) -> Generator[str, None, None]:
    """
    Emit Core IR statements that compute the row-major linear index for a
    multi-dimensional access.  The final result is stored in ``{base}_lin``.

    For dims=[d0, d1, ..., d_{n-1}] and indices [i0, i1, ..., i_{n-1}]:
        linear = i0*stride0 + i1*stride1 + ... + i_{n-1}*1
    where stride_k = d_{k+1} * d_{k+2} * ... * d_{n-1}.

    Temporary variable names are derived from *base* (the SSA result or rvalue
    name), which is unique within a function in SSA form.
    """
    n = len(dims)
    strides = [1] * n
    for i in range(n - 2, -1, -1):
        strides[i] = dims[i + 1] * strides[i + 1]

    # First term: indices[0] * strides[0]
    idx0 = indices[0].to_core()
    if strides[0] == 1:
        acc = f"{base}_t0"
        yield f"{acc} = {idx0}"
    else:
        s_var = f"{base}_s0"
        acc = f"{base}_t0"
        yield f"{s_var} = {strides[0]}"
        yield f"{acc} = felt.mul {idx0} {s_var}"

    for i in range(1, n):
        idx_i = indices[i].to_core()
        if strides[i] == 1:
            term = f"{base}_t{i}"
            yield f"{term} = {idx_i}"
        else:
            s_var = f"{base}_s{i}"
            term = f"{base}_t{i}"
            yield f"{s_var} = {strides[i]}"
            yield f"{term} = felt.mul {idx_i} {s_var}"

        new_acc = f"{base}_lin" if i == n - 1 else f"{base}_acc{i}"
        yield f"{new_acc} = felt.add {acc} {term}"
        acc = new_acc


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
        self._result = result
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

    @property
    def result(self):
        return self._result

    @property
    def operands(self) -> List[SSAVar]:
        return list(self.elements)

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        if len(self.elements) > 0:
            raise NotImplementedError("array.new not implemented with initial elements")
        dim = array_felt_first_dimension(self.result_type.name)
        if dim is None:
            # Clear stale entries from a prior function that reused this SSA name.
            ctx.array_pod_entries.pop(self._result.name, None)
            ctx.array_struct_entries.pop(self._result.name, None)
            return
        yield f"array.new {dim} {self._result}"

    def __repr__(self):
        elem_str = f" : ({', '.join(repr(e) for e in self.elements)})" if self.elements else ""
        return f"ArrayNew({self._result} = array.new{elem_str} : {self.result_type})"


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
        self._result = result
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
            [Type.parse(t.strip()) for t in split_top_level_commas(m["types"])]
            if m["types"] else []
        )
        return ArrayRead(SSAVar.parse(m["res"]), SSAVar.parse(m["arr"]),
                         indices, types)

    @property
    def result(self):
        return self._result

    @property
    def operands(self) -> List[SSAVar]:
        return [self.arr_ref] + list(self.indices)

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        # Non-felt element types (pod, struct): bookkeeping only, no CORE output.
        if self.types:
            elem_type = self.types[-1]
            if "!pod.type" in elem_type.name or "!struct.type" in elem_type.name:
                if self.indices:
                    idx_const = ctx.var2const.get(self.indices[0].name)
                    if idx_const is not None:
                        arr_name = self.arr_ref.name
                        if "!pod.type" in elem_type.name:
                            pod_name = ctx.array_pod_entries.get(arr_name, {}).get(idx_const)
                            if pod_name is not None and pod_name in ctx.ssa2pod_var:
                                # Copy pod-var dict using source variable names (not re-keyed),
                                # so downstream writes use the same CORE variable names.
                                ctx.ssa2pod_var[self._result.name] = dict(ctx.ssa2pod_var[pod_name])
                            else:
                                # No prior write: create fresh pod vars from the element type.
                                pod_fields = _parse_pod_fields(elem_type.name)
                                if pod_fields:
                                    ctx.ssa2pod_var[self._result.name] = {
                                        field: (f"{self._result.name}_{field}", type_)
                                        for field, type_ in pod_fields.items()
                                    }
                        else:
                            entry = ctx.array_struct_entries.get(arr_name, {}).get(idx_const)
                            if entry is not None:
                                ctx.ssa_to_name[self._result.name] = ctx.ssa_to_name.get(entry, entry)
                return

        if len(self.indices) <= 1:
            idx = self.indices[0].to_core() if self.indices else "0"
            yield f"array.read {self.arr_ref.to_core()}[{idx}] {self._result.to_core()}"
            return

        dims = array_felt_dimensions(self.types[0].name) if self.types else None
        assert dims is not None and len(dims) == len(self.indices), (
            f"ArrayRead: {len(self.indices)}-index read requires type annotation "
            f"with {len(self.indices)} felt dimensions, got {self.types}"
        )
        yield from _linearise_indices(self.indices, dims, self._result.name)
        lin = _lin_var(self._result.name, len(dims))
        yield f"array.read {self.arr_ref.to_core()}[{lin}] {self._result.to_core()}"

    def __repr__(self):
        idx_str = ', '.join(repr(i) for i in self.indices)
        type_str = '' if not self.types else ' : ' + ', '.join(repr(t) for t in self.types)
        return f"ArrayRead({self._result} = array.read {self.arr_ref}[{idx_str}]{type_str})"


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
            [Type.parse(t.strip()) for t in split_top_level_commas(m["types"])]
            if m["types"] else []
        )
        return ArrayWrite(SSAVar.parse(m["arr"]), indices,
                          SSAVar.parse(m["rval"]), types)

    @property
    def operands(self) -> List[SSAVar]:
        return [self.arr_ref] + list(self.indices) + [self.rvalue]

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        # Non-felt element types (pod, struct): update tracking, no CORE output.
        if self.types:
            elem_type = self.types[-1]
            if "!pod.type" in elem_type.name or "!struct.type" in elem_type.name:
                if self.indices:
                    idx_const = ctx.var2const.get(self.indices[0].name)
                    if idx_const is not None:
                        arr_name = self.arr_ref.name
                        if "!pod.type" in elem_type.name:
                            ctx.array_pod_entries.setdefault(arr_name, {})[idx_const] = self.rvalue.name
                        else:
                            ctx.array_struct_entries.setdefault(arr_name, {})[idx_const] = self.rvalue.name
                return

        # Resolve the array ref through ssa_to_name so that writes to a pod field
        # with a semantic name (e.g. "mux.c") go directly into that named array.
        arr_core = ctx.ssa_to_name.get(self.arr_ref.name, self.arr_ref.to_core())

        if len(self.indices) <= 1:
            idx = self.indices[0].to_core() if self.indices else "0"
            yield f"array.write {self.rvalue.to_core()} {arr_core}[{idx}]"
            return

        dims = array_felt_dimensions(self.types[0].name) if self.types else None
        assert dims is not None and len(dims) == len(self.indices), (
            f"ArrayWrite: {len(self.indices)}-index write requires type annotation "
            f"with {len(self.indices)} felt dimensions, got {self.types}"
        )
        # Base the temp names on the rvalue (unique SSA def) to avoid collisions
        # with other reads/writes in the same scope.
        base = self.rvalue.name
        yield from _linearise_indices(self.indices, dims, base)
        lin = _lin_var(base, len(dims))
        yield f"array.write {self.rvalue.to_core()} {arr_core}[{lin}]"

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
        self._result = result
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

    @property
    def result(self):
        return self._result

    @property
    def operands(self) -> List[SSAVar]:
        return [self.arr_ref] + list(self.indices)

    def to_core(self, ctx: TranslationContext) -> str:
        # TODO: implement core translation
        raise NotImplementedError

    def __repr__(self):
        idx_str = ', '.join(repr(i) for i in self.indices)
        return (f"ArrayExtract({self._result} = array.extract "
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
            [Type.parse(t.strip()) for t in split_top_level_commas(m["types"])]
            if m["types"] else []
        )
        return ArrayInsert(SSAVar.parse(m["arr"]), _parse_index_list(m["idx"]),
                           SSAVar.parse(m["rval"]), types)

    @property
    def operands(self) -> List[SSAVar]:
        return [self.arr_ref] + list(self.indices) + [self.rvalue]

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
        self._result = result
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

    @property
    def result(self):
        return self._result

    @property
    def operands(self) -> List[SSAVar]:
        return [self.arr_ref, self.dim]

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        dims = array_felt_dimensions(self.arr_type.name)
        assert dims is not None, \
            f"ArrayLen: requires an array of felt type, got {self.arr_type}"
        dim_idx = ctx.var2const.get(self.dim.name)
        assert dim_idx is not None, \
            f"ArrayLen: dimension index {self.dim} must be a known constant at translation time"
        assert 0 <= dim_idx < len(dims), \
            f"ArrayLen: dimension index {dim_idx} out of range for {len(dims)}-D array"
        ctx.var2const[self._result.name] = dims[dim_idx]
        yield f"{self._result.to_core()} = {dims[dim_idx]}"

    def __repr__(self):
        return (f"ArrayLen({self._result} = array.len "
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
