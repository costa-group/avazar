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

Container element types (pod, struct):
  CORE arrays only hold ff. An array whose element type is pod or struct is
  translated as a structure-of-arrays: one real flattened CORE array per leaf
  field of the element type (recursing through nested pod/struct fields; a
  leaf that is itself array-typed just contributes its own size as a
  multiplier). See _flatten_container_fields.
"""

import re
from typing import List, Optional, Generator, Tuple, Union

from llzk_dialects.core import Operation, SSAVar, Type, TranslationContext, LoopIndexedName
from llzk_dialects.definitions import Dialect
from llzk_dialects.utils import (
    array_felt_first_dimension, array_felt_dimensions,
    array_dimensions, array_total_size, split_top_level_commas,
    struct_type_name,
)
from llzk_dialects.pod import _parse_pod_fields, _register_nested_pod_vars


def _lin_var(base: str, n_dims: int) -> str:
    """Name for the final linearised index variable derived from base."""
    return f"{base}_lin"


def _row_major_strides(dims: List[int]) -> List[int]:
    """
    Row-major strides for *dims*: stride_k = d_{k+1} * d_{k+2} * ... * d_{n-1}
    (the last dimension always has stride 1).
    """
    n = len(dims)
    strides = [1] * n
    for i in range(n - 2, -1, -1):
        strides[i] = dims[i + 1] * strides[i + 1]
    return strides


def _linearise_indices(indices: List[SSAVar], dims: List[int], base: str) -> Generator[str, None, None]:
    """
    Emit Core IR statements that compute the row-major linear index for a
    (possibly partial) multi-dimensional access. The final result is stored
    in ``{base}_lin``.

    For dims=[d0, ..., d_{n-1}] and indices=[i0, ..., i_{k-1}] (k <= n):
        linear = i0*stride0 + i1*stride1 + ... + i_{k-1}*stride_{k-1}
    where stride_j = d_{j+1} * ... * d_{n-1} — computed from the FULL dims, so
    a partial index set (as used by array.insert/array.extract) correctly
    accounts for the unindexed trailing dimensions.

    Temporary variable names are derived from *base* (the SSA result or
    rvalue name), which is unique within a function in SSA form.
    """
    strides = _row_major_strides(dims)
    k = len(indices)
    assert k >= 1, "_linearise_indices requires at least one index"

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

    if k == 1:
        yield f"{base}_lin = {acc}"
        return

    for i in range(1, k):
        idx_i = indices[i].to_core()
        if strides[i] == 1:
            term = f"{base}_t{i}"
            yield f"{term} = {idx_i}"
        else:
            s_var = f"{base}_s{i}"
            term = f"{base}_t{i}"
            yield f"{s_var} = {strides[i]}"
            yield f"{term} = felt.mul {idx_i} {s_var}"

        new_acc = f"{base}_lin" if i == k - 1 else f"{base}_acc{i}"
        yield f"{new_acc} = felt.add {acc} {term}"
        acc = new_acc


def _parse_index_list(raw: Optional[str]) -> List[SSAVar]:
    """Parse a bracket-enclosed, comma-separated list of SSA index variables."""
    if not raw:
        return []
    return [SSAVar.parse(v.strip()) for v in raw.split(",") if v.strip()]


def _container_field_var(base: str, field_path: List[str]) -> str:
    """Core variable name for a flattened per-field array of a pod/struct array."""
    return base + "_" + "_".join(field_path)


def _semantic_field_var(semantic_base: str, field_path: List[str]) -> str:
    """
    Core variable name for a flattened field of a component read out of a
    named component array (e.g. "last_0.in1_last"), mirroring PodNew's
    "{member}.{record}" convention for a scalar subcomponent — a dot after
    the member/index prefix, then underscore-joined for any nested fields.
    """
    return semantic_base + "." + "_".join(p[1:] for p in field_path)


def _struct_out_args(struct_type_str: str, ctx: TranslationContext) -> List[Tuple[str, Type]]:
    """Resolve a struct type's own output args (name-with-@, Type), via ctx."""
    full_ref = struct_type_name(struct_type_str)
    core_func = ctx.llzk_func2core[f"{full_ref}::@compute"]
    _, out_args = ctx.core_func2args[core_func]
    return out_args


def _flatten_container_fields(type_str: str, ctx: TranslationContext) -> List[Tuple[List[str], Type]]:
    """
    Recursively expand a container element type (pod or struct) into a flat
    list of (field_path, leaf_type) pairs — one real CORE array per leaf
    (structure-of-arrays). A leaf is any type that is not itself pod/struct,
    including an array of felt (its own size just multiplies into the
    leaf's total array size). Empty pods contribute nothing.

    Pod is checked before struct, so a pod containing a struct-typed field
    (whose type string textually contains "!struct.type") isn't mistaken for
    a struct element.
    """
    if "!pod.type" in type_str:
        fields = list(_parse_pod_fields(type_str).items())
    else:
        fields = _struct_out_args(type_str, ctx)

    result: List[Tuple[List[str], Type]] = []
    for field, field_type in fields:
        if "!pod.type" in field_type.name or "!struct.type" in field_type.name:
            for sub_path, leaf_type in _flatten_container_fields(field_type.name, ctx):
                result.append(([field] + sub_path, leaf_type))
        else:
            result.append(([field], field_type))
    return result


def _emit_container_field_copy(src_arr: str, dest_arr: str, start: str, length: int,
                               base: str, offset_src: bool = False) -> Generator[str, None, None]:
    """
    Emit a Core 'repeat' loop copying `length` contiguous elements between
    src_arr and dest_arr. `start` is a Core sexp (a variable name or integer
    literal). Core's repeat has no implicit counter, so one is initialised
    before the loop and advanced inside it (see CORELLZK.md's Bounded Loops).

    Two shapes, depending on which side is the big (structure-of-arrays
    backing) array and which is the small, freshly-allocated one:

    - offset_src=False (default — "insert": copying a small array INTO a
      bigger one, e.g. ArrayWrite/ArrayInsert writing one instance's value
      back into the backing store): copies src_arr[0..length) into
      dest_arr[start..start+length) — the offset lands on the destination.
    - offset_src=True ("extract": copying a slice OUT OF a bigger array
      into a freshly allocated smaller one, e.g. ArrayRead/ArrayExtract
      reading one instance's value out of the backing store): copies
      src_arr[start..start+length) into dest_arr[0..length) instead — the
      offset must land on the source, or the (correctly small) destination
      array would be written out of bounds for any start > 0.
    """
    counter = f"{base}_cp_idx"
    tmp = f"{base}_cp_tmp"
    off = f"{base}_cp_src" if offset_src else f"{base}_cp_dest"
    yield f"{counter} = 0"
    yield f"repeat {length} {{"
    if offset_src:
        yield f"{off} = felt.add {counter} {start}"
        yield f"array.read {src_arr}[{off}] {tmp}"
        yield f"array.write {tmp} {dest_arr}[{counter}]"
    else:
        yield f"array.read {src_arr}[{counter}] {tmp}"
        yield f"{off} = felt.add {counter} {start}"
        yield f"array.write {tmp} {dest_arr}[{off}]"
    yield f"{counter} = felt.add {counter} 1"
    yield "}"


class ArrayNew(Operation):
    """
    Create a new array, optionally initialised with element values.

    Syntax: %result = array.new [$elements] : type($result)
    Example (empty):    %a = array.new : !array.type<index, 4 x index>
    Example (elements): %a = array.new %x, %y : !array.type<index, 2 x index>
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
        # %r = array.new %e0, %e1 : !type
        pattern = re.compile(
            r"\s*(?P<res>\S+)\s*=\s*array\.new"
            r"(?:\s+(?P<elems>%[^\s,]+(?:\s*,\s*%[^\s,]+)*))?"
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
        type_str = self.result_type.name
        dim = array_felt_first_dimension(type_str)
        if dim is not None:
            yield f"array.new {dim} {self._result}"
            if self.elements:
                # Core allows a literal/known value to be written directly
                # into an array slot, so each initial element just becomes a
                # plain array.write at its own index.
                assert len(self.elements) == dim, (
                    f"ArrayNew: {len(self.elements)} initial elements given "
                    f"for a {dim}-element array"
                )
                for i, elem in enumerate(self.elements):
                    yield f"array.write {elem.to_core()} {self._result.to_core()}[{i}]"
            return

        if self.elements:
            raise NotImplementedError(
                "array.new with initial elements is only implemented for felt arrays"
            )

        if "!pod.type" in type_str or "!struct.type" in type_str:
            # Array of pod/struct (structure-of-arrays): one real flattened
            # array per leaf field.
            size = array_total_size(type_str)
            assert size is not None, \
                f"ArrayNew: could not determine size for container array {type_str}"
            for field_path, leaf_type in _flatten_container_fields(type_str, ctx):
                leaf_size = size * (array_total_size(leaf_type.name) or 1)
                yield f"array.new {leaf_size} {_container_field_var(self._result.name, field_path)}"

    def __repr__(self):
        elem_str = f" {', '.join(repr(e) for e in self.elements)}" if self.elements else ""
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
        # Set by struct.py's _build_component_naming_maps pre-pass (via
        # _annotate_input_array_reads) when arr_ref is a registered
        # "$inputs" component array: the plain string "member_idx" for a
        # compile-time constant index, or LoopIndexedName("member") when the
        # index is a genuine runtime loop variable (resolved in to_core
        # below into "member#i" if that loop got unrolled, else bare
        # "member"). None until the pre-pass runs, or when arr_ref isn't a
        # registered component array.
        #
        # This can't be computed here from ctx.var2const at to_core time:
        # SCFFor/SCFWhile deliberately treat their own loop-carried
        # variables as a compile-time constant for structural purposes (see
        # their own to_core), even though the value actually varies per
        # iteration — trusting that here would misattribute a genuinely
        # symbolic loop index to one specific instance. The pre-pass instead
        # resolves this with its own scope-safe static fold, once per
        # function, and stamps the result directly on this node.
        self._semantic_base: Optional[Union[str, LoopIndexedName]] = None

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
        elem_type = self.types[-1] if self.types else None
        is_pod = elem_type is not None and "!pod.type" in elem_type.name
        is_struct = elem_type is not None and not is_pod and "!struct.type" in elem_type.name

        if is_pod or is_struct:
            # Array of pod/struct (structure-of-arrays): fan out into one real
            # array.read per leaf field. Pod results are additionally
            # registered in ssa2pod_var (mirroring PodNew's convention) so
            # downstream pod.read/pod.write keep working; struct results need
            # no registration, since struct.readm resolves member storage by
            # plain name concatenation.
            arr_core = ctx.ssa_to_name.get(self.arr_ref.name, self.arr_ref.to_core())

            # When this array backs a named component-array member, name the
            # extracted element after that member instead of a raw
            # SSA-derived name — see the _semantic_base field comment above
            # for how/when this is resolved. A LoopIndexedName means the
            # index wasn't a compile-time constant in the source IR; resolve
            # it against the current unroll iteration (set by SCFFor/
            # SCFWhile.to_core when they unroll a loop for this exact
            # reason — see scf.py's _contains_function_call), or leave it
            # bare if this loop wasn't unrolled after all.
            semantic_base = self._semantic_base
            if isinstance(semantic_base, LoopIndexedName):
                semantic_base = semantic_base.resolve(ctx.unroll_index)

            if is_pod:
                all_fields = _parse_pod_fields(elem_type.name)
                if semantic_base is not None:
                    ctx.ssa2pod_var[self._result.name] = {
                        field: (_semantic_field_var(semantic_base, [field]), field_type)
                        for field, field_type in all_fields.items()
                    }
                else:
                    ctx.ssa2pod_var[self._result.name] = {
                        field: (f"{self._result.name}_{field}", field_type)
                        for field, field_type in all_fields.items()
                    }
                # A pod-typed field (e.g. @idx_0: !pod.type<[@in: ...]>, or an
                # empty @params: !pod.type<[]>) needs its OWN ctx.ssa2pod_var
                # entry, not just leaf storage from _flatten_container_fields
                # below — otherwise a later pod.read chained through this
                # nested pod (pod-in-pod) finds no registered source. A pod
                # created via pod.new gets this for free (PodNew's own
                # initial-value assignment chain registers it when the source
                # is itself a registered pod), but a pod extracted from an
                # array has no such chain — register it explicitly here.
                for field, field_type in all_fields.items():
                    if "!pod.type" in field_type.name:
                        key = (_semantic_field_var(semantic_base, [field])
                               if semantic_base is not None else f"{self._result.name}_{field}")
                        _register_nested_pod_vars(ctx, key, field_type.name)

            if len(self.indices) <= 1:
                idx = self.indices[0].to_core() if self.indices else "0"
            else:
                dims = array_dimensions(self.types[0].name)
                assert dims is not None and len(dims) == len(self.indices), (
                    f"ArrayRead: {len(self.indices)}-index read requires type annotation "
                    f"with {len(self.indices)} dimensions, got {self.types}"
                )
                base = self._result.name
                yield from _linearise_indices(self.indices, dims, base)
                idx = _lin_var(base, len(dims))

            for field_path, leaf_type in _flatten_container_fields(elem_type.name, ctx):
                src_arr = _container_field_var(arr_core, field_path)
                raw_dest_var = _container_field_var(self._result.name, field_path)
                if semantic_base is not None:
                    dest_var = _semantic_field_var(semantic_base, field_path)
                    ctx.ssa_to_name[raw_dest_var] = dest_var
                else:
                    dest_var = raw_dest_var
                leaf_size = array_total_size(leaf_type.name)
                if leaf_size is None:
                    yield f"array.read {src_arr}[{idx}] {dest_var}"
                else:
                    start_var = f"{dest_var}_off"
                    yield f"{start_var} = felt.mul {idx} {leaf_size}"
                    yield f"array.new {leaf_size} {dest_var}"
                    # Extracting this instance's slice out of the bigger
                    # backing array (src_arr) into the freshly allocated
                    # dest_var — offset belongs on the source, not dest_var.
                    yield from _emit_container_field_copy(src_arr, dest_var, start_var, leaf_size, dest_var,
                                                          offset_src=True)
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
        elem_type = self.types[-1] if self.types else None
        is_pod = elem_type is not None and "!pod.type" in elem_type.name
        is_struct = elem_type is not None and not is_pod and "!struct.type" in elem_type.name

        if is_pod or is_struct:
            # Array of pod/struct (structure-of-arrays): fan out into one real
            # array.write per leaf field. The source variable for each leaf is
            # named by plain concatenation from rvalue.name (matching
            # PodNew/StructReadm's own default naming), resolved through
            # ssa_to_name in case it was given a semantic alias.
            arr_core = ctx.ssa_to_name.get(self.arr_ref.name, self.arr_ref.to_core())

            if len(self.indices) <= 1:
                idx = self.indices[0].to_core() if self.indices else "0"
            else:
                dims = array_dimensions(self.types[0].name)
                assert dims is not None and len(dims) == len(self.indices), (
                    f"ArrayWrite: {len(self.indices)}-index write requires type annotation "
                    f"with {len(self.indices)} dimensions, got {self.types}"
                )
                base = self.rvalue.name
                yield from _linearise_indices(self.indices, dims, base)
                idx = _lin_var(base, len(dims))

            for field_path, leaf_type in _flatten_container_fields(elem_type.name, ctx):
                raw_src = _container_field_var(self.rvalue.name, field_path)
                src = ctx.ssa_to_name.get(raw_src, raw_src)
                dest_arr = _container_field_var(arr_core, field_path)
                leaf_size = array_total_size(leaf_type.name)
                if leaf_size is None:
                    yield f"array.write {src} {dest_arr}[{idx}]"
                else:
                    start_var = f"{raw_src}_off"
                    yield f"{start_var} = felt.mul {idx} {leaf_size}"
                    yield from _emit_container_field_copy(src, dest_arr, start_var, leaf_size, raw_src)
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

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        # array.extract reads a lower-rank sub-array out of arr_ref: a
        # contiguous run of the flattened source array, copied into a freshly
        # allocated result array. The start/length derivation mirrors
        # ArrayInsert, but the copy itself runs the opposite way — this is
        # an "extract" (offset on the source, the bigger arr_ref; the fresh,
        # correctly-sized result is always written 0-based), not an
        # "insert" (offset on the destination) — see
        # _emit_container_field_copy's offset_src.
        type_str = self.arr_type.name
        dims = array_dimensions(type_str)
        assert dims is not None, \
            f"ArrayExtract: requires an array type annotation, got {self.arr_type}"

        n = len(dims)
        k = len(self.indices)
        assert 0 <= k < n, \
            f"ArrayExtract: {k} indices is not a valid partial index set for a {n}-D array"

        length = 1
        for d in dims[k:]:
            length *= d

        arr_core = ctx.ssa_to_name.get(self.arr_ref.name, self.arr_ref.to_core())
        base = self._result.name

        if k == 0:
            start = "0"
        else:
            yield from _linearise_indices(self.indices, dims, base)
            start = _lin_var(base, n)

        if "!pod.type" in type_str or "!struct.type" in type_str:
            for field_path, leaf_type in _flatten_container_fields(type_str, ctx):
                leaf_mult = array_total_size(leaf_type.name) or 1
                src_arr = _container_field_var(arr_core, field_path)
                dest_arr = _container_field_var(self._result.name, field_path)
                field_length = length * leaf_mult
                field_start = start
                if leaf_mult > 1:
                    field_start = f"{dest_arr}_start"
                    yield f"{field_start} = felt.mul {start} {leaf_mult}"
                yield f"array.new {field_length} {dest_arr}"
                yield from _emit_container_field_copy(src_arr, dest_arr, field_start, field_length, dest_arr,
                                                      offset_src=True)
            return

        yield f"array.new {length} {self._result.to_core()}"
        yield from _emit_container_field_copy(arr_core, self._result.to_core(), start, length, base,
                                              offset_src=True)

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

    def to_core(self, ctx: TranslationContext) -> Generator[str, None, None]:
        # array.insert writes a lower-rank sub-array into a partial slice of
        # arr_ref. Since arrays are flattened to 1-D, the slice is a
        # contiguous run: its first position ("start") and length are
        # determined by arr_ref's shape and the (partial) indices. The index
        # expression is kept symbolic (not resolved to a Python constant) so
        # this works even when it comes from a runtime-carried variable (e.g.
        # an scf.while loop variable), not just a compile-time-constant one.
        dims = array_dimensions(self.types[0].name) if self.types else None
        assert dims is not None, \
            f"ArrayInsert: requires an array type annotation, got {self.types}"

        n = len(dims)
        k = len(self.indices)
        assert 0 <= k < n, \
            f"ArrayInsert: {k} indices is not a valid partial index set for a {n}-D array"

        length = 1
        for d in dims[k:]:
            length *= d

        arr_core = ctx.ssa_to_name.get(self.arr_ref.name, self.arr_ref.to_core())
        base = self.rvalue.name

        if k == 0:
            start = "0"
        else:
            yield from _linearise_indices(self.indices, dims, base)
            start = _lin_var(base, n)

        elem_type = self.types[-1] if len(self.types) > 1 else None
        if elem_type is not None and ("!pod.type" in elem_type.name or "!struct.type" in elem_type.name):
            for field_path, leaf_type in _flatten_container_fields(elem_type.name, ctx):
                leaf_mult = array_total_size(leaf_type.name) or 1
                src_arr = _container_field_var(self.rvalue.name, field_path)
                dest_arr = _container_field_var(arr_core, field_path)
                field_base = _container_field_var(base, field_path)
                field_start = start
                field_length = length
                if leaf_mult > 1:
                    field_start = f"{field_base}_start"
                    yield f"{field_start} = felt.mul {start} {leaf_mult}"
                    field_length = length * leaf_mult
                yield from _emit_container_field_copy(src_arr, dest_arr, field_start, field_length, field_base)
            return

        yield from _emit_container_field_copy(self.rvalue.to_core(), arr_core, start, length, base)

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
