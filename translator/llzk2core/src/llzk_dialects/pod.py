"""
Pod dialect — Plain-Old-Data struct operations.
Prefix: pod.

Pod structs are fixed-layout records with named fields of any LLZK type.
Unlike struct (circuit components), pod structs have no constraint semantics.

Types:
  PodType — !pod.type<[@name: !type, ...]>

Operations:
  PodNew   — pod.new   (create a new pod struct, optionally initialising records)
  PodRead  — pod.read  (read a named record from a pod struct)
  PodWrite — pod.write (write a value into a named record of a pod struct)
"""

import re
from typing import List, Dict, Optional

from llzk_dialects.core import Operation, SSAVar, GlobalVariable, Type, TranslationContext
from llzk_dialects.definitions import Dialect
from llzk_dialects.core_utils import translate_assignment_core_with_ctx
from llzk_dialects.utils import array_felt_first_dimension, array_total_size, split_top_level_commas

_split_top_level_commas = split_top_level_commas


def _parse_pod_fields(pod_type_str: str) -> Dict[str, Type]:
    """
    Parse the field list inside !pod.type<[@name: type, ...]> into a dict.
    Returns an empty dict for !pod.type<[]> or when no bracket is found.
    """
    m = re.search(r'\[(?P<fields>.*)\]', pod_type_str, re.DOTALL)
    if not m:
        return {}
    fields_str = m.group('fields').strip()
    if not fields_str:
        return {}
    result: Dict[str, Type] = {}
    for part in _split_top_level_commas(fields_str):
        part = part.strip()
        name, type_str = part.split(':', 1)
        result[name.strip()] = Type.parse(type_str.strip())
    return result


def _register_nested_pod_vars(ctx: TranslationContext, var_name: str, type_str: str) -> None:
    """
    Register ctx.ssa2pod_var[var_name] for a pod-typed variable, then recurse
    into any field that is itself pod-typed (pod nested inside another pod).

    Callers (PodNew, ArrayRead) already register the *first* level of a pod's
    fields, using either an SSA-derived "<base>_<field>" name or, when the pod
    backs a struct member, a semantic "<member>.<field>" name (see
    _semantic_field_var). Without this recursive step, a nested pod field's
    own var name is only ever used to name ITS leaves (via
    _flatten_container_fields) -- it never becomes a key of ctx.ssa2pod_var
    itself, so a later pod.read/pod.write chained through that intermediate
    pod (e.g. `pod.read (pod.read %p[@a])[@b]`) finds nothing and either
    KeyErrors or silently falls through to an unregistered plain copy.
    """
    if "!pod.type" not in type_str:
        return
    fields = _parse_pod_fields(type_str)
    is_semantic = not var_name.startswith("%")

    def child_name(field: str) -> str:
        return f"{var_name}_{field[1:]}" if is_semantic else f"{var_name}_{field}"

    ctx.ssa2pod_var[var_name] = {
        field: (child_name(field), field_type)
        for field, field_type in fields.items()
    }
    for field, field_type in fields.items():
        if "!pod.type" in field_type.name:
            _register_nested_pod_vars(ctx, child_name(field), field_type.name)


class PodNew(Operation):
    """
    Create a new pod struct, optionally initialising named records.

    Syntax: %result = pod.new {(@rec = $val),*}? : !pod.type<...>
    Example (empty):        %p = pod.new : !pod.type<[@x: !felt.type]>
    Example (initialised):  %p = pod.new {@x = %v0} : !pod.type<[@x: !felt.type]>
    Operands: initialValues (variadic LLZK type)
    Attributes: initializedRecords (list of record names matched to values)
    Result: PodType
    """

    _OPS = {"pod.new"}

    def __init__(self, result: SSAVar, init_records: Dict[str, SSAVar],
                 result_type: Dict[str, Type]):
        self._result = result
        # Maps record name (with @) to its initial SSA value
        self.init_records = init_records
        # Maps field name (with @) to its Type
        self.result_type = result_type

    def dialect(self) -> Dialect:
        return Dialect("pod")

    @staticmethod
    def match(line: str) -> bool:
        # Split on the first '=' only — init records contain further '=' signs.
        return line.split('=', 1)[-1].strip().split()[0] in PodNew._OPS

    @classmethod
    def parse(cls, line: str) -> 'PodNew':
        # %r = pod.new : !type
        # %r = pod.new {@x = %v0, @y = %v1} : !type
        pattern = re.compile(
            r"\s*(?P<res>\S+)\s*=\s*pod\.new"
            r"(?:\s*\{(?P<inits>[^}]*)\})?"
            r"\s*:\s*(?P<type>\S.*\S|\S)\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse PodNew: {line}")
        init_records: Dict[str, SSAVar] = {}
        if m["inits"]:
            for item in m["inits"].split(","):
                item = item.strip()
                if not item:
                    continue
                k, v = item.split("=", 1)
                init_records[k.strip()] = SSAVar.parse(v.strip())
        return PodNew(SSAVar.parse(m["res"]), init_records,
                      _parse_pod_fields(m["type"]))

    @property
    def result(self):
        return self._result

    @property
    def operands(self) -> List[SSAVar]:
        return list(self.init_records.values())

    def to_core(self, ctx: TranslationContext) -> str:
        # Build the field-variable mapping. When this pod is an inputs pod for a
        # struct member, use semantic names (e.g. "last1.in1_last") instead of
        # the default SSA-derived names (e.g. "%pod_5_@in1_last").
        member = ctx.input_pod_to_member.get(self._result.name)
        if member:
            ctx.ssa2pod_var[self._result.name] = {
                record: (f"{member}.{record[1:]}", type_)
                for record, type_ in self.result_type.items()
            }
        else:
            ctx.ssa2pod_var[self._result.name] = {
                record: (f"{self._result.name}_{record}", type_)
                for record, type_ in self.result_type.items()
            }

        # Emit assignments for records that have an initial value
        for record, initial_value in self.init_records.items():
            var_name, var_type = ctx.ssa2pod_var[self._result.name][record]
            result = translate_assignment_core_with_ctx(
                SSAVar(var_name),
                initial_value,
                var_type,
                ctx,
            )
            if result:
                yield result

        # Allocate real storage for fields not given an initial value above.
        # A plain felt/index array gets a direct array.new. A struct/pod-typed
        # field recurses into its own leaves (structure-of-arrays) so that a
        # later copy into/out of it (e.g. via array.write on an array of this
        # pod type) reads from real, defined storage rather than an undefined
        # variable — even though the field's actual value may still be unset
        # until a later pod.write (e.g. a struct field only computed once a
        # counter reaches zero).
        for record, type_ in self.result_type.items():
            if record in self.init_records:
                continue
            var_name, _ = ctx.ssa2pod_var[self._result.name][record]
            first_dim = array_felt_first_dimension(type_.name)
            if first_dim is not None:
                yield f"array.new {first_dim} {var_name}"
            elif "!struct.type" in type_.name or "!pod.type" in type_.name:
                from llzk_dialects.array import _flatten_container_fields, _container_field_var
                from llzk_dialects.utils import is_array_type

                assert not is_array_type(type_.name), (
                    f"PodNew: a pod field that is itself an array of struct/pod "
                    f"({record}: {type_}) is not yet supported"
                )
                if "!pod.type" in type_.name:
                    _register_nested_pod_vars(ctx, var_name, type_.name)
                for field_path, leaf_type in _flatten_container_fields(type_.name, ctx):
                    leaf_size = array_total_size(leaf_type.name)
                    field_var = _container_field_var(var_name, field_path)
                    if leaf_size is None:
                        # Scalar leaf (e.g. a struct's felt-typed output
                        # member): no array to allocate, just a placeholder
                        # value so a later read/copy from it (before the
                        # field is actually computed) reads a defined
                        # variable instead of an undefined one.
                        yield f"{field_var} = 0"
                    else:
                        yield f"array.new {leaf_size} {field_var}"

    def __repr__(self):
        inits = ', '.join(f"{k} = {v}" for k, v in self.init_records.items())
        init_str = f" {{{inits}}}" if inits else ""
        fields = ', '.join(f"{k}: {v}" for k, v in self.result_type.items())
        return f"PodNew({self._result} = pod.new{init_str} : <[{fields}]>)"


class PodRead(Operation):
    """
    Read the value of a named record from a pod struct.

    Syntax: %result = pod.read $pod_ref [@record_name] : type($pod_ref), type($result)
    Attributes: record_name (FlatSymbolRefAttr — the @-prefixed record name)
    Operand:    pod_ref (PodType)
    Result:     valid LLZK type
    """

    _OPS = {"pod.read"}

    def __init__(self, result: SSAVar, pod_ref: SSAVar,
                 record_name: GlobalVariable,
                 pod_type: Dict[str, Type],
                 result_type: Optional[Type]):
        self._result = result
        self.pod_ref = pod_ref
        self.record_name = record_name
        # Maps field name (with @) to its Type; empty dict when no annotation
        self.pod_type = pod_type
        # Type of the read result; None when no annotation
        self.result_type = result_type

    def dialect(self) -> Dialect:
        return Dialect("pod")

    @staticmethod
    def match(line: str) -> bool:
        return line.split('=')[-1].strip().split()[0] in PodRead._OPS

    @classmethod
    def parse(cls, line: str) -> 'PodRead':
        pattern = re.compile(
            r"\s*(?P<res>\S+)\s*=\s*pod\.read\s+(?P<ref>\S+)"
            r"\s*\[\s*(?P<rec>@\S+)\s*\]"
            r"(?:\s*:\s*(?P<types>.+))?\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse PodRead: {line}")
        pod_type: Dict[str, Type] = {}
        result_type: Optional[Type] = None
        if m["types"]:
            parts = _split_top_level_commas(m["types"])
            pod_type = _parse_pod_fields(parts[0].strip())
            result_type = Type.parse(parts[1].strip()) if len(parts) > 1 else None
        return PodRead(SSAVar.parse(m["res"]), SSAVar.parse(m["ref"]),
                       GlobalVariable.parse(m["rec"]), pod_type, result_type)

    @property
    def result(self):
        return self._result

    @property
    def operands(self) -> List[SSAVar]:
        return [self.pod_ref]

    def to_core(self, ctx: TranslationContext) -> str:
        variable_name, var_type = ctx.ssa2pod_var[self.pod_ref.name][self.record_name.name]

        assert self.result_type is None or self.result_type == var_type, "Pod.read must match the type inside the dict ssa2pod_var"

        # When the pod field has a semantic name (no % prefix), record an alias so
        # that downstream operations (e.g. function.call args) use it directly.
        if not variable_name.startswith("%"):
            ctx.ssa_to_name[self._result.name] = variable_name
            # For array-typed fields, ArrayWrite will look up the alias and write
            # directly into the named array; no copy into a temp variable is needed.
            if array_felt_first_dimension(var_type.name) is not None:
                return

        result = translate_assignment_core_with_ctx(
            self._result,
            SSAVar(variable_name),
            var_type,
            ctx
        )
        if result:
            yield result

    def __repr__(self):
        fields = ', '.join(f"{k}: {v}" for k, v in self.pod_type.items())
        type_str = f" : <[{fields}]>" if self.pod_type else ""
        if self.result_type is not None:
            type_str += f", {self.result_type}"
        return (f"PodRead({self._result} = pod.read "
                f"{self.pod_ref}[{self.record_name}]{type_str})")


class PodWrite(Operation):
    """
    Write a value into a named record of a pod struct.

    Syntax: pod.write $pod_ref [@record_name] = $value : type($pod_ref), type($value)
    Attributes: record_name (FlatSymbolRefAttr)
    Operands:   pod_ref (PodType), value (valid LLZK type)
    No result.
    """

    _OPS = {"pod.write"}

    def __init__(self, pod_ref: SSAVar, record_name: GlobalVariable,
                 value: SSAVar,
                 pod_type: Dict[str, Type],
                 value_type: Optional[Type]):
        self.pod_ref = pod_ref
        self.record_name = record_name
        self.value = value
        # Maps field name (with @) to its Type; empty dict when no annotation
        self.pod_type = pod_type
        # Type of the written value; None when no annotation
        self.value_type = value_type

    def dialect(self) -> Dialect:
        return Dialect("pod")

    @staticmethod
    def match(line: str) -> bool:
        return line.strip().split()[0] in PodWrite._OPS

    @classmethod
    def parse(cls, line: str) -> 'PodWrite':
        pattern = re.compile(
            r"\s*pod\.write\s+(?P<ref>\S+)"
            r"\s*\[\s*(?P<rec>@\S+)\s*\]"
            r"\s*=\s*(?P<val>\S+)"
            r"(?:\s*:\s*(?P<types>.+))?\s*"
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse PodWrite: {line}")
        pod_type: Dict[str, Type] = {}
        value_type: Optional[Type] = None
        if m["types"]:
            parts = _split_top_level_commas(m["types"])
            pod_type = _parse_pod_fields(parts[0].strip())
            value_type = Type.parse(parts[1].strip()) if len(parts) > 1 else None
        return PodWrite(SSAVar.parse(m["ref"]), GlobalVariable.parse(m["rec"]),
                        SSAVar.parse(m["val"]), pod_type, value_type)

    @property
    def operands(self) -> List[SSAVar]:
        return [self.pod_ref, self.value]

    def to_core(self, ctx: TranslationContext) -> str:
        variable_name, var_type = ctx.ssa2pod_var[self.pod_ref.name][self.record_name.name]

        assert self.value_type is None or self.value_type == var_type, "Pod.write must match the type inside the dict ssa2pod_var"

        result = translate_assignment_core_with_ctx(
            SSAVar(variable_name),
            self.value,
            var_type,
            ctx
        )
        if result:
            yield result

    def __repr__(self):
        fields = ', '.join(f"{k}: {v}" for k, v in self.pod_type.items())
        type_str = f" : <[{fields}]>" if self.pod_type else ""
        if self.value_type is not None:
            type_str += f", {self.value_type}"
        return (f"PodWrite(pod.write {self.pod_ref}"
                f"[{self.record_name}] = {self.value}{type_str})")


class PodDialect(Dialect):
    """Registry for all pod dialect operations."""

    def __init__(self):
        super().__init__("pod")
        self.register(PodNew)
        self.register(PodRead)
        self.register(PodWrite)
