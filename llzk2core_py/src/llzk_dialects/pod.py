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


def _split_top_level_commas(s: str) -> List[str]:
    """Split s on commas that are not inside <>, [], or ()."""
    depth = 0
    parts: List[str] = []
    current: List[str] = []
    for ch in s:
        if ch in '<[(':
            depth += 1
            current.append(ch)
        elif ch in '>])':
            depth -= 1
            current.append(ch)
        elif ch == ',' and depth == 0:
            parts.append(''.join(current))
            current = []
        else:
            current.append(ch)
    if current:
        parts.append(''.join(current))
    return parts


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
        # Every variable inside the pod is initialized to
        # a new variable of the form "{pod_name}_{variable}"
        print(self.result_type)
        yield from (
            translate_assignment_core_with_ctx(
                SSAVar.parse(f"{self._result.name}_{record}"),
                initial_value,
                self.result_type.get(record, Type("!felt.type")),
                ctx,
            )
            for record, initial_value in self.init_records.items()
        )

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
        # TODO: implement core translation
        yield from ()

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
        # TODO: implement core translation
        yield from ()

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
