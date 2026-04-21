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
from typing import List, Dict

from llzk_dialects.core import Operation, SSAVar, GlobalVariable, Type, TranslationContext
from llzk_dialects.definitions import Dialect


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
                 result_type: Type):
        self.result = result
        # Maps record name (without @) to its initial SSA value
        self.init_records = init_records
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
        return PodNew(SSAVar.parse(m["res"]), init_records, Type.parse(m["type"]))

    def to_core(self, ctx: TranslationContext) -> str:
        # TODO: implement core translation
        raise NotImplementedError

    def __repr__(self):
        inits = ', '.join(f"{k} = {v}" for k, v in self.init_records.items())
        init_str = f" {{{inits}}}" if inits else ""
        return f"PodNew({self.result} = pod.new{init_str} : {self.result_type})"


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
                 record_name: GlobalVariable, types: List[Type]):
        self.result = result
        self.pod_ref = pod_ref
        self.record_name = record_name
        self.types = types

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
        types = (
            [Type.parse(t.strip()) for t in m["types"].split(",")]
            if m["types"] else []
        )
        return PodRead(SSAVar.parse(m["res"]), SSAVar.parse(m["ref"]),
                       GlobalVariable.parse(m["rec"]), types)

    def to_core(self, ctx: TranslationContext) -> str:
        # TODO: implement core translation
        raise NotImplementedError

    def __repr__(self):
        type_str = '' if not self.types else ' : ' + ', '.join(repr(t) for t in self.types)
        return (f"PodRead({self.result} = pod.read "
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
                 value: SSAVar, types: List[Type]):
        self.pod_ref = pod_ref
        self.record_name = record_name
        self.value = value
        self.types = types

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
        types = (
            [Type.parse(t.strip()) for t in m["types"].split(",")]
            if m["types"] else []
        )
        return PodWrite(SSAVar.parse(m["ref"]), GlobalVariable.parse(m["rec"]),
                        SSAVar.parse(m["val"]), types)

    def to_core(self, ctx: TranslationContext) -> str:
        # TODO: implement core translation
        raise NotImplementedError

    def __repr__(self):
        type_str = '' if not self.types else ' : ' + ', '.join(repr(t) for t in self.types)
        return (f"PodWrite(pod.write {self.pod_ref}"
                f"[{self.record_name}] = {self.value}{type_str})")


class PodDialect(Dialect):
    """Registry for all pod dialect operations."""

    def __init__(self):
        super().__init__("pod")
        self.register(PodNew)
        self.register(PodRead)
        self.register(PodWrite)
