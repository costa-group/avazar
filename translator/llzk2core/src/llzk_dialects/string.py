"""
String dialect — string literal type and operations.
Prefix: string.

Operations:
  StringNew — string.new (creates a string literal constant)

Types:
  StringType — !string.type (no parameters)
"""

import re
from typing import List

from llzk_dialects.core import Operation, SSAVar, TranslationContext
from llzk_dialects.definitions import Dialect


class StringNew(Operation):
    """
    Create a string literal constant.

    Syntax: %result = string.new $value
    Attribute: value (StringAttr — a quoted string literal)
    Result: !string.type
    Traits: ConstantLike
    """

    _OPS = {"string.new"}

    def __init__(self, result: SSAVar, value: str):
        self._result = result
        # value stores the raw quoted string, e.g. '"hello"'
        self.value = value

    def dialect(self) -> Dialect:
        return Dialect("string")

    @staticmethod
    def match(line: str) -> bool:
        return line.split('=')[-1].strip().split()[0] in StringNew._OPS

    @classmethod
    def parse(cls, line: str) -> 'StringNew':
        pattern = re.compile(
            r'\s*(?P<res>\S+)\s*=\s*string\.new\s+(?P<val>"[^"]*")\s*'
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse StringNew: {line}")
        return StringNew(SSAVar.parse(m["res"]), m["val"])

    @property
    def result(self):
        return self._result

    @property
    def operands(self) -> List[SSAVar]:
        return []

    def to_core(self, ctx: TranslationContext) -> str:
        # TODO: implement core translation
        raise NotImplementedError

    def __repr__(self):
        return f"StringNew({self._result} = string.new({self.value}))"


class StringDialect(Dialect):
    """Registry for all string dialect operations."""

    def __init__(self):
        super().__init__("string")
        self.register(StringNew)
