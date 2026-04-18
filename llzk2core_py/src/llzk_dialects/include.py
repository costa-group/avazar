"""
Include dialect — file inclusion at module level.
Prefix: include.

Operations:
  IncludeFrom — include.from (import a file and bind it to a symbol name)
"""

import re

from llzk_dialects.core import Operation, GlobalVariable, TranslationContext
from llzk_dialects.definitions import Dialect


class IncludeFrom(Operation):
    """
    Include an external file and bind its contents to a symbol name.

    Syntax: include.from $path as $sym_name
    Attributes:
      path     (StringAttr) — file path as a quoted string
      sym_name (StringAttr) — local name bound to the included module
    Valid parent: ModuleOp
    Interfaces: Symbol
    """

    _OPS = {"include.from"}

    def __init__(self, path: str, sym_name: GlobalVariable):
        # path is the raw quoted string, e.g. '"lib/math.llzk"'
        self.path = path
        self.sym_name = sym_name

    def dialect(self) -> Dialect:
        return Dialect("include")

    @staticmethod
    def match(line: str) -> bool:
        return line.strip().split()[0] in IncludeFrom._OPS

    @classmethod
    def parse(cls, line: str) -> 'IncludeFrom':
        # include.from "path/to/file" as @SymName
        pattern = re.compile(
            r'\s*include\.from\s+(?P<path>"[^"]*")\s+as\s+(?P<sym>\S+)\s*'
        )
        m = re.fullmatch(pattern, line)
        if not m:
            raise ValueError(f"Failed to parse IncludeFrom: {line}")
        return IncludeFrom(m["path"], GlobalVariable.parse(m["sym"]))

    def to_core(self, ctx: TranslationContext) -> str:
        # TODO: implement core translation
        raise NotImplementedError

    def __repr__(self):
        return f"IncludeFrom(include.from {self.path} as {self.sym_name})"


class IncludeDialect(Dialect):
    """Registry for all include dialect operations."""

    def __init__(self):
        super().__init__("include")
        self.register(IncludeFrom)
