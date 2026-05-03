"""
LLZKParser — top-level parser for LLZK IR text.

Dispatch strategy
-----------------
1. Extract the dialect prefix from the operation token (the identifier before
   the first '.' that starts with a letter).
2. Look up the registered Dialect by prefix.
3. Iterate its registered_ops calling op_cls.match(line) to find the owner.
4. Dispatch to BlockOperation.parse(lines, cursor, parse_body) or the flat
   Operation.parse(line) depending on the matched class.
"""

from typing import Dict, List, Optional

from llzk_dialects.core import Operation, BlockOperation
from llzk_dialects.definitions import Dialect
from llzk_dialects.llzk import ModuleOp


class LLZKParser:
    """
    Parser for LLZK IR source text.

    Usage::

        parser = LLZKParser(source_lines)
        parser.add_dialects([FeltDialect(), StructDialect(), SCFDialect(), ...])
        ops = parser.parse()
    """

    def __init__(self, lines: List[str]):
        # Strip whitespace and drop blank lines so cursor arithmetic is simple.
        # Block operations receive self.lines directly and rely on this invariant.
        self.lines: List[str] = [l.strip() for l in lines if l.strip()]
        self.dialects: Dict[str, Dialect] = {}

    # ── Dialect registration ──────────────────────────────────────────────────

    def add_dialect(self, dialect: Dialect) -> None:
        """Register a dialect; its name becomes the routing key."""
        self.dialects[dialect.name] = dialect

    def add_dialects(self, dialects) -> None:
        for d in dialects:
            self.add_dialect(d)

    # ── Prefix extraction ─────────────────────────────────────────────────────

    def _dialect_prefix(self, line: str) -> Optional[str]:
        """
        Extract the dialect prefix from an operation line.

        Scans tokens for the first one that starts with a letter and contains
        '.', which identifies the operation token (e.g. 'felt.add').
        Returns the substring before the first '.', or None if none found.

        Handles all assignment forms:
          '%r = felt.add …'            — result assignment before op
          '%r0, %r1 = function.call …' — multi-result assignment
          'struct.writem %s [@m] = %v' — '=' inside operands, not an assignment
        """
        for token in line.split():
            if '.' in token and token[0].isalpha():
                return token[:token.index('.')]
        return None

    def _find_op_class(self, line: str) -> Optional[type]:
        """
        Return the first registered Operation class whose match() accepts line,
        or None if no registered op recognises it.
        """
        prefix = self._dialect_prefix(line)
        if prefix is None or prefix not in self.dialects:
            return None
        for op_cls in self.dialects[prefix].registered_ops:
            if op_cls.match(line):
                return op_cls
        return None

    # ── Core parsing ──────────────────────────────────────────────────────────

    def parse_body(self, start: int, end: int) -> List[Operation]:
        """
        Parse self.lines[start:end] into a list of Operation objects.

        Passed as the parse_fn callback to every BlockOperation.parse() call so
        block ops can recursively parse their bodies without coupling to this
        class directly.

        Structural markers (closing braces, else/do transitions, block labels)
        and lines that belong to no registered dialect are silently skipped.
        """
        ops: List[Operation] = []
        cursor = start
        while cursor < end:
            line = self.lines[cursor]

            if line in ('}', '} else {', 'do {', '} do {') or line.startswith('^bb'):
                cursor += 1
                continue

            op_cls = self._find_op_class(line)
            if op_cls is None:
                raise ValueError(f"{line}: no operation matches the statement")

            if issubclass(op_cls, BlockOperation):
                # Block ops consume multiple lines and return the next cursor.
                op, cursor = op_cls.parse(self.lines, cursor, self.parse_body)
                ops.append(op)
            else:
                ops.append(op_cls.parse(line))
                cursor += 1

        return ops

    def parse(self) -> List[Operation]:
        """
        Parse the full input and return the top-level list of Operations.

        If the input is wrapped in a 'module { … }' header the body inside the
        outermost braces is extracted first; otherwise the whole input is parsed.
        """
        if not self.lines:
            return []

        if self.lines[0].startswith('module'):
            body_start = self._find_opening_brace(0)
            body_end = self._find_closing_brace(body_start)
            if body_start == -1 or body_end == -1:
                return self.parse_body(0, len(self.lines))
            lang, main_type = ModuleOp.parse_header(self.lines[0])
            body = self.parse_body(body_start + 1, body_end)
            return [ModuleOp(lang, main_type, body)]

        return self.parse_body(0, len(self.lines))

    # ── Brace helpers (used only for the module wrapper) ─────────────────────

    def _find_opening_brace(self, cursor: int) -> int:
        """Return the index of the first line at or after cursor that contains
        '{', or -1 if none found."""
        for i in range(cursor, len(self.lines)):
            if '{' in self.lines[i]:
                return i
        return -1

    def _find_closing_brace(self, start: int) -> int:
        """Return the index of the line that closes the brace block opened at
        start (depth-tracked from that line), or -1 if never closed."""
        depth = 0
        for i in range(start, len(self.lines)):
            depth += self.lines[i].count('{')
            depth -= self.lines[i].count('}')
            if depth == 0:
                return i
        return -1
