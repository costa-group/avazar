"""
Location (loc(...)) preprocessing for LLZK IR text.

The '--llzk_plaintext' output of circom-llzk embeds MLIR-style debug info:
almost every operation line (and every block-closing '}') can carry a
trailing ' loc(#locN)' suffix, or an inline literal such as
' loc("file.circom":1:16)' / ' loc(unknown)'. The file also ends with a
block of top-level alias definitions:

    #loc1 = loc("file.circom":1:16)
    #loc = loc("file.circom":14:18)

None of the dialect parsers in llzk_dialects/*.py know about 'loc', so this
module is responsible for:

  1. Pulling the '#locN = loc(...)' alias definitions out of the line stream
     into a LocTable (they are not operations and must not reach the
     dispatcher).
  2. Stripping the trailing ' loc(...)' suffix from every remaining line so
     the existing per-dialect regexes keep matching unchanged, while
     recording which (raw, possibly-aliased) location reference was attached
     to each line.

Callers (LLZKParser) use the returned line->reference map together with the
LocTable to resolve and attach the final location string to whatever
Operation/BlockOperation ends up being parsed from that line/range.
"""
import re
from typing import Dict, List, Optional, Set, Tuple


_LOC_DEF_RE = re.compile(r'#loc(?P<id>\d*)\s*=\s*loc\((?P<body>.*)\)')


def is_loc_def(line: str) -> Optional[Tuple[str, str]]:
    """
    If `line` is a top-level '#locN = loc(...)' alias definition, return
    (alias, raw_body) — e.g. ('#loc1', '"f.circom":1:16') — else None.
    """
    m = _LOC_DEF_RE.fullmatch(line)
    if m is None:
        return None
    return f"#loc{m.group('id')}", m.group('body')


def strip_trailing_loc(line: str) -> Tuple[str, Optional[str]]:
    """
    Split off a trailing ' loc(...)' suffix (parens balanced), if present.

    Returns (line_without_suffix, raw_body) or (line, None) when the line
    doesn't end in such a suffix. 'raw_body' is either a '#locN' alias or a
    literal location text (e.g. '"f.circom":1:16', 'unknown').
    """
    if not line.endswith(')'):
        return line, None

    depth = 0
    for i in range(len(line) - 1, -1, -1):
        c = line[i]
        if c == ')':
            depth += 1
        elif c == '(':
            depth -= 1
            if depth == 0:
                prefix = line[:i]
                if prefix.endswith('loc'):
                    before = prefix[:-3]
                    if before == '' or before[-1].isspace():
                        return before.rstrip(), line[i + 1:-1]
                break

    return line, None


class LocTable:
    """
    Dictionary of '#locN' alias -> raw location text, with recursive
    resolution (an alias may itself point to another alias).
    """

    def __init__(self):
        self.defs: Dict[str, str] = {}

    def add(self, alias: str, raw_body: str) -> None:
        self.defs[alias] = raw_body

    def resolve(self, ref: Optional[str], _seen: Optional[Set[str]] = None) -> Optional[str]:
        """
        Resolve a raw reference ('#locN' or a literal) to its final text.
        Anything that isn't a bare '#locN' token is returned unchanged.
        """
        if ref is None:
            return None
        if not re.fullmatch(r'#loc\d*', ref):
            return ref

        seen = _seen or set()
        if ref in seen:
            raise ValueError(f"Cyclic loc alias detected: {ref}")
        if ref not in self.defs:
            return ref
        return self.resolve(self.defs[ref], seen | {ref})

    def resolved(self) -> Dict[str, str]:
        """Dict mapping every known '#locN' alias to its fully-resolved location text."""
        return {alias: self.resolve(alias) for alias in self.defs}


def preprocess(raw_lines: List[str]) -> Tuple[List[str], Dict[int, str], LocTable]:
    """
    Strip location metadata out of an already-stripped, non-blank line list.

    Returns (clean_lines, line_locs, loc_table):
      - clean_lines: raw_lines with alias-definition lines dropped and any
        trailing ' loc(...)' suffix removed from the rest.
      - line_locs: maps an index into clean_lines to the raw (unresolved)
        location reference that was found on that line, if any.
      - loc_table: the alias -> raw location text dictionary.
    """
    loc_table = LocTable()
    clean_lines: List[str] = []
    line_locs: Dict[int, str] = {}

    for raw in raw_lines:
        loc_def = is_loc_def(raw)
        if loc_def is not None:
            alias, body = loc_def
            loc_table.add(alias, body)
            continue

        stripped, ref = strip_trailing_loc(raw)
        if ref is not None:
            line_locs[len(clean_lines)] = ref
        clean_lines.append(stripped)

    return clean_lines, line_locs, loc_table
