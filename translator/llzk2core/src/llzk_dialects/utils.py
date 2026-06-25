"""
Module for reusable methods in different modules
"""
import re
from typing import List, Optional, Tuple


def split_top_level_commas(s: str) -> List[str]:
    """Split s on commas that are not nested inside <>, [], or ()."""
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


def array_felt_dimensions(type_: str) -> Optional[List[int]]:
    """
    Returns the list of integer dimensions for an N-D array of felt type.

    Handles the real MLIR format where outer dimensions are comma-separated
    and the final dimension precedes the element type with 'x':
        <d0,d1,...,dn x !felt.type<...>>   (n-D, commas between dims)
        <N x !felt.type<...>>              (1-D, single dim)

    Also accepts the all-x-separated form for compatibility:
        <d0 x d1 x ... x !felt.type<...>>

    Returns None if the type is not a recognised felt array.
    """
    # Primary format: comma-separated outer dims, last dim uses 'x' before element type
    m = re.search(r"<\s*((?:\d+\s*,\s*)*\d+)\s+x\s+!felt\.type<", type_)
    if m:
        return [int(d) for d in re.findall(r'\d+', m.group(1))]
    # Fallback: all dims x-separated (e.g. test fixtures)
    m = re.search(r"<\s*((?:\d+\s+x\s+)+)!felt\.type<", type_)
    if m:
        return [int(d) for d in re.findall(r'\d+', m.group(1))]
    return None


def array_felt_first_dimension(type_: str) -> Optional[int]:
    """
    Returns the total linearized size (product of all dimensions) for an
    N-D felt array type.  E.g. !array.type<2 x 3 x !felt.type<"bn128">> -> 6.
    """
    dims = array_felt_dimensions(type_)
    if dims is None:
        return None
    result = 1
    for d in dims:
        result *= d
    return result


def translate_assignment_core(lhs: str, rhs: str, is_ff: bool) -> str:
    """
    Translates an assignment between the lhs and rhs variables to core.
    Depending on whether the variables are ff or arr<2>, a different statement is issued.
    Bool "is_ff" marks the corresponding case
    """
    if lhs == rhs:
        return ""
    if is_ff:
        return f"{lhs} = {rhs}"
    else:
        return f"array.copy {rhs} {lhs}"


def indent_stream(source, indent: str = "  "):
    """
    Consumes lines from a generator and yields them properly indented,
    tracking brace depth as it goes. Useful for printing CORE programs nicely
    """
    level = 0
    for raw in source:

        # A single line may contain multiple braces, so split on them
        tokens = raw.replace("{", "{\n").replace("}", "\n}").splitlines()
        for token in tokens:
            line = token.strip()
            if not line:
                continue
            if line.startswith("}"):
                level -= 1
            yield indent * level + line + '\n'
            if line.endswith("{"):
                level += 1
