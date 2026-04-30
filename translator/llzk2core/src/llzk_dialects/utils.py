"""
Module for reusable methods in different modules
"""
import re
from typing import List, Tuple, Optional


def array_felt_first_dimension(type_: str) -> Optional[int]:
    """
    Method that recognizes 2D array expressions of felt and
    returns the x dimension.
    """
    pattern = r"!array\.type<(\d+)\s+x\s+!felt\.type<"
    match = re.search(pattern, type_)
    if match:
        return int(match.group(1))
    return None


def translate_assignment_core(lhs: str, rhs: str, is_ff: bool) -> str:
    """
    Translates an assignment between the lhs and rhs variables to core.
    Depending on whether the variables are ff or arr<2>, a different statement is issued.
    Bool "is_ff" marks the corresponding case
    """
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
