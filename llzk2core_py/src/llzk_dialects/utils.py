"""
Module for reusable methods in different modules
"""
import re
from typing import List, Tuple, Optional


def invocation_args(args: List[Tuple[str, str]]) -> str:
    """
    Given a list of args and their types, returns a string for invoking
    a function in CORE, with the format: "arg1, arg2, ..."
    """
    return ', '.join(arg for arg, _ in args)


def signature_args(args: List[Tuple[str, str]]) -> str:
    """
    Given a list of args and their types, returns a string for declaring
    the signature of a function in CORE, with the format: "arg1: type1, arg2: type2, ..."
    """
    return', '.join(f"{arg}: {type_}" for arg, type_ in args)


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
