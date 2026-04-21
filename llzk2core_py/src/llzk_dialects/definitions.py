"""
Dialect base class. Each dialect holds a registry of Operation classes
and dispatches parse_line to the matching one.
"""
from typing import List, Type


class Dialect:
    """
    Base class for every LLZK dialect.
    Each subclass instantiation registers its operation classes via register().
    """

    def __init__(self, name: str):
        self.name = name
        self.registered_ops: List[Type] = []

    def register(self, op):
        """Register an Operation class with this dialect."""
        self.registered_ops.append(op)
        return op

    def parse_line(self, line: str):
        """
        Dispatch a single-line string to the matching flat Operation class.
        Raises ValueError if no registered op matches.
        """
        for op in self.registered_ops:
            if op.match(line):
                return op.parse(line)
        raise ValueError(f"No operation found in dialect '{self.name}' for: {line}")
