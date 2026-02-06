"""
Core functionalities in the parser
"""

from definitions import Dialect
from abc import ABC, abstractmethod


class SSAVar:
    """
    SSA variable. Includes the % in the name
    """

    def __init__(self, name: str, n_components: int = 1):
        self.name = name
        self.n_components = n_components

    @classmethod
    def parse(cls, ssa_var: str) -> 'SSAVar':
        assert ssa_var[0] == "%", f"Trying to parse a SSAVar with no preceding %: {value_name}"
        components = ssa_var.split(":")
        if len(components) == 1:
            return SSAVar(components[0])
        elif len(components) == 2:
            return SSAVar(components[0], int(components[1]))
        else:
            raise ValueError(f"SSA variable has more than one ':': {ssa_var}")

    def __repr__(self) -> str:
        return self.name if self.n_components == 1 else f"{self.name}:{self.n_components}"

class GlobalVariable:
    """
    Variable that is preceded by @ (included in the name).
    Serves for multiple purposes:
    function names, fields...
    """
    def __init__(self, name: str):
        self.name = name

    @classmethod
    def parse(cls, global_var: str) -> 'GlobalVariable':
        assert global_var[0] == "@", f"Global variable must start with @: {global_var}"
        return GlobalVariable(global_var)

    def __repr__(self):
        return self.name

class Type:
    # TODO: decide what we want to do with the types
    def __init__(self, type_: str):
        self.name = type_

    @classmethod
    def parse(cls, type_: str) -> 'Type':
        return Type(type_)

    def __repr__(self):
        return f"Type({self.name})"

class Operation(ABC):
    """
    Abstract class to represent any operation
    in a dialect
    """
    @abstractmethod
    def dialect(self) -> Dialect:
        pass

    @classmethod
    @abstractmethod
    def parse(cls, line: str) -> 'Operation':
        raise NotImplementedError
