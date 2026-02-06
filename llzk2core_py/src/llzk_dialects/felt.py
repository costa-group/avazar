"""
Module that contains the parser for the dialect 'felt'
(finite elements)
"""
import re
from typing import List
from src.llzk_dialects.core import Operation, SSAVar, Type
from src.llzk_dialects.definitions import Dialect, FELT_UNARY, FELT_BINARY

class FeltUnary(Operation):
    """
    Unary operations (except for 'felt.const').

    Syntax: operation ::= `op` $operand
              `` custom<InferredOrParsedType>(type($operand), "true")
              attr-dict
    """

    def __init__(self, variable: SSAVar, op: str,
                 operand: SSAVar, types: List[Type]):
        self.result = variable
        self.op = op
        self.operand = operand
        self.types = types

    def dialect(self) -> Dialect:
        return Dialect.felt_d

    @classmethod
    def parse(cls, line: str) -> 'FeltUnary':
        pattern = re.compile(r"\s*(?P<res>\S+)\s*=\s*(?P<op>\S+)\s*(?P<operand>\S+)\s*(?:\s*:\s*(?P<types>\S.*\S))?\s*")
        match = re.fullmatch(pattern, line)
        if not match:
            raise ValueError(f"Failed to parse FeltUnary: {line}")
        else:
            if match["types"] is not None:
                print("Types", match["types"])
                types = [Type.parse(type_.strip()) for type_ in match["types"].split(",")]
            else:
                types = []
            assert match["op"] in FELT_UNARY, f"Unary operation in Felt has not been recognized: {match['op']}. Expression: {line}"
            return FeltUnary(SSAVar.parse(match["res"]), match["op"],
                             SSAVar.parse(match["operand"]), types)

    def __repr__(self):
        optional_type = '' if len(self.types) == 0 else f' : {", ".join([repr(type_) for type_ in self.types])}'
        return f"FeltUnary({self.result} = {self.op}({self.operand}){optional_type}"



class FeltBinary(Operation):
    """
    Binary operations.

    Syntax: operation ::= `op` $lhs `,` $rhs
              `` custom<InferredOrParsedType>(type($lhs), "true")
              `` custom<InferredOrParsedType>(type($rhs), "false")
              attr-dict
    """

    def __init__(self, variable: SSAVar, op: str, lhs: SSAVar,
                 rhs: SSAVar, types: List[Type]):
        self.result = variable
        self.op = op
        self.lhs = lhs
        self.rhs = rhs
        self.types = types

    def dialect(self) -> Dialect:
        return Dialect.felt_d

    @classmethod
    def parse(cls, line: str) -> 'FeltBinary':
        pattern = re.compile(r"\s*(?P<res>\S+)\s*=\s*(?P<op>\S+)\s*(?P<op1>\S+)\s*,\s*(?P<op2>\S+)(?:\s*:\s*(?P<types>\S.*\S))?\s*")
        match = re.fullmatch(pattern, line)
        if not match:
            raise ValueError(f"Failed to parse FeltBinary: {line}")
        else:
            if match["types"] is not None:
                print("Types", match["types"])
                types = [Type.parse(type_.strip()) for type_ in match["types"].split(",")]
            else:
                types = []
            assert match["op"] in FELT_BINARY, f"Binary operation in Felt has not been recognized: {match['op']}. Expression: {line}"
            return FeltBinary(SSAVar.parse(match["res"]), match["op"], SSAVar.parse(match["op1"]),
                              SSAVar.parse(match["op2"]), types)

    def __repr__(self):
        optional_type = '' if len(self.types) == 0 else f' : {", ".join([repr(type_) for type_ in self.types])}'
        return f"FeltBinary({self.result} = {self.op}({self.lhs}, {self.rhs})){optional_type}"



if __name__ == "__main__":
    binary_op_simplified = FeltBinary.parse("   %0 = felt.mul %arg0, %arg1 ")
    print(binary_op_simplified)

    binary_op_complete = FeltBinary.parse("       %0 = felt.mul %arg0, %arg1 : !felt.type, !felt.type ")
    print(binary_op_complete)

    # wrong_operation = FeltBinary.parse("       %0 = felt.op %arg0, %arg1 : !felt.type, !felt.type ")
    # print(binary_op_complete)
