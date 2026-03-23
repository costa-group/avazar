from enum import Enum
from typing import List


class Dialect(Enum, ABC):
    array_d = 1
    bool_d = 2
    cast_d = 3
    constraint_d = 4
    felt_d = 5
    function_d = 6
    global_d = 7
    include_d = 8
    llzk_d = 9
    poly_d = 10
    string_d = 11
    struct_d = 12

    def __init__(self, name: str):
        self.name = name
        self.registered_ops: List[Type[Operation]] = []

    def get_name(self):
        return self.name
        
    def register(self, op: Operation):
        self.registered_ops.append(op)
        return op

    def parse_line(self, line: str) -> Operation:
        for op in self.registered_ops:
            if op.match(line):
                return op.parse(line)
        raise ValueError(f"No operation found in dialect '{self.name}' for: {line}")

    
    
# FELT_CONST = ["felt.const"]

# FELT_UNARY = ["felt.bit_not", "felt.const",
#               "felt.inv", "felt.neg", ]

# FELT_BINARY = ["felt.add", "felt.bit_and",
#                "felt.bit_or", "felt.bit_xor",
#                "felt.div", "felt.mul", "felt.pow",
#                "felt.shl", "felt.shr", "felt.sintdiv",
#                "felt.smod", "felt.sub",
#                "felt.uintdiv", "felt.umod"]

# FELT_OPS = [*FELT_CONST, *FELT_UNARY, *FELT_BINARY]
