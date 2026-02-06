from enum import Enum

class Dialect(Enum):
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

FELT_UNARY = ["felt.bit_not", "felt.const",
              "felt.inv", "felt.neg", ]
FELT_BINARY = ["felt.add", "felt.bit_and",
               "felt.bit_or", "felt.bit_xor",
               "felt.div", "felt.mul", "felt.pow",
               "felt.shl", "felt.shr", "felt.sintdiv",
               "felt.smod", "felt.sub",
               "felt.uintdiv", "felt.umod"]

FELT_OPS = [*FELT_BINARY]