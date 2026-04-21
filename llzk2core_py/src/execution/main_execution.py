import argparse
from typing import List
from llzk_dialects.parser import LLZKParser
from llzk_dialects.arith import ArithDialect
from llzk_dialects.array import ArrayDialect
from llzk_dialects.bool import BoolDialect
from llzk_dialects.cast import CastDialect
from llzk_dialects.constrain import ConstrainDialect
from llzk_dialects.felt import FeltDialect
from llzk_dialects.function import FunctionDialect
from llzk_dialects.global_ import GlobalDialect
from llzk_dialects.include import IncludeDialect
from llzk_dialects.llzk import LLZKDialect
from llzk_dialects.pod import PodDialect
from llzk_dialects.poly import PolyDialect
from llzk_dialects.scf import SCFDialect
from llzk_dialects.string import StringDialect
from llzk_dialects.struct import StructDialect
from llzk_dialects.core import TranslationContext
from llzk_dialects.utils import indent_stream


def init_llzk_parser(llzk_plain_str: List[str]):
    p = LLZKParser(llzk_plain_str)

    p.add_dialects([
        ArithDialect(),
        ArrayDialect(),
        BoolDialect(),
        CastDialect(),
        ConstrainDialect(),
        FeltDialect(),
        FunctionDialect(),
        GlobalDialect(),
        IncludeDialect(),
        LLZKDialect(),
        PodDialect(),
        PolyDialect(),
        SCFDialect(),
        StringDialect(),
        StructDialect(),
    ])

    return p


def main(args: argparse.Namespace):
    with open(args.source, 'r') as f:
        llzk_contents = f.readlines()

    p = init_llzk_parser(llzk_contents)
    res = p.parse()

    # For now, we assume only one top
    # module element must be parsed
    assert len(res) == 1, "Multiple modules have been recognized inside the program"

    module_structure = res[0]
    core_generator = module_structure.to_core(TranslationContext())
    with open(args.target, 'w') as f:
        # Indent stream generates the statements in a nice format
        for line in indent_stream(core_generator):
            f.write(line)
