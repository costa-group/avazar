import argparse
from typing import List
from llzk_dialects.parser import LLZKParser
from llzk_dialects.felt import FeltDialect
from llzk_dialects.scf import SCFDialect
from llzk_dialects.function import FunctionDialect
from llzk_dialects.llzk import LLZKDialect


def init_llzk_parser(llzk_plain_str: List[str]):
    p = LLZKParser(llzk_plain_str)

    # Adding all required dialects
    p.add_dialects([FeltDialect, SCFDialect, FunctionDialect, LLZKDialect])

    return p 


def main(args: argparse.Namespace):
    with open(args.source, 'r') as f:
        llzk_contents = f.readlines()

    p = init_llzk_parser(llzk_contents)
    res = p.parse_module()
