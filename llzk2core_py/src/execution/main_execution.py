from llzk_dialects.parser import LLZKParser
from llzk_dialects.felt import FeltDialect
from llzk_dialects.scf import SCFDialect

def init_llzk_parser(lines:str):
    p = LLZKParser(lines)

    p.add_dialect(FeltDialect()) 
    p.add_dialect(SCFDialect())
    
    return p 


def main(args):
    print("AVAZAR LLZK2CORE Language")

    p = init_llzk_parser()
    res = p.parse_module()
    
