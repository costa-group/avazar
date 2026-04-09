import re
from typing import List, Dict
from src.llzk_dialects.core import Operation, SSAVar, Type
from src.llzk_dialects.definitions import Dialect

class StructNew(Operation):
     """
    Struct creation.

    Syntax: operation ::= `struct.new` `:` type($result) attr-dict
    E.g.: %self = struct.new : !struct.type<@Reg>
    """

     STRUCT_NEW = ["struct.new"]

     def __init__(self, var: SSAVar, t:str, attr: Dict[str,str]):
         self.result = var
         self.type_struct = t
         self.attr = attr
                 
    def dialect(self) -> Dialect:
        return Dialect.struct_d

    def match(line: str) -> bool:
        op_name = line.split('=')[-1].strip().split()[0]
        return op_name in STRUCT_NEW
    
    @classmethod
    def parse(cls, line: str) -> 'StructNew':
        pattern = re.compile(r"\s*(?P<res>\S+)\s*=\s*struct\.new\s*:\s*(?P<type>\S+)\s*(?P<attrs>\{.*?\})?"
        match = re.fullmatch(pattern, line)
        if not match:
            raise ValueError(f"Failed to parse StructNew: {line}")
        else:
            if match["type"] is not None:
                print("Type", match["type"])
                type_rex = [Type.parse(t.strip()) for t in match["type"].split(",")]
            else:
                type_rex = ""

            if match["attrs"] is not None:
                attrs = {}
                for e in match["attrs"].split(","):
                    items = e.split("=")
                    k = items[0]
                    v = items[1]
                    attrs[k] = v
            else:
                attrs = {}
                             
            return Struct(SSAVar.parse(match["res"]), type_rex, attrs)

    def __repr__(self):
        optional_type = '' if len(self.types) == 0 else f' : {", ".join([repr(type_) for type_ in self.types])}'
        return f"FeltUnary({self.result} = {self.op}({self.operand}){optional_type}"




         
class StructDef(Operation):
    pass

class StructRead(Operation):
    pass

class StructWrite(Operation):
    pass

class StructMember(Operation):
    pass

class StructDialect(Dialect):

    def __init__(self):
        super().__init__("struct")
        self.register(StructNew)
        self.register(StructDef)
        self.register(StructWrite)
        self.register(StructMember)

        
    def parse_complex(self, cursor, lines, parse_fn, find_brace_fn):
        line = lines[cursor]
        
        if "struct.def" in line:
            struct_name = line.split("struct.def")[1].split('{')[0].strip()
            end_struct = find_brace_fn(cursor)
            
            # El interior de un struct puede tener campos (líneas simples) 
            # o funciones (dialecto 'function')
            content = parse_fn(cursor + 1, end_struct)
            
            return {
                "type": "struct_definition",
                "name": struct_name,
                "body": content
            }, end_struct + 1
            
        # Para operaciones simples como struct.new, struct.readf, etc.
        return self.parse_line(line), cursor + 1

    
