
class StructNew(Operation):
    pass

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

    
