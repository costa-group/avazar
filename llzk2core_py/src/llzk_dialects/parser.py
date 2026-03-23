from typing import List, Dict, Any

from typing import List, Dict, Any, Callable, Tuple

class LLZKParser:

    def __init__(self, lines: List[str]):
        self.lines = [l.strip() for l in lines if l.strip()]
        self.dialects = {}

        
    def add_dialect(self, dialect):
        self.dialects[dialect.name] = dialect

    def add_dialects(self, dialects):
        for dl in dialects:
            self.add_dialect(dl)
        
        
    def find_closing_brace(self, start_index: int) -> int:
        """Busca la llave de cierre balanceada en el array de líneas."""
        stack = 0
        for i in range(start_index, len(self.lines)):
            stack += self.lines[i].count('{')
            stack -= self.lines[i].count('}')
            if stack == 0:
                return i
        return -1

    
    def parse_module(self) -> Dict[str, Any]:
        
        module_data = {"attributes": None, "structs": {}}

        cursor = 0
        while cursor < len(self.lines):
            line = self.lines[cursor]
            if line.startswith("module attributes"):
                module_data["attributes"] = line
                cursor += 1
            elif "struct.def" in line:
                name = line.split("struct.def")[1].split('{')[0].strip()
                end = self.find_closing_brace(cursor)
                module_data["structs"][name] = self._parse_struct_body(cursor + 1, end)
                cursor = end + 1
            else: cursor += 1
        return module_data

    
    def _parse_struct_body(self, start: int, end: int) -> Dict[str, Any]:
        body = {"fields": [], "functions": {}}
        cursor = start
        while cursor < end:
            line = self.lines[cursor]
            if "struct.field" in line or "struct.member" in line:
                body["fields"].append(line)
                cursor += 1
            elif "function.def" in line:
                name = line.split("function.def")[1].split('(')[0].strip()
                closing = self.find_closing_brace(cursor)
                body["functions"][name] = {
                    "header": line,
                    "operations": self.parse_range(cursor + 1, closing)
                }
                cursor = closing + 1
            else: cursor += 1
        return body

    
    def parse_range(self, start: int, end: int) -> List[Any]:
        """Parsea un rango de líneas devolviendo objetos Operation."""
        ops = []
        cursor = start
        while cursor < end:
            line = self.lines[cursor]
            if line == "}" or line.startswith("^bb"):
                cursor += 1; continue

            cmd_part = line.split('=')[-1].strip()
            prefix = cmd_part.split('.')[0]

            if prefix == "scf" and ("while" in line or "if" in line):
                #Pasamos solo lo necesario al dialecto SCF
                op, next_cursor = self.dialects["scf"].parse_complex(
                    cursor, 
                    self.lines, 
                    self.parse_range, 
                    self.find_closing_brace
                )
                ops.append(op)
                cursor = next_cursor
            elif prefix in self.dialects:
                ops.append(self.dialects[prefix].parse_line(line))
                cursor += 1
            else:
                cursor += 1
        return ops
