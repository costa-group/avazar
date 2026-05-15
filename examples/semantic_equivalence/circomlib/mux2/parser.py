import re

def procesar_smt(fichero_path):
    with open(fichero_path, 'r') as f:
        contenido = f.read()

    # 1. Regex para capturar define-fun, sus argumentos y su cuerpo
    # Explicación:
    # (define-fun\s+(@\w+) -> Captura el nombre
    # \s+\((.*?)\)         -> Captura todo lo que hay dentro de los paréntesis de argumentos
    # \s+\w+\s+            -> Salta el tipo de retorno (Bool, FFp, etc.)
    # ([\s\S]*?)(?=\n\)\n|\n\(define-fun|\n\(assert) -> Captura el cuerpo hasta el cierre o sig. función
    
    patron_fun = re.compile(r'\(define-fun\s+(@\w+)\s+\((.*?)\)\s+\w+\s+([\s\S]*?)(?=\n\)\s*\n|\n\(define-fun|\n\(assert)', re.MULTILINE)
    
    funciones_procesadas = {}

    for match in patron_fun.finditer(contenido):
        nombre = match.group(1)
        args_raw = match.group(2)
        cuerpo = match.group(3).strip()

        # 2. Procesar variables (v_0 FFp) -> ['v_0', 'v_1', ...]
        variables = re.findall(r'\((\w+)\s+\w+\)', args_raw)

        # 3. Almacenar
        funciones_procesadas[nombre] = {
            "variables": variables,
            "ecuacion": cuerpo
        }

    return funciones_procesadas

# --- Ejecución ---
datos = procesar_smt('mux2_1_concrete.smt2')

for nombre, info in datos.items():
    print(f"Función: {nombre}")
    print(f"  Variables ({len(info['variables'])}): {', '.join(info['variables'])}")
    print(f"  Ecuación (resumen): {info['ecuacion'][:100]}...") 
    print("-" * 30)