import json
import sys

def agrupar_nodos(nodos_1, nodos_2):
    agrupados = {}
    campos_objetivo = ['constraints', 'signals', 'input_signals', 'output_signals']

    for nodo in nodos_1:
        nombre = nodo.get("node_id", "Unknown")
        if nombre not in agrupados:
            agrupados[nombre] = {}
        
        for clave, valor in nodo.items():
            if clave in campos_objetivo:
                agrupados[nombre][f"{clave}_1"] = valor
            else:
                agrupados[nombre][clave] = valor

    for nodo in nodos_2:
        nombre = nodo.get("node_id", "Unknown")
        if nombre not in agrupados:
            agrupados[nombre] = {}
        
        for clave, valor in nodo.items():
            if clave in campos_objetivo:
                agrupados[nombre][f"{clave}_2"] = valor

    list_nodos = []
    for (nombre, valor) in agrupados.items():
        list_nodos.append(valor)
    return list_nodos

def main():
    if len(sys.argv) != 4:
        print("Uso: python script.py <file1.json> <file2.json> <output.json>")
        return

    with open(sys.argv[1], 'r') as f1: data1 = json.load(f1)
    with open(sys.argv[2], 'r') as f2: data2 = json.load(f2)

    # Mantenemos la estructura original pero transformamos 'nodes'
    resultado = data1.copy() # Copiamos timing, equivalency, etc. del primero
        
    resultado['nodes'] = agrupar_nodos(
        data1.get('nodes', []), 
        data2.get('nodes', [])
    )

    with open(sys.argv[3], 'w') as f_out:
        json.dump(resultado, f_out, indent=2)
        


if __name__ == "__main__":
    main()