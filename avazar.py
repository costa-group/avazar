#!/usr/bin/env python3

import subprocess
import os
import sys
from typing import List
import logging


VERSION = "1.0.0"

def run_command(command: List[str]):
    logging.info(f"Executing: {command}")

    res = subprocess.run(command,capture_output = True, text=True, check = True)
    logging.info(f"Finished {command}")


    

def main():
    logging.info(f"=== AVAZAR Tool v{VERSION} ===")
    

    parser = argparse.ArgumentParser(
        description="AVAZAR Tool Script"
    )
    
    # Flag -s (mandatory)
    parser.add_argument("-s", "--source", type=str, required=True,
                        help="Circom circuit file."  )
    
    # Flag -llzk (mandatory)
    parser.add_argument("-llzk", type=str, required=True, help="LLZK file corresponding to the circuit specified in -s"  )
    
    # Flag -out (mandatory)
    parser.add_argument( "-out", type=str, required=True, help="Output Path"  )
    
    # Parsear los argumentos de la línea de comandos
    args: argparse.Namespace = parser.parse_args()
    
    try:
        # 2. Validación de existencia de los ficheros de lectura
        if not os.path.isfile(args.source):
            raise FileNotFoundError(f"El fichero source especificado no existe: {args.source}")
            
        if not os.path.isfile(args.llzk):
            raise FileNotFoundError(f"El fichero llzk especificado no existe: {args.llzk}")
        
        # 3. Obtener el directorio del tercer fichero (-out)
        # os.path.dirname("ruta/al/fichero.txt") -> devuelve "ruta/al"
        # os.path.abspath asegura que la ruta sea absoluta y limpia
        ruta_absoluta_out: str = os.path.abspath(args.out)
        directorio_salida: str = os.path.dirname(ruta_absoluta_out)
        
        # Opcional: Crear el directorio de salida si no existe
        if directorio_salida and not os.path.exists(directorio_salida):
            logging.info(f"El directorio {directorio_salida} no existe. Creándolo...")
            os.makedirs(directorio_salida, exist_ok=True)

        # 4. Ejecutar la lógica principal
        procesar_ficheros(
            fichero_source=args.source, 
            fichero_llzk=args.llzk, 
            directorio_out=directorio_salida
        )
        
    except FileNotFoundError as e:
        logging.error(f"Error de archivo: {e}")
        sys.exit(1)
    except Exception as e:
        logging.error(f"Ocurrió un error inesperado: {e}")
        sys.exit(1)
    
if __name__ == '__main__':
    main()

