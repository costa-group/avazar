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
    
    # # Flag -llzk (mandatory)
    # parser.add_argument("-llzk", type=str, required=True, help="LLZK file corresponding to the circuit specified in -s"  )
    
    # Flag -out (mandatory)
    parser.add_argument( "-out", type=str, required=True, help="Output Path"  )

    #Flag -solver (default ffsol)
    parser.add_argument( "-solver", type=str, required=False, default="ffsol", help = "Solver to be used")
    
    args = parser.parse_args()
    
    try:
        if not os.path.isfile(args.source):
            raise FileNotFoundError(f"Source file {args.source} does not exist")
            
        # if not os.path.isfile(args.llzk):
        #     raise FileNotFoundError(f"El fichero llzk especificado no existe: {args.llzk}")
                
        if args.out and not os.path.exists(args.out):
            logging.info(f"Dir {args.out} does not exist. Creating...")
            os.makedirs(args.out, exist_ok=True)
        
            
            
    except FileNotFoundError as e:
        logging.error(f"File error: {e}")
        sys.exit(1)
    except Exception as e:
        logging.error(f"Unexpeted error: {e}")
        sys.exit(1)
    
if __name__ == '__main__':
    main()

