#!/usr/bin/env python3

import subprocess
import os
import sys
sys.path.append("translator/llzk2core/src")
from typing import List
import logging
import argparse
import shutil
from execution.main_execution import main as llzk2core_main


VERSION = "1.0.0"
CIRCOM = "circom/target/release/circom"
CIRCOM_LLZK = "circom-llzk/target/release/circom"
AVAZAR_TOOL = "avazar_tool/target/release/avazar"

def run_command(command: List[str]):
    logging.info(f"Executing: {command}")
    try:
        res = subprocess.run(command,capture_output = True, text=True, check = True)
    except Exception as e:
        e.printMessage()
        
    logging.info(f"Finished {command}")
    

def main():

    logging.basicConfig( level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s",handlers=[logging.StreamHandler(sys.stdout)] )

    
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
    parser.add_argument( "-out", type=str, required=False, default = "/tmp/avazar_output/", help="Output Path"  )

    #Flag -solver (default ffsol)
    parser.add_argument( "-solver", type=str, required=False, default="ffsol", help = "Solver to be used")
    
    args = parser.parse_args()
    
    try:
        if not os.path.isfile(args.source):
            raise FileNotFoundError(f"Source file {args.source} does not exist")
            
        # if not os.path.isfile(args.llzk):
        #     raise FileNotFoundError(f"El fichero llzk especificado no existe: {args.llzk}")

        out_abs_path = os.path.abspath(args.out)
        
        if args.out and not os.path.exists(out_abs_path):
            logging.info(f"Dir {args.out} does not exist. Creating...")
            os.makedirs(args.out, exist_ok=True)
            
        root_name_ext = os.path.basename(args.source)
        root_name_withoutext = root_name_ext.split(".circom")[0]


        #1. run circom to generate r1cs
        circom_command = [CIRCOM, args.source,"--r1cs", "--O0", "--print_tree_info", "--name_to_signal", "--output", out_abs_path]
        run_command(circom_command)

        #2. run circom-llzk to generate llzk-ir
        circom_llzk_command = [CIRCOM_LLZK, args.source,"--llzk", "concrete", "--output", out_abs_path, "--llzk_plaintext"]
        run_command(circom_llzk_command)

        dest_llzk = out_abs_path+"/"+root_name_withoutext+".llzk"
        if os.path.exists(dest_llzk):
            os.remove(dest_llzk)
        shutil.move(out_abs_path+"/"+root_name_withoutext+"_llzk/"+root_name_withoutext+".llzk",out_abs_path)
        shutil.rmtree(out_abs_path+"/"+root_name_withoutext+"_llzk/")

        #3. call to llzk2core
        llzk2core_args = argparse.Namespace(source=out_abs_path+"/"+root_name_withoutext+".llzk",target=out_abs_path+"/"+root_name_withoutext+".core")
        llzk2core_main(llzk2core_args)

        #4. call to the solver
        avazar_tool_command = [AVAZAR_TOOL, out_abs_path+"/"+root_name_withoutext+".r1cs", "--input_structure", out_abs_path+"/"+root_name_withoutext+"_structure.json", "--check_correctness", out_abs_path+"/"+root_name_withoutext+".json", "--correspondance", out_abs_path+"/"+root_name_withoutext+"_signals.json", "--solver", args.solver, "--verbose"]
        print(" ".join(avazar_tool_command))
        run_command(avazar_tool_command)

        
        
    except FileNotFoundError as e:
        logging.error(f"File error: {e}")
        sys.exit(1)
    except Exception as e:
        logging.error(f"Unexpeted error: {e}")
        sys.exit(1)
    
if __name__ == '__main__':
    main()

