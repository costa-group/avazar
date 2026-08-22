#!/usr/bin/env python3

import subprocess
import json
import os
import sys
sys.path.append("translator/llzk2core/src")
sys.path.append("translator/circom_linearization")

from typing import List
import logging
import argparse
import shutil
from execution.main_execution import main as llzk2core_main

from linearize_component_names import main as linearize_components
from linearize_signal_names import main as linearize_signals


VERSION = "1.0.0"
CIRCOM = "circom/target/release/circom"
CIRCOM_LLZK = "circom-llzk/target/release/circom"
AVAZAR_TOOL = "avazar_tool/target/release/avazar"

PRIMES = {
    "goldilocks": 18446744069414584321,
    "secq256r1": 115792089210356248762697446949407573529996955224253574108868205240008320037127,
    "pallas": 28948022309329048855892746252171976963363056481941560715954679059200803120067,
    "vesta": 28948022309329048855892746252171976963363056481941600130006322964104920678209,
    "bn128": 21888242871839275222246405745257275088548364400416034343698204186575808495617,
    "grumpkin": 21888242871839275222246405745257275088696311157297823662689037894645226208583,
    "bls12377": 25866442601296909401065273369489353353639351283510007695335291307297420126659,
    "bls12381": 52435875175126190479447740508185965837690552500527637822603658699938581184513,
}


def run_command(command: List[str]):
    logging.info(f"Executing: {command}")
    try:
        res = subprocess.run(command, capture_output=True, text=True, check=True)
    except subprocess.CalledProcessError as e:
        logging.error(f"Command failed with exit code {e.returncode}: {' '.join(command)}")
        if e.stdout:
            logging.error(f"stdout:\n{e.stdout}")
        if e.stderr:
            logging.error(f"stderr:\n{e.stderr}")
        raise

    logging.info(f"Finished {command}")
    return res


def spec_prime(spec_path: str):
    """The prime the llzk specification declares, or None if it cannot be read.
    It may be written as a number or as a string: a 254-bit prime does not
    survive most JSON writers as a number."""
    try:
        with open(spec_path) as f:
            declared = json.load(f).get("prime")
    except (OSError, json.JSONDecodeError) as e:
        logging.warning(f"Could not read the prime declared by {spec_path}: {e}")
        return None
    if declared is None:
        return None
    try:
        return int(declared)
    except (TypeError, ValueError):
        logging.warning(f"The specification declares an unreadable prime: {declared!r}")
        return None


def warn_on_prime_mismatch(spec_path: str, prime_name: str):
    """The r1cs follows --prime, the specification does not: llzk2core always
    emits it in Goldilocks (llzk_cli -zk g64), so any other --prime puts the two
    sides in different fields. Neither check stops for it -- correctness never
    reads the specification's prime, and semantic equivalence is given
    --ignore_spec_prime -- so say it out loud here instead."""
    declared = spec_prime(spec_path)
    from_cli = PRIMES[prime_name]
    if declared is None or declared == from_cli:
        return
    logging.warning(
        f"PRIME MISMATCH: the r1cs is over {prime_name} ({from_cli}) but the llzk "
        f"specification declares {declared}. Both sides are verified inside a single "
        f"field sort, so every field literal of the specification is reinterpreted "
        f"modulo {prime_name}: the checks still run, but a VERIFIED verdict may be "
        f"vacuous and proves nothing."
    )


def main():

    logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s", handlers=[logging.StreamHandler(sys.stdout)])

    logging.info(f"=== COMPLETE AVAZAR v{VERSION} ===")

    parser = argparse.ArgumentParser(description="Complete AVAZAR pipeline: generate the artefacts and run the semantic equivalence check")
    parser.add_argument("-s", "--source", type=str, required=True, help="Circom circuit file.")
    parser.add_argument("-out", "--out", type=str, required=False, default="/tmp/avazar_output/", help="Output Path")
    parser.add_argument("-solver", "--solver", type=str, required=False, default="ffsol", help="Solver to be used")
    parser.add_argument("-tout", "--timeout", type=int, required=False, help="Timeout for the solver expressed in miliseconds")
    parser.add_argument("-p", "--prime", type=str, required=False, choices=["bn128", "bls12377", "bls12381", "goldilocks", "grumpkin", "pallas", "secq256r1", "vesta"], default="goldilocks", help="Prime number used to generate the circuit")
    parser.add_argument("--report-dir", type=str, required=False, help="Directory to store semantic equivalence reports (defaults to <out>/semantic_equivalence_runs)")

    args = parser.parse_args()

    try:
        if not os.path.isfile(args.source):
            raise FileNotFoundError(f"Source file {args.source} does not exist")

        out_abs_path = os.path.abspath(args.out)

        if args.out and not os.path.exists(out_abs_path):
            logging.info(f"Dir {args.out} does not exist. Creating...")
            os.makedirs(out_abs_path, exist_ok=True)

        root_name_ext = os.path.basename(args.source)
        root_name_withoutext = root_name_ext.split(".circom")[0]

        # 1. run circom to generate r1cs
        circom_command = [CIRCOM, args.source, "--r1cs", "--O0", "--prime", args.prime, "--name_to_signal", "--output", out_abs_path]
        run_command(circom_command)

        # 1.b run the linearization
        #args_comp = out_abs_path + "/" + root_name_withoutext + "_structure.json"
        #linearize_components(args_comp, args_comp)
        args_sig = out_abs_path + "/" + root_name_withoutext + "_signals.json"
        linearize_signals(args_sig, args_sig)

        # 2. run circom-llzk to generate llzk-ir
        # --llzk_strip_debug_info: since circom-llzk #450 every op carries a loc(...)
        # suffix, which llzk2core does not skip and which perturbs the clustering
        # enough that --check_semantic_equivalence refuses the run.
        # --prime, like circom above: circom-llzk defaults to bn128, so without it
        # the llzk ir is over a different field than the r1cs on every run that
        # does not ask for bn128 -- including the goldilocks default.
        circom_llzk_command = [CIRCOM_LLZK, args.source, "--llzk", "concrete", "--prime", args.prime, "--output", out_abs_path, "--llzk_plaintext", "--llzk_strip_debug_info"]
        run_command(circom_llzk_command)

        dest_llzk = out_abs_path + "/" + root_name_withoutext + ".llzk"
        if os.path.exists(dest_llzk):
            os.remove(dest_llzk)
        shutil.move(out_abs_path + "/" + root_name_withoutext + "_llzk/" + root_name_withoutext + ".llzk", out_abs_path)
        shutil.rmtree(out_abs_path + "/" + root_name_withoutext + "_llzk/")

        # 3. call to llzk2core
        llzk2core_args = argparse.Namespace(source=out_abs_path + "/" + root_name_withoutext + ".llzk", target=out_abs_path + "/" + root_name_withoutext + ".core")
        llzk2core_main(llzk2core_args)

        spec_json = out_abs_path + "/" + root_name_withoutext + ".json"

        # 3.b the specification's prime against --prime, before anything uses it
        warn_on_prime_mismatch(spec_json, args.prime)

        # 4. semantic equivalence check
        # The only check this pipeline runs. No --input_structure: avazar derives
        # the structure from the specification's components_info/vars_info plus
        # --correspondence, which is why circom no longer needs --print_tree_info.
        report_root = args.report_dir if args.report_dir else os.path.join(out_abs_path, "semantic_equivalence_runs")
        report_dir = os.path.join(report_root, root_name_withoutext)
        os.makedirs(report_dir, exist_ok=True)
        report_path = os.path.join(report_dir, "report.json")

        sem_eq_command = [AVAZAR_TOOL, out_abs_path + "/" + root_name_withoutext + ".r1cs", "--check_semantic_equivalence", spec_json, "--correspondence", out_abs_path + "/" + root_name_withoutext + "_signals.json", "--solver", args.solver, "--report", report_path, "--verbose", "--prime", str(PRIMES[args.prime])]

        if args.timeout is not None:
            sem_eq_command += ["--timeout", str(args.timeout)]

        logging.info("Running avazar semantic equivalence check:")
        print(" ".join(sem_eq_command))
        res_sem = run_command(sem_eq_command)
        print(res_sem.stdout)
        logging.info(f"Semantic equivalence report: {report_path}")

    except FileNotFoundError as e:
        logging.error(f"File error: {e}")
        sys.exit(1)
    except Exception as e:
        logging.error(f"Unexpected error: {e}")
        sys.exit(1)


if __name__ == '__main__':
    main()
