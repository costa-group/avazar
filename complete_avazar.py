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
from llzk_r1cs import layout_to_signals


VERSION = "1.0.0"
CIRCOM = "circom/target/release/circom"
CIRCOM_LLZK = "circom-llzk/result/bin/circom"
LLZK_TRANSLATE = "llzk-lib/build/bin/llzk-translate"
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


def generate_llzk(circom_file: str, out_abs_path: str, prime: str) -> str:
    """Run circom-llzk on circom_file and leave the result as <out>/<name>.llzk."""
    name = os.path.basename(circom_file).split(".circom")[0]
    # --llzk_strip_debug_info: since circom-llzk #450 every op carries a loc(...)
    # suffix, which llzk2core does not skip and which perturbs the clustering
    # enough that --check_semantic_equivalence refuses the run.
    # --prime, like circom: circom-llzk defaults to bn128, so without it
    # the llzk ir is over a different field than the r1cs on every run that
    # does not ask for bn128 -- including the goldilocks default.
    circom_llzk_command = [CIRCOM_LLZK, circom_file, "--llzk", "concrete", "--prime", prime, "--output", out_abs_path, "--llzk_plaintext", "--llzk_strip_debug_info"]
    run_command(circom_llzk_command)

    dest_llzk = out_abs_path + "/" + name + ".llzk"
    if os.path.exists(dest_llzk):
        os.remove(dest_llzk)
    shutil.move(out_abs_path + "/" + name + "_llzk/" + name + ".llzk", out_abs_path)
    shutil.rmtree(out_abs_path + "/" + name + "_llzk/")
    return dest_llzk


def run_circom(circom_file: str, out_dir: str, prime: str):
    """r1cs, _signals.json and _structure.json of circom_file, in out_dir."""
    os.makedirs(out_dir, exist_ok=True)
    circom_command = [CIRCOM, circom_file, "--r1cs", "--O0", "--prime", prime, "--name_to_signal", "--output", out_dir, "--print_tree_info"]
    run_command(circom_command)


def main():

    logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s", handlers=[logging.StreamHandler(sys.stdout)])

    logging.info(f"=== COMPLETE AVAZAR v{VERSION} ===")

    parser = argparse.ArgumentParser(description="Complete AVAZAR pipeline: generate the artefacts and run the semantic equivalence check")
    parser.add_argument("-s", "--source", type=str, required=True, help="Circom circuit file (the r1cs is generated from it).")
    parser.add_argument("-sp", "--spec", type=str, required=False, help="Specification file (witness code generation). Defaults to --source.", dest="spec")
    parser.add_argument("-out", "--out", type=str, required=False, default="/tmp/avazar_output/", help="Output Path")
    parser.add_argument("-solver", "--solver", type=str, required=False, default="ffsol", help="Solver to be used")
    parser.add_argument("-tout", "--timeout", type=int, required=False, help="Timeout for the solver expressed in miliseconds")
    parser.add_argument("-p", "--prime", type=str, required=False, choices=["bn128", "bls12377", "bls12381", "goldilocks", "grumpkin", "pallas", "secq256r1", "vesta"], default="goldilocks", help="Prime number used to generate the circuit")
    parser.add_argument("--r1cs-from", type=str, required=False, choices=["circom", "llzk"], default="circom", dest="r1cs_from", help="Tool that generates the r1cs of --source: circom (--O0) or circom-llzk + llzk-translate --llzk-to-r1cs")
    parser.add_argument("--report-dir", type=str, required=False, help="Directory to store semantic equivalence reports (defaults to <out>/semantic_equivalence_runs)")

    args = parser.parse_args()

    try:
        if not os.path.isfile(args.source):
            raise FileNotFoundError(f"Source file {args.source} does not exist")

        if args.spec is None:
            args.spec = args.source
        if not os.path.isfile(args.spec):
            raise FileNotFoundError(f"Specification file {args.spec} does not exist")

        out_abs_path = os.path.abspath(args.out)

        if args.out and not os.path.exists(out_abs_path):
            logging.info(f"Dir {args.out} does not exist. Creating...")
            os.makedirs(out_abs_path, exist_ok=True)

        same_file = os.path.samefile(args.source, args.spec)

        root_name_withoutext_source = os.path.basename(args.source).split(".circom")[0]
        root_name_withoutext_spec = os.path.basename(args.spec).split(".circom")[0]

        # Every artefact goes to <out>/<name>.*: two different files with the
        # same name would overwrite each other's.
        if not same_file and root_name_withoutext_source == root_name_withoutext_spec:
            raise ValueError(f"--source and --spec are different files with the same name ({root_name_withoutext_source}); rename one of them")

        source_r1cs = out_abs_path + "/" + root_name_withoutext_source + ".r1cs"
        source_signals = out_abs_path + "/" + root_name_withoutext_source + "_signals.json"
        source_structure = out_abs_path + "/" + root_name_withoutext_source + "_structure.json"

        # 1. r1cs of the source, with its _signals.json (and _structure.json,
        # only used when the source is its own specification)
        if args.r1cs_from == "circom":
            run_circom(args.source, out_abs_path, args.prime)
        else:
            # 1.a circom-llzk + llzk-translate. The .llzk of the source is
            # also the specification's when both are the same file, so it is
            # generated only once (step 2).
            source_llzk = generate_llzk(args.source, out_abs_path, args.prime)
            layout = out_abs_path + "/" + root_name_withoutext_source + ".llzk-layout"
            llzk_translate_command = [LLZK_TRANSLATE, source_llzk, "--llzk-to-r1cs", "--r1cs-prime", str(PRIMES[args.prime]), "--llzk-layout-map=" + layout, "-o", source_r1cs]
            run_command(llzk_translate_command)

            # 1.b the layout as a circom-style _signals.json
            layout_to_signals(layout, source_signals)

            # 1.c --input_structure needs a _structure.json, which only circom
            # generates (--print_tree_info) and only for its own r1cs.
            if same_file:
                logging.warning("TO MODIFY: --r1cs-from llzk still calls circom, only to obtain the _structure.json for --input_structure")
                raise NotImplementedError("--r1cs-from llzk has no _structure.json for --input_structure (--source is its own --spec)")

        # 1.d run the linearization
        #linearize_components(source_structure, source_structure)
        linearize_signals(source_signals, source_signals)

        # 2. run circom-llzk to generate llzk-ir of the specification
        if args.r1cs_from == "llzk" and same_file:
            spec_llzk = source_llzk
        else:
            spec_llzk = generate_llzk(args.spec, out_abs_path, args.prime)

        # 3. call to llzk2core
        # --prime: llzk2core must simulate while-loop trip counts modulo the
        # same field circom-llzk generated the .llzk over, or a value that
        # wraps in the real field (e.g. circom's "-1") won't be simulated
        # correctly.
        llzk2core_args = argparse.Namespace(source=spec_llzk, target=out_abs_path + "/" + root_name_withoutext_spec + ".core", prime=args.prime)
        llzk2core_main(llzk2core_args)

        spec_json = out_abs_path + "/" + root_name_withoutext_spec + ".json"

        # 3.b the specification's prime against --prime, before anything uses it
        warn_on_prime_mismatch(spec_json, args.prime)

        # 4. semantic equivalence check
        # The only check this pipeline runs. When the source is its own
        # specification, --input_structure gives avazar the source's component
        # tree; otherwise avazar derives the structure from the specification's
        # components_info/vars_info plus --correspondence.
        report_root = args.report_dir if args.report_dir else os.path.join(out_abs_path, "semantic_equivalence_runs")
        report_dir = os.path.join(report_root, root_name_withoutext_source)
        os.makedirs(report_dir, exist_ok=True)
        report_path = os.path.join(report_dir, "report.json")

        sem_eq_command = [AVAZAR_TOOL, source_r1cs, "--check_semantic_equivalence", spec_json, "--correspondence", source_signals, "--solver", args.solver, "--report", report_path, "--verbose"]

        if same_file:
            sem_eq_command += ["--input_structure", source_structure]

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
