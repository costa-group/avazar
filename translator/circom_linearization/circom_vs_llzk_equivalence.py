#!/usr/bin/env python3
"""Equivalence between the r1cs circom generates for a circuit and the one
circom-llzk + llzk-translate --llzk-to-r1cs generate for the same circuit.

Both r1cs are generated as complete_avazar.py does for each value of
--r1cs-from, and then compared by the checks selected with --checks (both by
default):
  * avazar: `avazar <circom r1cs> --check_equivalence <llzk r1cs>`
  * equivalence: `equivalence <circom r1cs> <llzk r1cs>`
The sizes of both r1cs and the verdict of each check are written as a single
row of a csv file.
"""

import argparse
import csv
import logging
import os
import re
import shutil
import subprocess
import sys
from typing import List

from llzk_r1cs import layout_to_signals

# Tool paths are relative to the root of the repository, not to the cwd
REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
CIRCOM = os.path.join(REPO_ROOT, "circom/target/release/circom")
CIRCOM_LLZK = os.path.join(REPO_ROOT, "circom-llzk/result/bin/circom")
LLZK_TRANSLATE = os.path.join(REPO_ROOT, "llzk-lib/build/bin/llzk-translate")
AVAZAR_TOOL = os.path.join(REPO_ROOT, "avazar_tool/target/release/avazar")
EQUIVALENCE_TOOL = os.path.join(REPO_ROOT, "avazar_tool/target/release/equivalence")


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

CHECKS = ["avazar", "equivalence"]

# Columns of the csv. status is "ok" when every selected check is "ok", and
# otherwise the first step that failed. Each check has its own status:
#   * avazar_status: "ok" when avazar ran and its output was parsed
#   * equivalence_status: "ok" when the equivalence tool exited with 0 and its
#     output was parsed
# and is empty when the check was not selected. The sizes of the r1cs come
# from the output of avazar.
FIELDS = [
    "circuit", "circom_file", "prime", "checks", "status",
    "circom_constraints", "circom_signals", "llzk_constraints", "llzk_signals",
    "avazar_status", "verified_nodes", "failed_nodes", "timeout_nodes", "verification_time",
    "equivalence_status", "equivalence_exit_code", "equivalence_result", "equivalence_reason",
    "equivalence_encoding_ms", "equivalence_preprocessing_ms", "equivalence_fingerprinting_ms",
    "equivalence_solving_ms", "equivalence_total_ms",
    "error",
]

# The first version is the first r1cs given to avazar (circom's), the second
# one the r1cs given to --check_equivalence (circom-llzk's). Only the first
# occurrence is kept: it belongs to node 0, the main component.
PATTERNS = {
    "circom_signals": r"Number of signals in the first version \(i,int,o\):\s*(\d+)",
    "llzk_signals": r"Number of signals in the second version \(i,int,o\):\s*(\d+)",
    "circom_constraints": r"Number of constraints in the first template:\s*(\d+)",
    "llzk_constraints": r"Number of constraints in the second template:\s*(\d+)",
    "verified_nodes": r"Number of verified nodes \(equivalence\):\s*(\d+)",
    "failed_nodes": r"Number of failed nodes \(equivalence\):\s*(\d+)",
    "timeout_nodes": r"Number of timeout nodes \(equivalence\):\s*(\d+)",
}


# Phases in the timing of the equivalence tool, each one an equivalence_<phase>_ms column
EQUIVALENCE_PHASES = ["encoding", "preprocessing", "fingerprinting", "solving", "total"]

# Units of a Rust Duration printed with {:?}, in milliseconds
DURATION_UNITS = {"ns": 1e-6, "µs": 1e-3, "us": 1e-3, "ms": 1.0, "s": 1000.0}


class StepError(Exception):
    """A step of the pipeline failed; status is the value of the csv column."""

    def __init__(self, status: str, message: str):
        super().__init__(message)
        self.status = status


def run_command(command: List[str], status: str):
    logging.info(f"Executing: {' '.join(command)}")
    try:
        res = subprocess.run(command, capture_output=True, text=True)
    except FileNotFoundError as e:
        raise StepError(status, str(e))
    if res.returncode != 0:
        logging.error(f"Command failed with exit code {res.returncode}: {' '.join(command)}")
        if res.stdout:
            logging.error(f"stdout:\n{res.stdout}")
        if res.stderr:
            logging.error(f"stderr:\n{res.stderr}")
        raise StepError(status, f"exit code {res.returncode}: {res.stderr.strip()[-500:]}")
    logging.info(f"Finished {command[0]}")
    return res


def circom_r1cs(circom_file: str, out_dir: str, prime: str) -> str:
    """r1cs and _signals.json of circom_file generated by circom (--O0), in out_dir."""
    name = os.path.basename(circom_file).split(".circom")[0]
    os.makedirs(out_dir, exist_ok=True)
    run_command([CIRCOM, circom_file, "--r1cs", "--O0", "--prime", prime, "--name_to_signal", "--output", out_dir], "circom_error")
    return os.path.join(out_dir, name + ".r1cs")


def llzk_r1cs(circom_file: str, out_dir: str, prime: str) -> str:
    """r1cs and _signals.json of circom_file generated by circom-llzk +
    llzk-translate, in out_dir. The _signals.json is the .llzk-layout in
    circom's notation, as in complete_avazar.py."""
    name = os.path.basename(circom_file).split(".circom")[0]
    os.makedirs(out_dir, exist_ok=True)
    # Same flags as complete_avazar.generate_llzk
    run_command([CIRCOM_LLZK, circom_file, "--llzk", "concrete", "--prime", prime, "--output", out_dir,
                 "--llzk_plaintext", "--llzk_strip_debug_info"], "circom_llzk_error")

    llzk_file = os.path.join(out_dir, name + ".llzk")
    if os.path.exists(llzk_file):
        os.remove(llzk_file)
    shutil.move(os.path.join(out_dir, name + "_llzk", name + ".llzk"), out_dir)
    shutil.rmtree(os.path.join(out_dir, name + "_llzk"))

    r1cs = os.path.join(out_dir, name + ".r1cs")
    layout = os.path.join(out_dir, name + ".llzk-layout")
    run_command([LLZK_TRANSLATE, llzk_file, "--llzk-to-r1cs", "--r1cs-prime", str(PRIMES[prime]), "--llzk-layout-map=" + layout, "-o", r1cs], "llzk_translate_error")
    try:
        layout_to_signals(layout, os.path.join(out_dir, name + "_signals.json"))
    except Exception as e:
        raise StepError("llzk_signals_error", f"{layout}: {e}")
    return r1cs


def parse_avazar_output(output: str) -> dict:
    """Sizes of both r1cs and number of verified/failed/timeout nodes."""
    row = {}
    for field, pattern in PATTERNS.items():
        match = re.search(pattern, output)
        row[field] = int(match.group(1)) if match else None
    times = [float(t) for t in re.findall(r"Verification time per template:\s*([0-9.eE+-]+)", output)]
    row["verification_time"] = sum(times) if times else None
    return row


def avazar_check(circom_file: str, llzk_file: str, args, log_path: str) -> dict:
    """Columns of `avazar <circom r1cs> --check_equivalence <llzk r1cs>`. Its
    output is kept in log_path."""
    command = [AVAZAR_TOOL, circom_file, "--check_equivalence", llzk_file, "--solver", args.solver, "--verbose"]
    if args.timeout is not None:
        command += ["--timeout", str(args.timeout)]
    res = run_command(command, "avazar_error")
    with open(log_path, "w") as f:
        f.write(res.stdout)
    print(res.stdout)

    row = parse_avazar_output(res.stdout)
    missing = [field for field in PATTERNS if row[field] is None]
    if missing:
        raise StepError("avazar_parse_error", f"Not found in the output of avazar: {', '.join(missing)}")
    row["avazar_status"] = "ok"
    return row


def parse_equivalence_output(output: str) -> dict:
    """Verdict, reason and timing (in ms) of the equivalence tool, from its
    `ComparisonData { result: true, reason: None, timing: {"encoding":
    133.094807ms, ...}, ... }`. A field that is not found is None."""
    row = {}
    match = re.search(r"\bresult:\s*(true|false)\b", output)
    row["equivalence_result"] = match.group(1) if match else None

    # None, or Some(...) with whatever the tool gives as the reason
    match = re.search(r"\breason:\s*(.*?),\s*timing:", output, re.DOTALL)
    reason = match.group(1).strip() if match else None
    if reason is not None:
        some = re.fullmatch(r"Some\((.*)\)", reason, re.DOTALL)
        reason = None if reason == "None" else (some.group(1) if some else reason).strip().strip('"')
    row["equivalence_reason"] = reason

    timing = {}
    match = re.search(r"\btiming:\s*\{(.*?)\}", output, re.DOTALL)
    if match:
        for phase, value, unit in re.findall(r'"(\w+)":\s*([0-9.eE+-]+)\s*(ns|µs|us|ms|s)\b', match.group(1)):
            timing[phase] = float(value) * DURATION_UNITS[unit]
    for phase in EQUIVALENCE_PHASES:
        row[f"equivalence_{phase}_ms"] = timing.get(phase)
    return row


def equivalence_check(circom_file: str, llzk_file: str, log_path: str) -> dict:
    """Columns of `equivalence <circom r1cs> <llzk r1cs>`. Its output is kept
    in log_path. A non-zero exit code is not raised: its output may still say
    why, so it goes to the csv together with whatever could be parsed."""
    command = [EQUIVALENCE_TOOL, circom_file, llzk_file]
    logging.info(f"Executing: {' '.join(command)}")
    try:
        res = subprocess.run(command, capture_output=True, text=True)
    except FileNotFoundError as e:
        raise StepError("equivalence_error", str(e))
    with open(log_path, "w") as f:
        f.write(res.stdout + res.stderr)
    print(res.stdout)
    logging.info(f"Finished {command[0]} with exit code {res.returncode}")

    row = parse_equivalence_output(res.stdout + res.stderr)
    row["equivalence_exit_code"] = res.returncode
    if res.returncode != 0:
        row["equivalence_status"] = "equivalence_error"
    elif row["equivalence_result"] is None:
        row["equivalence_status"] = "equivalence_parse_error"
    else:
        row["equivalence_status"] = "ok"
    return row


def write_csv(csv_path: str, row: dict):
    os.makedirs(os.path.dirname(os.path.abspath(csv_path)), exist_ok=True)
    with open(csv_path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=FIELDS)
        writer.writeheader()
        writer.writerow(row)


def main():
    logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s", handlers=[logging.StreamHandler(sys.stdout)])

    parser = argparse.ArgumentParser(description="Check the equivalence of the r1cs generated by circom and by circom-llzk for a circom file")
    parser.add_argument("-s", "--source", type=str, required=True, help="Circom circuit file.")
    parser.add_argument("-out", "--out", type=str, required=False, default="/tmp/avazar_output/", help="Output Path")
    parser.add_argument("-solver", "--solver", type=str, required=False, default="ffsol", help="Solver to be used")
    parser.add_argument("-tout", "--timeout", type=int, required=False, help="Timeout for the solver expressed in miliseconds")
    parser.add_argument("-p", "--prime", type=str, required=False, choices=sorted(PRIMES), default="goldilocks", help="Prime number used to generate the circuit")
    parser.add_argument("--csv", type=str, required=False, help="Csv file with the results (defaults to <out>/<name>.csv)")
    parser.add_argument("--checks", type=str, nargs="+", required=False, choices=CHECKS, default=CHECKS, help="Checks to run on both r1cs (defaults to all of them)")

    args = parser.parse_args()

    name = os.path.basename(args.source).split(".circom")[0]
    out_abs_path = os.path.abspath(args.out)
    csv_path = args.csv if args.csv else os.path.join(out_abs_path, name + ".csv")
    row = {field: None for field in FIELDS}
    checks = [check for check in CHECKS if check in args.checks]
    row.update(circuit=name, circom_file=os.path.abspath(args.source), prime=args.prime, checks="+".join(checks))

    try:
        if not os.path.isfile(args.source):
            raise StepError("file_error", f"Source file {args.source} does not exist")
        os.makedirs(out_abs_path, exist_ok=True)

        # 1. both r1cs, in separate directories: they share the same name
        circom_file = circom_r1cs(args.source, os.path.join(out_abs_path, "circom"), args.prime)
        llzk_file = llzk_r1cs(args.source, os.path.join(out_abs_path, "llzk"), args.prime)

        # 2. the checks, each one on its own: one failing does not stop the
        # other. Their output is kept in <out>/<name>_<check>.log
        errors = []
        for check in checks:
            log_path = os.path.join(out_abs_path, f"{name}_{check}.log")
            try:
                if check == "avazar":
                    row.update(avazar_check(circom_file, llzk_file, args, log_path))
                else:
                    row.update(equivalence_check(circom_file, llzk_file, log_path))
            except StepError as e:
                logging.error(f"{e.status}: {e}")
                row[f"{check}_status"] = e.status
                errors.append(f"{check}: {e}")

        # 3. overall status: the first check that is not ok
        failed = [row[f"{check}_status"] for check in checks if row[f"{check}_status"] != "ok"]
        row["status"] = failed[0] if failed else "ok"
        row["error"] = "; ".join(errors) or None

    except StepError as e:
        # The r1cs could not be generated: no check could run
        logging.error(f"{e.status}: {e}")
        row.update(status=e.status, error=str(e))
    except Exception as e:
        logging.error(f"Unexpected error: {e}")
        row.update(status="unexpected_error", error=str(e))
    finally:
        write_csv(csv_path, row)
        logging.info(f"Results: {csv_path}")

    sys.exit(0 if row["status"] == "ok" else 1)


if __name__ == '__main__':
    main()
