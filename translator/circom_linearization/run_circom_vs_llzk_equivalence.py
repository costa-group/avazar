#!/usr/bin/env python3
"""Runs circom_vs_llzk_equivalence.py on many circom files concurrently and
combines the csv file of each run into a single one.
"""

import argparse
import csv
import logging
import multiprocessing as mp
import os
import re
import subprocess
import sys

from circom_vs_llzk_equivalence import CHECKS, FIELDS

SCRIPT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "circom_vs_llzk_equivalence.py")


def has_main_component(circom_file: str) -> bool:
    """Library files (no main component) cannot be compiled on their own."""
    try:
        with open(circom_file, errors="ignore") as f:
            return re.search(r"\bcomponent\s+main\b", f.read()) is not None
    except OSError:
        return False


def collect_circuits(inputs):
    """(key, file) for every circom file with a main component in inputs. The key
    names the output directory of the run: the path relative to the input
    directory, so files with the same name in different directories do not
    overwrite each other's results."""
    circuits, seen = [], set()
    for path in inputs:
        if os.path.isdir(path):
            files = [(os.path.relpath(os.path.join(root, f), path), os.path.join(root, f))
                     for root, _, names in os.walk(path) for f in sorted(names) if f.endswith(".circom")]
        else:
            files = [(os.path.basename(path), path)]
        for rel, file in sorted(files):
            if not has_main_component(file):
                continue
            key = rel[:-len(".circom")].replace(os.sep, "__")
            unique, i = key, 1
            while unique in seen:
                unique, i = f"{key}_{i}", i + 1
            seen.add(unique)
            circuits.append((unique, os.path.abspath(file)))
    return circuits


def run_one(job):
    key, circom_file, args = job
    out_dir = os.path.join(args.out, key)
    os.makedirs(out_dir, exist_ok=True)
    csv_path = os.path.join(out_dir, "result.csv")
    # A csv from a previous run would be taken as this run's if this one is killed
    if os.path.exists(csv_path):
        os.remove(csv_path)

    command = [sys.executable, SCRIPT, "-s", circom_file, "-out", out_dir, "-solver", args.solver, "-p", args.prime, "--csv", csv_path]
    command += ["--checks"] + args.checks
    if args.timeout is not None:
        command += ["-tout", str(args.timeout)]

    error = None
    try:
        res = subprocess.run(command, capture_output=True, text=True, timeout=args.run_timeout)
        log = res.stdout + res.stderr
    except subprocess.TimeoutExpired as e:
        log = (e.stdout or b"").decode(errors="ignore") if isinstance(e.stdout, bytes) else (e.stdout or "")
        error = f"run_timeout ({args.run_timeout}s)"
    with open(os.path.join(out_dir, "run.log"), "w") as f:
        f.write(log)

    if error is None and os.path.exists(csv_path):
        with open(csv_path, newline="") as f:
            rows = list(csv.DictReader(f))
        if rows:
            rows[0]["circuit"] = key
            return rows[0]

    row = {field: "" for field in FIELDS}
    row.update(circuit=key, circom_file=circom_file, prime=args.prime,
               status="run_timeout" if error else "no_csv", error=error or "the run did not write its csv")
    return row


def main():
    logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s", handlers=[logging.StreamHandler(sys.stdout)])

    parser = argparse.ArgumentParser(description="Run circom_vs_llzk_equivalence.py concurrently on circom files and combine the results in a csv")
    parser.add_argument("inputs", nargs="+", help="Circom files or directories (searched recursively for files with a main component)")
    parser.add_argument("-out", "--out", type=str, required=False, default="/tmp/avazar_output/circom_vs_llzk", help="Output Path")
    parser.add_argument("-j", "--jobs", type=int, required=False, default=max(1, mp.cpu_count() - 2), help="Number of concurrent runs (defaults to cpu_count - 2)")
    parser.add_argument("-solver", "--solver", type=str, required=False, default="ffsol", help="Solver to be used")
    parser.add_argument("-tout", "--timeout", type=int, required=False, help="Timeout for the solver expressed in miliseconds")
    parser.add_argument("-p", "--prime", type=str, required=False, default="goldilocks", help="Prime number used to generate the circuits")
    parser.add_argument("--run-timeout", type=int, required=False, dest="run_timeout", help="Wall-clock timeout of each run, in seconds")
    parser.add_argument("--csv", type=str, required=False, help="Combined csv file (defaults to <out>/results.csv)")
    parser.add_argument("--checks", type=str, nargs="+", required=False, choices=CHECKS, default=CHECKS, help="Checks to run on both r1cs (defaults to all of them)")

    args = parser.parse_args()
    args.out = os.path.abspath(args.out)
    csv_path = args.csv if args.csv else os.path.join(args.out, "results.csv")
    os.makedirs(args.out, exist_ok=True)

    circuits = collect_circuits(args.inputs)
    logging.info(f"{len(circuits)} circuits, {args.jobs} concurrent runs")

    rows = []
    with mp.Pool(args.jobs) as pool:
        for i, row in enumerate(pool.imap_unordered(run_one, [(key, file, args) for key, file in circuits]), 1):
            logging.info(f"[{i}/{len(circuits)}] {row['circuit']}: {row['status']}")
            rows.append(row)

    rows.sort(key=lambda row: row["circuit"])
    with open(csv_path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=FIELDS, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)

    ok = sum(row["status"] == "ok" for row in rows)
    logging.info(f"{ok}/{len(rows)} runs completed. Results: {csv_path}")


if __name__ == '__main__':
    main()
