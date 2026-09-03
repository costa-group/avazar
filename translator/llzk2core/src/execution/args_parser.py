"""
Methods for parsing the options to execute grey
"""
import argparse
from pathlib import Path

def generate_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Avazar Project")

    input_options = parser.add_argument_group("Input Options")

    input_options.add_argument("-s", "--source", type=str, help="Local source file name.", required=True,
                               dest="source")

    output_options = parser.add_argument_group("Output Options")

    output_options.add_argument("-o", "--output", type=str, help="Target output file. If not specified, "
                                                                 "it is stored in the file {source}.core",
                                dest="target")

    # Same flag/choices as complete_avazar.py's own --prime, so a caller
    # (e.g. complete_avazar.py itself) can pass its own selection straight
    # through: every compile-time constant fold and while-loop trip-count
    # simulation is done modulo this field's prime (see core_utils.FIELD_PRIMES),
    # so a value that wraps in the real field (e.g. circom's "-1") is
    # simulated correctly instead of drifting off as a raw Python int.
    parser.add_argument("-p", "--prime", type=str, required=False,
                        choices=["bn128", "bls12377", "bls12381", "goldilocks",
                                 "grumpkin", "pallas", "secq256r1", "vesta"],
                        default="goldilocks",
                        help="Finite field the source .llzk targets (must match whatever "
                             "--prime circom-llzk was run with). Defaults to goldilocks.",
                        dest="prime")

    #TODO: add option to execute llzk directly instead of reading the file

    return parser


def parse_args() -> argparse.Namespace:
    parser = generate_parser()
    parsed_args = parser.parse_args()

    # Generate a default name
    if parsed_args.target is None:
        parsed_args.target = Path(Path(parsed_args.source).name).stem + ".core"

    return parsed_args
