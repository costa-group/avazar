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

    #TODO: add option to execute llzk directly instead of reading the file
    
    return parser


def parse_args() -> argparse.Namespace:
    parser = generate_parser()
    parsed_args = parser.parse_args()

    # Generate a default name
    if parsed_args.target is None:
        parsed_args.target = Path(Path(parsed_args.source).name).stem + ".core"

    return parsed_args
