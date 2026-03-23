"""
Methods for parsing the options to execute grey
"""
import argparse
import global_params.constants as constants


def generate_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Avazar Project")

    input_options = parser.add_argument_group("Input Options")

    input_options.add_argument("-s", "--source", type=str, help="Local source file name.", required=True)

    #TODO: add option to execute llzk directly instead of reading the file
    
    return parser


def parse_args() -> argparse.Namespace:
    parser = generate_parser()
    parsed_args = parser.parse_args()

    return parsed_args
