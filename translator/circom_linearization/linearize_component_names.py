import json
import os
import re
import sys

from linearize_signal_names import linearize_component_path


def transform_component_names(data: dict) -> dict:
    """Every index of a component name becomes '#i', keeping all of them:
    "sigmaF[0][1]" -> "sigmaF#0#1", which is how llzk2core names the keys of
    components_info."""
    for node in data.get("nodes", []):
        component_name = node.get("component_name", "")
        if component_name:
            node["component_name"] = linearize_component_path(component_name)
    return data


def main(input_file, output_file):

    if not os.path.isfile(input_file):
        print(f"Error: The input file '{input_file}' does not exist.")
        return

    try:
        with open(input_file, "r", encoding="utf-8") as f:
            data = json.load(f)
    except Exception as e:
        print(f"Error al leer el archivo JSON: {e}")
        return

    transformed_data = transform_component_names(data)

    try:
        with open(output_file, "w", encoding="utf-8") as f:
            json.dump(transformed_data, f, indent=2, ensure_ascii=False)
        print(f"Success: file saved in '{output_file}'.")
    except Exception as e:
        print(f"Error: failed translation {e}")



if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else sys.argv[1])
