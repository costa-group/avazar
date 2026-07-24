import json
import os
import re
import sys


def transform_component_names(data: dict) -> dict:
    counters = {}

    pattern = re.compile(r"^(?P<base>.*?)(?P<indices>(\[\d+\])+)$")

    nodes = data.get("nodes", [])

    for node in nodes:
        component_name = node.get("component_name", "")

        if not component_name:
            continue

        match = pattern.match(component_name)

        if match:
            base_key = match.group("base")

            if base_key not in counters:
                counters[base_key] = 0

            node["component_name"] = f"{base_key}#{counters[base_key]}"
            counters[base_key] += 1
        else:
            node["component_name"] = re.sub(r"\[(\d+)\]", r"#\1", component_name)

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

