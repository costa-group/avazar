import json
import os
import re
import sys


def transform_and_linearize_all(data: dict) -> dict:
    result = {}

    final_counters = {}
    intermediate_counters = {}

    final_pattern = re.compile(r"^(?P<base>.*?)(?P<final_indices>(\[\d+\])+)$")

    bracket_group_pattern = re.compile(r"(\[\d+\])+")

    for key, value in data.items():
        match_final = final_pattern.match(key)
        if match_final:
            base_key = match_final.group("base")
            has_final_indices = True
        else:
            base_key = key
            has_final_indices = False

        def replace_intermediate(match):
            full_group = match.group(0)
            indices = re.findall(r"\d+", full_group)

            prefix_up_to_here = base_key[: match.start()]

            if len(indices) > 1:
                # Multidimensional intermedio -> contador incremental (#0, #1, ...)
                if prefix_up_to_here not in intermediate_counters:
                    intermediate_counters[prefix_up_to_here] = 0

                idx = intermediate_counters[prefix_up_to_here]
                intermediate_counters[prefix_up_to_here] += 1
                return f"#{idx}"
            else:
                # Unidimensional intermedio -> sustituye [N] por #N
                return f"#{indices[0]}"

        transformed_base = bracket_group_pattern.sub(replace_intermediate, base_key)

        if has_final_indices:
            if transformed_base not in final_counters:
                final_counters[transformed_base] = 0

            new_key = f"{transformed_base}[{final_counters[transformed_base]}]"
            final_counters[transformed_base] += 1
        else:
            new_key = transformed_base

        result[new_key] = value

    return result


def main(input_file, output_file):

    if not os.path.isfile(input_file):
        print(f"Error: file '{input_file}' does not exist.")
        return

    try:
        with open(input_file, "r", encoding="utf-8") as f:
            data = json.load(f)
    except Exception as e:
        print(f"Error reading the json: {e}")
        return

    transformed_data = transform_and_linearize_all(data)

    try:
        with open(output_file, "w", encoding="utf-8") as f:
            json.dump(transformed_data, f, indent=2, ensure_ascii=False)
        print(f" SUCCESS: saved in '{output_file}'.")
    except Exception as e:
        print(f"Error saving the file: {e}")


if __name__ == "__main__":
    main()
