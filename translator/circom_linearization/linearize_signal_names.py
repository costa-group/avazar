import json
import os
import re
import sys


# A name made of a base and the trailing index group of the signal itself,
# e.g. "main.pEx.sigmaF[0][1].in[2][0]" -> base "main.pEx.sigmaF[0][1].in",
# final indices "[2][0]".
FINAL_PATTERN = re.compile(r"^(?P<base>.*?)(?P<final_indices>(\[\d+\])+)$")
INDEX_GROUP_PATTERN = re.compile(r"(\[\d+\])+")


def _indices(group: str) -> list:
    return [int(i) for i in re.findall(r"\d+", group)]


def linearize_component_path(path: str) -> str:
    """Every index of an (array of) component(s) becomes '#i', keeping all of
    them: "sigmaF[0][1]" -> "sigmaF#0#1". This is how llzk2core names the
    components in components_info, and the prefix of their vars_info keys."""
    return INDEX_GROUP_PATTERN.sub(lambda m: "".join(f"#{i}" for i in _indices(m.group(0))), path)


def transform_and_linearize_all(data: dict) -> dict:
    """Linearize the names of a circom _signals.json:
    - the indices of components ("intermediate" indices) become '#i' each;
    - the indices of the signal itself ("final" indices) become a single
      row-major flat index, since the specification's vars_info keeps every
      signal array flat: "in[1][2]" of a [3][4] array -> "in[6]".
    The dimensions of each signal array are taken from the largest index of
    every dimension among all its elements."""
    parsed = []
    dims = {}

    for key, value in data.items():
        match = FINAL_PATTERN.match(key)
        if match:
            base = linearize_component_path(match.group("base"))
            indices = _indices(match.group("final_indices"))
            known = dims.get(base)
            if known is None:
                dims[base] = [i + 1 for i in indices]
            elif len(known) != len(indices):
                raise ValueError(f"Signal '{base}' is accessed with {len(known)} and {len(indices)} indices")
            else:
                dims[base] = [max(d, i + 1) for d, i in zip(known, indices)]
        else:
            base = linearize_component_path(key)
            indices = None
        parsed.append((base, indices, value))

    result = {}
    for base, indices, value in parsed:
        if indices is None:
            new_key = base
        else:
            flat = 0
            for i, d in zip(indices, dims[base]):
                flat = flat * d + i
            new_key = f"{base}[{flat}]"
        if new_key in result:
            raise ValueError(f"Two signals linearize to the same name '{new_key}'")
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
    main(sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else sys.argv[1])
