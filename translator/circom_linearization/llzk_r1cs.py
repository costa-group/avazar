"""Bridge between `llzk-translate --llzk-to-r1cs --llzk-layout-map` and the
`_signals.json` the rest of the pipeline expects from circom: the .llzk-layout
as signal name -> wire, with names in circom's notation. Also a reader for the
binary .r1cs it generates.
"""

import json
import re
import struct


def parse_r1cs(path):
    """Header fields and constraints of a binary .r1cs (iden3 format, as written
    by circom and by llzk-translate --llzk-to-r1cs). Each constraint is [A, B, C],
    each one a {wire: coefficient} dict, meaning A * B = C."""
    with open(path, "rb") as f:
        data = f.read()
    if data[:4] != b"r1cs":
        raise ValueError(f"{path} is not an r1cs file")
    n_sections = struct.unpack_from("<I", data, 8)[0]
    offset, sections = 12, {}
    for _ in range(n_sections):
        section_type, size = struct.unpack_from("<IQ", data, offset)
        offset += 12
        sections[section_type] = data[offset:offset + size]
        offset += size

    header = sections[1]
    field_size = struct.unpack_from("<I", header, 0)[0]
    prime = int.from_bytes(header[4:4 + field_size], "little")
    n_wires, n_pub_out, n_pub_in, n_prv_in, n_labels, n_constraints = struct.unpack_from("<IIIIQI", header, 4 + field_size)

    body, pos, constraints = sections[2], 0, []
    for _ in range(n_constraints):
        lcs = []
        for _ in range(3):
            n_terms = struct.unpack_from("<I", body, pos)[0]
            pos += 4
            lc = {}
            for _ in range(n_terms):
                wire = struct.unpack_from("<I", body, pos)[0]
                pos += 4
                lc[wire] = int.from_bytes(body[pos:pos + field_size], "little")
                pos += field_size
            lcs.append(lc)
        constraints.append(lcs)

    info = dict(prime=prime, n_wires=n_wires, n_pub_out=n_pub_out, n_pub_in=n_pub_in,
                n_prv_in=n_prv_in, n_labels=n_labels, n_constraints=n_constraints)
    return info, constraints


def normalize_llzk_path(path):
    """main["isz$inputs"]["in"][0] -> main.isz.in[0]; arg["in"][0] -> main.in[0];
    main["ark"]["idx_3"]["out"] -> main.ark[3].out (heterogeneous component arrays
    are emitted by circom-llzk as a pod with one idx_N member per element)."""
    path = re.sub(r'^arg(?=\[)', "main", path)
    path = re.sub(r'\["([^"]+)"\]', r'.\1', path)
    path = path.replace("$inputs", "")
    return re.sub(r'\.idx_(\d+)', r'[\1]', path)


def parse_layout(path):
    """{wire: circom-style signal name} for every wire but the constant one."""
    signals, wires = {}, {}
    with open(path) as f:
        for line in f:
            line = line.rstrip("\n")
            if line.startswith("signal "):
                signal_id, signal_path = line[len("signal "):].split("\t")
                signals[int(signal_id)] = signal_path
            elif line.startswith("wire "):
                wire, target = line[len("wire "):].split("\t")
                if target != "<one>":
                    wires[int(wire)] = normalize_llzk_path(signals[int(target.split()[1])])
    return wires


def _natural_key(name):
    return [int(tok) if tok.isdigit() else tok for tok in re.split(r'(\d+)', name)]


def layout_to_signals(layout_path, signals_path):
    """Write the layout as a `_signals.json`. Keys go in natural order: the
    linearization numbers repeated names by order of appearance, and llzk's wire
    order is not circom's, while natural order matches circom's within each array."""
    wires = parse_layout(layout_path)
    names = {name: wire for wire, name in wires.items()}
    if len(names) != len(wires):
        raise ValueError(f"{layout_path}: two wires normalize to the same signal name")
    ordered = {name: names[name] for name in sorted(names, key=_natural_key)}
    with open(signals_path, "w") as f:
        json.dump(ordered, f, indent=2)
    return ordered
