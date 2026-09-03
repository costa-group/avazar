"""
Module to produce the JSON with the expected format for signals inside loops
(one different subindex of the form component#i.signal_name). This information
is extracted from smt fields :in-vars-info and :out-vars-info, which contains a mapping
that links every core variable used as an input (output resp.) parameter in a call to the
corresponding smt variable.
"""
import codecs
import json
import re
import warnings
from typing import Dict, Tuple, List, Optional
from copy import deepcopy
from collections import Counter

# Matches one call's annotation triple embedded in an SMT formula string, e.g.:
#   :meta-data "call @Num2Bits_0 (Num2Bits_17_364.in) to Num2Bits_17_364.out"
#   :in-vars-info "{\"Num2Bits_17_364.in\": \"v_32\"}"
#   :out-vars-info "{\"Num2Bits_17_364.out\": [\"v_50\", \"v_51\"]}"
# Each payload is itself JSON-encoded, so -- since `formula` has already been
# JSON-decoded once (by json.load on the whole SMT file) -- its own quotes
# still carry one extra level of "\"" escaping. Hence the quoted-string-with-
# escapes group (?:[^"\\]|\\.)* rather than a plain [^"]*, which would stop
# at the first *escaped* quote instead of the payload's true closing one.
_CALL_ANNOTATION_RE = re.compile(
    r':meta-data\s+"(?P<meta>(?:[^"\\]|\\.)*)"'
    r'\s*:in-vars-info\s+"(?P<in_vars>(?:[^"\\]|\\.)*)"'
    r'\s*:out-vars-info\s+"(?P<out_vars>(?:[^"\\]|\\.)*)"'
)

# metadata shape: "call <callee> (<inputs>) to <outputs>"
_CALL_METADATA_RE = re.compile(r'call\s+\S+\s*\((?P<inputs>[^)]*)\)\s*to\s+(?P<outputs>.*)')


def _decode_json_payload(raw: str) -> Dict:
    """
    Decodes one :in-vars-info/:out-vars-info payload into a real dict.
    `raw` is the payload's text *without* its surrounding quotes -- its own
    embedded quotes are still one level escaped (e.g. {\"a\": \"v_0\"}),
    which codecs.decode(..., "unicode_escape") unescapes, leaving plain,
    directly loadable JSON text.
    """
    return json.loads(codecs.decode(raw, "unicode_escape"))


def extract_vars_info_from_concrete_call(call_formula: str) -> Tuple[Dict[str, str], Dict[str, str], str]:
    """
    Given a string containing a formula that represents a concrete call
    (e.g. (! (foo v_0 v_2 v_3) :meta-data "call foo (%x) to %z" :in-vars-info "{\"%x\": \"v_5\"}" :out-vars-info "{"%x": "v_5"}") ),
    extracts two dicts (one with :in-vars-info and the other one with :out-vars-info)
    and the :meta-data
    """
    # To produce the in-vars-info and out-vars-info, use
    # raw_dict = codecs.decode(raw_str, "unicode_escape").strip('"')
    # json.loads(raw_dict) (it should work)
    match = _CALL_ANNOTATION_RE.search(call_formula)
    if not match:
        raise ValueError(f"Not a recognizable call annotation: {call_formula!r}")

    in_vars_info = _decode_json_payload(match["in_vars"])
    out_vars_info = _decode_json_payload(match["out_vars"])
    return in_vars_info, out_vars_info, match["meta"]


def extract_calls(smt_formula: str) -> List[str]:
    """
    Given a string that represents a complete formula, with possible multiple subformulas nested,
    extracts all formulas that contain a :meta-data with "call ...".
    """
    # Alternatively, it can filter just those subformulas with :in-vars-info and :out-vars-info
    return [
        match.group(0)
        for match in _CALL_ANNOTATION_RE.finditer(smt_formula)
        if match["meta"].startswith("call ")
    ]


def extract_component(metadata: str) -> Optional[str]:
    """
    Given the metadata from a call (e.g. "call @Num2Bits_0 (Num2Bits_17_364.in) to Num2Bits_17_364.out"),
    extracts the name of the invoked component (e.g. "Num2Bits_17_364").
    """
    # There must be either and input or output signal to extract the name from. If not,
    # just raise a warning and return None. Same if the inputs or outputs are just a name with no "."
    # in between
    match = _CALL_METADATA_RE.fullmatch(metadata.strip())
    if not match:
        warnings.warn(f"Could not parse call metadata: {metadata!r}")
        return None

    candidates = match["inputs"].split(",") + match["outputs"].split(",")
    for candidate in candidates:
        candidate = candidate.strip()
        if "." in candidate:
            return candidate.split(".", 1)[0]

    # No need for warning, as non-component array calls
    # warnings.warn(f"No component.signal-shaped input/output found in call metadata: {metadata!r}")
    return None


def process_components(smt_json: Dict) -> Dict:
    """
    Given a JSON containing multiple components with smt formula, adds to the mapping of variables
    (vars_info) a distinct name for each core variable in each iteration, following the convention
    described above.

    A component's real array index (for an array-of-components member left
    at its bare name -- no single compile-time-known instance, see
    struct.py's array-component index-sequence pre-pass) is looked up from
    "components_index_sequences" -- the translator's own static analysis of
    the population loop's actual traversal order, keyed by the occurrence
    number (0-indexed) at which a given component_name is seen in this
    macro's own call trace. This generalizes the previous behavior (which
    just used that same occurrence number directly as a single "#i" index)
    to any array dimensionality and any traversal order -- a flat "#i" is
    both the wrong shape for an N-D member (its own "components_info" keys
    are "member#i1#i2..."-shaped) and wrong for any population order other
    than simple sequential 0,1,2,... visitation. A component with no
    registered sequence (its population loop's own bound wasn't statically
    resolvable) falls back to that original flat-counter behavior.
    """
    extended_smt_json = deepcopy(smt_json)
    for macro_name, current_macro in smt_json["macros"].items():
        current_formula = current_macro["formula"]

        calls = extract_calls(current_formula)
        components = current_macro.get("components_info", {})
        index_sequences = current_macro.get("components_index_sequences", {})

        # Dict that counts the current occurrence for each of the traversed components so far
        component2iteration = Counter()

        for call in calls:
            # First we extract the information from the formula
            in_vars_info, out_vars_info, metadata = extract_vars_info_from_concrete_call(call)

            component_name = extract_component(metadata)
            if component_name is None:
                continue

            occurrence = component2iteration[component_name]
            component2iteration[component_name] += 1

            sequence = index_sequences.get(component_name)
            if sequence is not None:
                if occurrence >= len(sequence):
                    # More calls observed in the trace than the static
                    # analysis predicted for this component -- skip rather
                    # than guess (same "don't rename what we can't
                    # confidently attribute" philosophy as decision 20).
                    continue
                component_iteration = component_name + "".join(f"#{i}" for i in sequence[occurrence])
            else:
                component_iteration = f"{component_name}#{occurrence}"

            # We only need to handle arrays of components, as other signals
            # are already processed in the mapping dict. This already appear in the components
            # dict passed as an argument
            if component_iteration in components:

                # In vars and out vars are handled equally
                for core_var, smt_var in dict(**in_vars_info, **out_vars_info).items():
                    # Here, core args must be of the form component.signal_name
                    # Hence, we can just remove the prefix "component."
                    if not core_var.startswith(f"{component_name}."):
                        continue
                    signal_name = core_var[len(component_name) + 1:]
                    new_signal_name = f"{component_iteration}.{signal_name}"
                    extended_smt_json["macros"][macro_name]["vars_info"][new_signal_name] = smt_var

    return extended_smt_json
