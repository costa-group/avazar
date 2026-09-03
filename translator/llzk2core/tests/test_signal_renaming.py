import pytest

from execution.signal_renaming import (
    extract_calls,
    extract_component,
    extract_vars_info_from_concrete_call,
    process_components,
)

# The four fragments below are the *exact* text extract_calls() returns when
# run against the real, generated `ternary_two_calls_concrete.json` (built
# from tests/aux_files/ternary_two_calls_concrete.mlir -- Num2Ternary(2),
# which calls Num2Bits(2) twice per iteration of a 2-iteration loop, once for
# each of two array-of-components members Num2Bits_17_364/Num2Bits_18_416).
# Captured directly from that file rather than hand-written, so the
# escaping/decoding tests below are grounded in what llzk_cli actually emits.
CALL_17_364_ITER0 = (
    ':meta-data "call @Num2Bits_0 (Num2Bits_17_364.in) to Num2Bits_17_364.out" '
    ':in-vars-info "{\\"Num2Bits_17_364.in\\": \\"v_32\\"}" '
    ':out-vars-info "{\\"Num2Bits_17_364.out\\": [\\"v_50\\", \\"v_51\\"]}"'
)
CALL_18_416_ITER0 = (
    ':meta-data "call @Num2Bits_0 (Num2Bits_18_416.in) to Num2Bits_18_416.out" '
    ':in-vars-info "{\\"Num2Bits_18_416.in\\": \\"v_32\\"}" '
    ':out-vars-info "{\\"Num2Bits_18_416.out\\": [\\"v_144\\", \\"v_145\\"]}"'
)
CALL_17_364_ITER1 = (
    ':meta-data "call @Num2Bits_0 (Num2Bits_17_364.in) to Num2Bits_17_364.out" '
    ':in-vars-info "{\\"Num2Bits_17_364.in\\": \\"v_241\\"}" '
    ':out-vars-info "{\\"Num2Bits_17_364.out\\": [\\"v_259\\", \\"v_260\\"]}"'
)
CALL_18_416_ITER1 = (
    ':meta-data "call @Num2Bits_0 (Num2Bits_18_416.in) to Num2Bits_18_416.out" '
    ':in-vars-info "{\\"Num2Bits_18_416.in\\": \\"v_241\\"}" '
    ':out-vars-info "{\\"Num2Bits_18_416.out\\": [\\"v_353\\", \\"v_354\\"]}"'
)


class TestSignalRenaming:

    # ── extract_calls ────────────────────────────────────────────────────────

    def test_extract_calls_empty_formula(self):
        assert extract_calls("(and true true)") == []

    def test_extract_calls_single(self):
        formula = f"(and (! (@Num2Bits_0 v_1) {CALL_17_364_ITER0}) true)"
        assert extract_calls(formula) == [CALL_17_364_ITER0]

    def test_extract_calls_multiple_in_document_order(self):
        # Mirrors the real formula: two components, each called once per
        # loop iteration, interleaved in source order.
        formula = (
            f"(and (! (@Num2Bits_0 v_1) {CALL_17_364_ITER0}) "
            f"(and (! (@Num2Bits_0 v_2) {CALL_18_416_ITER0}) "
            f"(and (! (@Num2Bits_0 v_3) {CALL_17_364_ITER1}) "
            f"(! (@Num2Bits_0 v_4) {CALL_18_416_ITER1}))))"
        )
        assert extract_calls(formula) == [
            CALL_17_364_ITER0, CALL_18_416_ITER0, CALL_17_364_ITER1, CALL_18_416_ITER1,
        ]

    def test_extract_calls_ignores_non_call_metadata(self):
        # A :meta-data annotation that isn't a call (even one that happens to
        # carry the same :in-vars-info/:out-vars-info shape) must not match.
        formula = (
            '(! (= v_1 v_2) :meta-data "assign %x" '
            ':in-vars-info "{}" :out-vars-info "{}")'
        )
        assert extract_calls(formula) == []

    # ── extract_vars_info_from_concrete_call ─────────────────────────────────

    def test_extract_vars_info_from_concrete_call_scalar_and_array_out(self):
        in_vars, out_vars, metadata = extract_vars_info_from_concrete_call(CALL_17_364_ITER0)
        assert in_vars == {"Num2Bits_17_364.in": "v_32"}
        assert out_vars == {"Num2Bits_17_364.out": ["v_50", "v_51"]}
        assert metadata == "call @Num2Bits_0 (Num2Bits_17_364.in) to Num2Bits_17_364.out"

    def test_extract_vars_info_from_concrete_call_second_iteration(self):
        in_vars, out_vars, metadata = extract_vars_info_from_concrete_call(CALL_18_416_ITER1)
        assert in_vars == {"Num2Bits_18_416.in": "v_241"}
        assert out_vars == {"Num2Bits_18_416.out": ["v_353", "v_354"]}

    def test_extract_vars_info_from_concrete_call_not_a_call_raises(self):
        with pytest.raises(ValueError):
            extract_vars_info_from_concrete_call("(and true true)")

    # ── extract_component ────────────────────────────────────────────────────

    def test_extract_component_from_dotted_input(self):
        assert extract_component(
            "call @Num2Bits_0 (Num2Bits_17_364.in) to Num2Bits_17_364.out"
        ) == "Num2Bits_17_364"

    def test_extract_component_from_dotted_output_only(self):
        assert extract_component("call @Foo (%x) to Bar.out") == "Bar"

    def test_extract_component_multiple_outputs_first_dotted_wins(self):
        assert extract_component("call @Foo (%x) to Bar.out, Bar.out2") == "Bar"

    def test_extract_component_no_dot_anywhere_warns_and_returns_none(self):
        result = extract_component("call @Num2Ternary_1 (%arg0) to out, out2")
        assert result is None, f"Result: {result}"

    def test_extract_component_unparseable_metadata_warns_and_returns_none(self):
        with pytest.warns(UserWarning):
            result = extract_component("not a call at all")
        assert result is None

    # ── process_components ───────────────────────────────────────────────────

    def _num2ternary_smt_json(self):
        """
        A trimmed-but-real fixture: the actual components_info produced for
        @Num2Ternary_1 in ternary_two_calls_concrete.json (see
        tests/aux_files/ternary_two_calls_concrete.mlir), and a formula built
        from the four real call fragments above -- not the full ~50KB real
        formula, which is almost entirely unrelated SMT clauses, but not
        fabricated data either.
        """
        formula = (
            f"(and (! (@Num2Bits_0 v_1) {CALL_17_364_ITER0}) "
            f"(and (! (@Num2Bits_0 v_2) {CALL_18_416_ITER0}) "
            f"(and (! (@Num2Bits_0 v_3) {CALL_17_364_ITER1}) "
            f"(! (@Num2Bits_0 v_4) {CALL_18_416_ITER1}))))"
        )
        return {
            "macros": {
                "@Num2Ternary_1": {
                    "formula": formula,
                    "components_info": {
                        "Num2Bits_18_416#0": "@Num2Bits_0",
                        "Num2Bits_18_416#1": "@Num2Bits_0",
                        "Num2Bits_17_364#0": "@Num2Bits_0",
                        "Num2Bits_17_364#1": "@Num2Bits_0",
                    },
                    "vars_info": {
                        # Pre-existing, flat, last-iteration-wins entries --
                        # must survive untouched (renaming is additive).
                        "Num2Bits_18_416.in": "v_241",
                        "Num2Bits_18_416.out": ["v_353", "v_354"],
                        "Num2Bits_17_364.in": "v_241",
                        "Num2Bits_17_364.out": ["v_259", "v_260"],
                    },
                },
            },
        }

    def test_process_components_adds_indexed_entries_for_array_of_components(self):
        smt_json = self._num2ternary_smt_json()
        result = process_components(smt_json)
        vars_info = result["macros"]["@Num2Ternary_1"]["vars_info"]

        assert vars_info["Num2Bits_17_364#0.in"] == "v_32"
        assert vars_info["Num2Bits_17_364#0.out"] == ["v_50", "v_51"]
        assert vars_info["Num2Bits_17_364#1.in"] == "v_241"
        assert vars_info["Num2Bits_17_364#1.out"] == ["v_259", "v_260"]
        assert vars_info["Num2Bits_18_416#0.in"] == "v_32"
        assert vars_info["Num2Bits_18_416#0.out"] == ["v_144", "v_145"]
        assert vars_info["Num2Bits_18_416#1.in"] == "v_241"
        assert vars_info["Num2Bits_18_416#1.out"] == ["v_353", "v_354"]

    def test_process_components_is_additive_not_replacing(self):
        smt_json = self._num2ternary_smt_json()
        result = process_components(smt_json)
        vars_info = result["macros"]["@Num2Ternary_1"]["vars_info"]

        # The original, flat, unindexed entries are untouched.
        assert vars_info["Num2Bits_18_416.in"] == "v_241"
        assert vars_info["Num2Bits_18_416.out"] == ["v_353", "v_354"]
        assert vars_info["Num2Bits_17_364.in"] == "v_241"
        assert vars_info["Num2Bits_17_364.out"] == ["v_259", "v_260"]

    def test_process_components_does_not_mutate_input(self):
        smt_json = self._num2ternary_smt_json()
        before = dict(smt_json["macros"]["@Num2Ternary_1"]["vars_info"])
        process_components(smt_json)
        assert smt_json["macros"]["@Num2Ternary_1"]["vars_info"] == before

    def test_process_components_skips_scalar_subcomponent_calls(self):
        # A scalar (non-array) subcomponent call has no "#i" entry in
        # components_info at all -- its call must be counted (to keep the
        # per-component iteration counter coherent for any array-of-
        # components calls that follow) but must not get a renamed entry,
        # since its existing flat vars_info entry is already unambiguous.
        formula = (
            ':meta-data "call @Num2Bits_0 (last1.in) to last1.out" '
            ':in-vars-info "{\\"last1.in\\": \\"v_9\\"}" '
            ':out-vars-info "{\\"last1.out\\": [\\"v_10\\"]}"'
        )
        smt_json = {
            "macros": {
                "@Foo_1": {
                    "formula": f"(! (@Num2Bits_0 v_9) {formula})",
                    "components_info": {},
                    "vars_info": {"last1.in": "v_9", "last1.out": ["v_10"]},
                },
            },
        }
        result = process_components(smt_json)
        vars_info = result["macros"]["@Foo_1"]["vars_info"]
        assert "last1#0.in" not in vars_info
        assert "last1#0.out" not in vars_info
        assert vars_info == {"last1.in": "v_9", "last1.out": ["v_10"]}

    def test_process_components_no_calls_leaves_macro_untouched(self):
        smt_json = {
            "macros": {
                "main": {
                    "formula": "(and true true)",
                    "components_info": {},
                    "vars_info": {"%x": "v_0"},
                },
            },
        }
        result = process_components(smt_json)
        assert result["macros"]["main"]["vars_info"] == {"%x": "v_0"}

    def test_process_components_real_fixture_end_to_end(self):
        # End-to-end against the actual generated JSON for
        # tests/aux_files/ternary_two_calls_concrete.mlir, not just the
        # trimmed fixture above -- guards against the trimmed fixture ever
        # drifting from what llzk_cli really emits.
        import json
        import os

        fixture_path = os.path.join(
            os.path.dirname(__file__), "aux_files", "ternary_two_calls_concrete.json"
        )
        if not os.path.exists(fixture_path):
            pytest.skip(f"real fixture not present: {fixture_path}")

        with open(fixture_path) as f:
            smt_json = json.load(f)

        result = process_components(smt_json)
        vars_info = result["macros"]["@Num2Ternary_1"]["vars_info"]

        assert vars_info["Num2Bits_17_364#0.in"] == "v_32"
        assert vars_info["Num2Bits_17_364#0.out"] == ["v_50", "v_51"]
        assert vars_info["Num2Bits_17_364#1.in"] == "v_241"
        assert vars_info["Num2Bits_17_364#1.out"] == ["v_259", "v_260"]
        assert vars_info["Num2Bits_18_416#0.in"] == "v_32"
        assert vars_info["Num2Bits_18_416#0.out"] == ["v_144", "v_145"]
        assert vars_info["Num2Bits_18_416#1.in"] == "v_241"
        assert vars_info["Num2Bits_18_416#1.out"] == ["v_353", "v_354"]

    # ── process_components — components_index_sequences (N-D / arbitrary order) ──

    def _sigmaf_smt_json(self):
        """
        A trimmed, N-D fixture mirroring poseidon3_test_concrete.mlir's
        real "@sigmaF" (!array.type<8,3 x !struct.type<@Sigma_1::...>>,
        populated inside a genuinely symbolic loop): two calls, each
        attributable to a real (i, j) pair via components_index_sequences
        rather than a flat per-call counter. The exact shape (call/vars
        format, "sigmaF#0#0"-keyed components_info) is confirmed end-to-end
        against real llzk_cli output for poseidon3_test_concrete.mlir --
        see PROGRESS.md.
        """
        call0 = (
            ':meta-data "call @Sigma_1 (sigmaF.in) to sigmaF.out" '
            ':in-vars-info "{\\"sigmaF.in\\": \\"v_1\\"}" '
            ':out-vars-info "{\\"sigmaF.out\\": \\"v_2\\"}"'
        )
        call1 = (
            ':meta-data "call @Sigma_1 (sigmaF.in) to sigmaF.out" '
            ':in-vars-info "{\\"sigmaF.in\\": \\"v_3\\"}" '
            ':out-vars-info "{\\"sigmaF.out\\": \\"v_4\\"}"'
        )
        formula = f"(and (! (@Sigma_1 v_1) {call0}) (! (@Sigma_1 v_3) {call1}))"
        return {
            "macros": {
                "@PoseidonEx_69": {
                    "formula": formula,
                    "components_info": {
                        "sigmaF#0#0": "@Sigma_1",
                        "sigmaF#0#1": "@Sigma_1",
                    },
                    "components_index_sequences": {
                        "sigmaF": [[0, 0], [0, 1]],
                    },
                    "vars_info": {},
                },
            },
        }

    def test_nd_sequence_used_to_build_component_iteration(self):
        # The core fix: a flat "#i" counter can never match an N-D
        # component_info key -- the real (i, j) pair from
        # components_index_sequences is what makes this resolve at all.
        smt_json = self._sigmaf_smt_json()
        result = process_components(smt_json)
        vars_info = result["macros"]["@PoseidonEx_69"]["vars_info"]

        assert vars_info["sigmaF#0#0.in"] == "v_1"
        assert vars_info["sigmaF#0#0.out"] == "v_2"
        assert vars_info["sigmaF#0#1.in"] == "v_3"
        assert vars_info["sigmaF#0#1.out"] == "v_4"

    def test_no_registered_sequence_falls_back_to_flat_counter(self):
        # A component_name absent from components_index_sequences entirely
        # (an older JSON without the field, or a member whose population
        # loop's own bound wasn't statically resolvable) keeps the
        # original flat "#i" behavior -- not a regression for that case.
        smt_json = self._sigmaf_smt_json()
        del smt_json["macros"]["@PoseidonEx_69"]["components_index_sequences"]
        smt_json["macros"]["@PoseidonEx_69"]["components_info"] = {
            "sigmaF#0": "@Sigma_1",
            "sigmaF#1": "@Sigma_1",
        }
        result = process_components(smt_json)
        vars_info = result["macros"]["@PoseidonEx_69"]["vars_info"]

        assert vars_info["sigmaF#0.in"] == "v_1"
        assert vars_info["sigmaF#0.out"] == "v_2"
        assert vars_info["sigmaF#1.in"] == "v_3"
        assert vars_info["sigmaF#1.out"] == "v_4"

    def test_more_calls_observed_than_sequence_length_skips_extra(self):
        # The static analysis predicted only ONE occurrence, but the trace
        # has two calls -- the second is skipped rather than guessed at
        # (same "don't rename what we can't confidently attribute"
        # philosophy as decision 20), and does not corrupt the first.
        smt_json = self._sigmaf_smt_json()
        smt_json["macros"]["@PoseidonEx_69"]["components_index_sequences"]["sigmaF"] = [[0, 0]]
        result = process_components(smt_json)
        vars_info = result["macros"]["@PoseidonEx_69"]["vars_info"]

        assert vars_info["sigmaF#0#0.in"] == "v_1"
        assert vars_info["sigmaF#0#0.out"] == "v_2"
        assert "sigmaF#0#1.in" not in vars_info
        assert "sigmaF#0#1.out" not in vars_info

    def test_missing_components_index_sequences_field_is_backward_compatible(self):
        # An older-shaped JSON with no "components_index_sequences" key at
        # all (not even an empty dict) must not raise -- falls back to the
        # flat counter for every component, same as before this feature.
        smt_json = self._num2ternary_smt_json()
        assert "components_index_sequences" not in smt_json["macros"]["@Num2Ternary_1"]
        result = process_components(smt_json)
        vars_info = result["macros"]["@Num2Ternary_1"]["vars_info"]
        assert vars_info["Num2Bits_17_364#0.in"] == "v_32"
