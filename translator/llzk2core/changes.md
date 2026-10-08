# Changes — Session Notes

Four bugs were identified and fixed in this session. Each section names the
problem, the root cause, and the resolution.

---

## 1. SCF while: component references not renamed (`%2#1` → `%2_aft#1`)

**Symptom.**  Inside `scf.while` bodies, when an SSA variable `%2` was renamed
to `%2_aft` (because the same name was already used in the preceding region),
a `scf.yield` operand written as `%2#1` (component index 1 of the multi-result
var) was left unchanged and did not become `%2_aft#1`.

**Root cause.**  `Operation.update_variables` checked `operand.name in rename`.
The stored operand name was the literal string `"%2#1"`, which is not a key in
the rename dict (only `"%2"` is).  Component-reference names were therefore
never rewritten.

**Fix.** Added a helper `_apply_rename(name, rename)` in `src/llzk_dialects/core.py`:

```python
def _apply_rename(name: str, rename: Dict[str, str]) -> str:
    if name in rename:
        return rename[name]
    if '#' in name:
        base, idx = name.rsplit('#', 1)
        if base in rename:
            return rename[base] + '#' + idx
    return name
```

`update_variables` now calls `_apply_rename` for both the result and every
operand instead of doing a direct dict lookup.

---

## 2. `felt.pow`: naive linear chain replaced with fast exponentiation

**Initial implementation.**  `felt.pow %base, %exp` was expanded into a linear
chain of `felt.mul` operations (one per unit of the exponent), leading to O(n)
multiplications for exponent n.

**User feedback.**  For `exp=4` the optimal expansion is:

```
%r_p1 = felt.mul %base %base   // base²
%r    = felt.mul %r_p1 %r_p1   // (base²)² = base⁴
```

which is 2 multiplications instead of 3.

**Fix.**  Replaced the linear chain with recursive exponentiation by squaring
in `FeltPow.to_core` (`src/llzk_dialects/felt.py`).  A nested generator
`emit(base_, exp_, result_)` handles five cases:

| Condition | Output |
|-----------|--------|
| `exp == 0` | `result = 1` |
| `exp == 1` | `result = base` |
| `exp == 2` | `result = felt.mul base base` |
| even exp   | recurse on `exp//2` to a fresh temp; square the temp |
| odd exp    | recurse on `exp-1` to a fresh temp; multiply temp by base |

A shared mutable counter (`counter = [0]`) generates unique intermediate
variable names (`%r_p1`, `%r_p2`, …) without needing to pre-compute tree depth.

The `exp == 2` base case is critical: without it, recursing on `exp-1 == 1`
and then squaring would emit an unnecessary `%r_p = base` assignment before the
final `felt.mul`.

`FeltPow` extends `FeltBinary`, overriding only `_OPS` and `to_core`.
`FeltPow` is registered in `FeltDialect` before `FeltBinary` so the more
specific class wins the dispatch.

---

## 3. Sibling `scf.if` branches: wrong component member name on first call

**Symptom.**  In `struct BinSub`, the `@compute` function contains two sibling
`scf.if` branches.  Both branches call `Num2Bits` and store the result into a
component pod — one into `n2ba`, the other into `n2bb`.  The generated Core
output labelled the *first* call's outputs as `n2bb.out` instead of `n2ba.out`.

**Root cause.**  `_build_component_naming_maps` (in `struct.py`) populated a
flat dict `struct_result_to_member` keyed by SSA variable name.  Both `scf.if`
branches defined `%16` as the call result (valid in LLZK/MLIR — SSA names are
scoped to their enclosing block).  The pre-pass ran through the first branch
(recording `{"%16": "n2ba"}`), then the second (overwriting to
`{"%16": "n2bb"}`).  When `FunctionCall.to_core` looked up `result.name` in
the dict, both calls found `"n2bb"`.

**Fix.**  Replaced the flat dict with per-object annotation:

1. Removed `struct_result_to_member` from `TranslationContext`.
2. Added `self._member_hint: Optional[str] = None` to `FunctionCall.__init__`.
3. Added `_annotate_function_calls(ops, pod_to_member)` to `struct.py`.  This
   function builds a *per-body* SSA def-map (`{ssa_name: op}`) at each nesting
   level, so sibling branches that reuse the same SSA name produce distinct
   Python object keys and are never confused:

   ```python
   def _annotate_function_calls(ops, pod_to_member):
       def_map = {}
       for op in ops:
           if op.result is not None:
               def_map[op.result.name] = op
       for op in ops:
           if isinstance(op, PodWrite) and op.record_name.name == "@comp":
               member = pod_to_member.get(op.pod_ref.name)
               if member is not None:
                   defining_op = def_map.get(op.value.name)
                   if isinstance(defining_op, FunctionCall):
                       defining_op._member_hint = member
           elif isinstance(op, PodNew) and "@comp" in op.init_records:
               ...  # analogous for pod.new
           for attr in ('body', 'then_body', 'else_body', 'before_body', 'after_body'):
               sub = getattr(op, attr, None)
               if sub:
                   _annotate_function_calls(sub, pod_to_member)
   ```

4. `FunctionCall.to_core` now reads `self._member_hint` instead of querying the
   old dict.

The annotation is identity-based (each `FunctionCall` Python object carries its
own hint), so the SSA-name collision between sibling branches is structurally
impossible.

---

## 4. `FunctionCall.result` property missing — annotation silently failed

**Symptom.**  After implementing `_annotate_function_calls`, all `_member_hint`
fields remained `None` — the annotation never fired.

**Root cause.**  The pre-pass builds a def-map with:

```python
if op.result is not None:
    def_map[op.result.name] = op
```

`FunctionCall` did not override the `result` property.  The base class
`Operation.result` returns `None` unconditionally.  Therefore no `FunctionCall`
was ever inserted into the def-map, and the subsequent look-up
`def_map.get(op.value.name)` always returned `None`.

**Fix.**  Added a `result` property to `FunctionCall`:

```python
@property
def result(self) -> Optional[SSAVar]:
    return self.results[0] if self.results else None
```

This is consistent with how all other `Operation` subclasses expose their
single result and makes `FunctionCall` visible to any code that iterates ops
and checks `op.result`.

---

## Files changed

| File | Change |
|------|--------|
| `src/llzk_dialects/core.py` | Added `_apply_rename`; `update_variables` uses it; removed `struct_result_to_member` from `TranslationContext` |
| `src/llzk_dialects/felt.py` | Removed `felt.pow` from `FeltBinary._OPS`; added `FeltPow` subclass with fast-exp `to_core`; registered `FeltPow` before `FeltBinary` in `FeltDialect` |
| `src/llzk_dialects/function.py` | Added `result` property and `_member_hint` field to `FunctionCall`; `to_core` reads `self._member_hint`; removed debug `print` |
| `src/llzk_dialects/struct.py` | Added `_annotate_function_calls`; `_build_component_naming_maps` calls it; removed dead `_collect_all_ops`; removed `struct_result_to_member.clear()` from `StructDef.to_core` |
| `tests/test_function_parse.py` | Added `test_call_result_property_single`, `test_call_result_property_no_result`, `test_call_member_hint_initially_none` |
| `tests/test_struct_parse.py` | Added `TestAnnotateFunctionCalls` with 8 tests covering flat bodies, `pod.new` path, sibling-if regression, nested-if, multiple pods, and missing defining call |

---

# Session — Remove loop unrolling entirely

Subcomponent/signal naming is now resolved afterwards by `llzk_cli`, not by
this translator (the `-ru` flag removal in commit `5a3e46a`, "Remove -ru
flag to avoid missing signal names," was the first, already-landed piece).
`scf.for`/`scf.while` go back to translating their body as one generic
iteration only, while still correctly determining the bounded number of
iterations. See `PROGRESS.md` §29 and `DECISIONS.md` decision 19 for the
full write-up; summarized here per this file's own convention.

## 1. `_contains_function_call`-driven unroll-vs-repeat decision removed

**Symptom / motivation.** `SCFFor`/`SCFWhile` used to branch: a loop body
with no `function.call` translated as a single generic `repeat N { ... }`
block; a body containing a call was instead unrolled into N literal
per-iteration Python-side copies, so each copy's subcomponent could be
named `"base#0"`, `"base#1"`, etc. That per-iteration naming is no longer
this translator's job.

**Fix.** Deleted `_contains_function_call` entirely. `SCFFor.to_core`/
`SCFWhile.to_core` now always take what used to be the "no call" branch.
`SCFWhile.to_core`'s `if needs_unroll: raise NotImplementedError(...)`
guard (for a body containing a call whose bound is a `SymbolicSteps`
expression) is gone too — a symbolic bound now always drives
`repeat %steps_N { ... }`, regardless of whether the body contains a call.
This incidentally fixed a real, previously-blocked file:
`escalarmulw4table_concrete.mlir` (and its `_test`/`_test3` variants) now
translate to completion.

## 2. `ctx.unroll_index` / `LoopIndexedName` removed

**Symptom / motivation.** `TranslationContext.unroll_index` and the
`LoopIndexedName` dataclass existed solely to resolve a component's name
to `"base#i"` while translating one unrolled copy of a loop, or the bare
`"base"` otherwise. With no loop ever unrolled, `ctx.unroll_index` is
always `None`, and `LoopIndexedName(base).resolve(None)` already, today,
degrades to the bare `base` string.

**Fix.** Deleted `LoopIndexedName` and `TranslationContext.unroll_index`.
`ArrayRead._semantic_base`/`FunctionCall._member_hint` are now always
`Optional[str]` (previously `Optional[Union[str, LoopIndexedName]]`); their
resolution in `ArrayRead.to_core`/`FunctionCall.to_core` dropped the
`isinstance(x, LoopIndexedName): x.resolve(ctx.unroll_index)` branch. In
`struct.py`, the two producers of a `LoopIndexedName` for a non-constant
array index (`_annotate_array_component_reads`,
`_annotate_input_array_reads`) now just use the bare base-name string
directly — the *rest* of these functions, and the naming pre-passes around
them (`_fold_index_constants`, `_find_array_component_bases`,
`_annotate_function_calls`, the `while_iter_args`/`trace_source` block-arg
aliasing), are unchanged: they determine whether a *source-level* array
index is a compile-time constant, a question independent of whether this
translator ever unrolls a loop. This is a pure code simplification with
zero output change, not a naming-behavior change.

## 3. Memoization added alongside the immediately preceding session's fix
   removed as dead weight

**Symptom / motivation.** `SCFWhile._structural_analysis`/
`_cached_structural_analysis` (plus `SCFFor._contains_call`/
`SCFWhile._needs_unroll`) were added to avoid redoing purely-structural
work on every outer-loop iteration during unrolling. With no loop ever
unrolling, `_extract_step` runs at most once per instance regardless, so
the caching has no remaining purpose.

**Fix.** Folded `_structural_analysis`'s body back into a plain, uncached
`_extract_step`, matching its pre-memoization shape. Deleted the
now-unused `_contains_call`/`_needs_unroll` fields.

## What was explicitly NOT touched

The constant-folding work from the immediately preceding session
(`FeltBinary`/`FeltUnary`/`BoolCmp`/`BoolBinary`/`BoolNot` folding into
`ctx.var2const`, and the `SCFIf.to_core` branch-value bug fix) stays as-is
— neither is "unrolling complexity": the `SCFIf` fix corrects an
independent, pre-existing correctness bug, and the folding is a generically
useful improvement (confirmed, via the regression sweep below, to have
already fixed a genuine silent bug in `escalarmulany_test_concrete.mlir`
in the preceding session).

## Verification

Full pytest suite: 423 tests, down from 433 (deletions/replacements of
now-inapplicable unroll-decision and `LoopIndexedName` coverage). Full
sweep of every `circomlib_examples/*.mlir` file (49 of 50 — `poseidonex`
previously timed out under the sweep script's own budget and now
completes well within it): **zero regressions** — every file that
previously translated successfully still does, generally with
substantially more compact output (e.g. `aliascheck_test_concrete.mlir`:
5562 → 251 generated lines). `escalarmulw4table_concrete.mlir` (+ `_test`/
`_test3`) and `poseidonex_test_concrete.mlir` newly translate to
completion; `escalarmul_min/test/test_min_concrete.mlir` and
`pedersen_test_concrete.mlir` newly progress past their old
`NotImplementedError` into the same pre-existing pod-variable-tracking
`KeyError` already documented for `babypbk_test_concrete.mlir`.

## Files changed

| File | Change |
|------|--------|
| `src/llzk_dialects/scf.py` | Deleted `_contains_function_call`; collapsed `SCFFor.to_core`/`SCFWhile.to_core` to always translate one generic body; removed `SCFFor._contains_call`, `SCFWhile._needs_unroll`, `SCFWhile._structural_analysis`/`_cached_structural_analysis` (folded back into a plain `_extract_step`) |
| `src/llzk_dialects/core.py` | Deleted `LoopIndexedName`; deleted `TranslationContext.unroll_index` |
| `src/llzk_dialects/array.py` | `ArrayRead._semantic_base` is now `Optional[str]`; dropped the `LoopIndexedName`/`ctx.unroll_index` resolution branch in `to_core` |
| `src/llzk_dialects/function.py` | `FunctionCall._member_hint` is now `Optional[str]`; dropped the `LoopIndexedName`/`ctx.unroll_index` resolution branch in `to_core` |
| `src/llzk_dialects/struct.py` | `_annotate_array_component_reads`/`_annotate_input_array_reads` now produce the bare base-name string instead of `LoopIndexedName(base)` for a non-constant index; docstrings updated |
| `tests/test_scf_parse.py` | Deleted the `_contains_function_call` test section and the unroll-specific `to_core` tests; added coverage confirming a call-containing body now translates identically to a call-free one, and that a symbolic-steps while with a call no longer raises |
| `tests/test_array_parse.py` / `tests/test_function_parse.py` | Deleted tests constructing a `LoopIndexedName` and asserting `ctx.unroll_index` resolution; merged into the existing bare-string semantic-naming coverage |
| `tests/test_struct_parse.py` | Updated the two assertions checking `isinstance(x, LoopIndexedName)` / equality against a `LoopIndexedName` instance to compare against the bare string instead |
| `PROGRESS.md` | New §29; removed the now-moot `ctx.unroll_index`/`LoopIndexedName` "Known pre-existing" bullet; marked the `escalarmulw4table` bullet resolved; updated the pod-tracking `KeyError` bullet to list the newly-affected files |
| `DECISIONS.md` | Marked decisions 10-14 and 18 superseded; added decision 19 |

---

# Session — Implement `signal_renaming.py` (per-iteration SMT variable naming)

With loop unrolling removed, a component called N times inside a loop is
now called exactly once, textually, in the `.core` output — `llzk_cli`
disambiguates the N runtime occurrences itself, annotating each concrete
call in its SMT formula with a `:meta-data "call ..."` +
`:in-vars-info "{...}"`/`:out-vars-info "{...}"` triple. This session
completed the previously-stubbed `src/execution/signal_renaming.py`, which
turns that into `vars_info` entries of the form
`"{component}#{i}.{signal}": smt_var`.

## 1. All three extraction helpers implemented

**Symptom / starting point.** `extract_calls`, `extract_component`, and
`extract_vars_info_from_concrete_call` were `pass`-only stubs; the driver
(`process_components`) already had the right shape but called all three.

**Fix.** One shared compiled regex (`_CALL_ANNOTATION_RE`), using the
"quoted string with escapes" idiom `(?:[^"\\]|\\.)*` for each payload
(confirmed necessary against the real formula text — a plain `[^"]*`
would stop at a payload's first *escaped* quote, not its true closing
one). `extract_calls` returns each match's full text, filtered to
meta-data starting with `"call "`. `extract_vars_info_from_concrete_call`
re-applies the same regex to one such fragment and decodes each payload
via `json.loads(codecs.decode(raw, "unicode_escape"))` — no `.strip('"')`
needed, since the capture excludes the payload's surrounding quotes (see
`DECISIONS.md` §20). `extract_component` parses
`"call <callee> (<inputs>) to <outputs>"` and returns the text before the
first `.` in whichever input/output is dotted; warns and returns `None`
otherwise.

## 2. Two indexing bugs fixed in `process_components`

**Symptom.** `current_macro = smt_json[macro_name]` and
`extended_smt_json["macros"]["vars_info"][...]` don't match the real JSON
schema (`macros` is a dict of macro-name → `{params, vars_info, formula,
components_info}`; `vars_info` lives inside each macro, not as a sibling
of `macros`).

**Fix.** `current_macro` now comes from `smt_json["macros"][macro_name]`
(via `.items()`); the new entry is written to
`extended_smt_json["macros"][macro_name]["vars_info"]`. Also: skip a call
outright when `extract_component` returns `None`; replaced the original's
unescaped `re.sub(f"{component_name}\.", "", core_var)` with a
`startswith`-guarded slice (see `DECISIONS.md` §20).

## Verification

`tests/test_signal_renaming.py` (new, replacing a broken 5-line stub):
18 tests — unit tests per function plus two `process_components`
integration tests, one built from a trimmed-but-real fixture (the actual
`components_info` and the 4 real call fragments from
`tests/aux_files/ternary_two_calls_concrete.mlir`'s generated JSON) and
one against that real JSON file directly (copied to
`tests/aux_files/ternary_two_calls_concrete.json`). Full suite: 441
tests, up from 423.

Ran the real end-to-end pipeline live (`src/llzk2core.py`, actually
invoking `lean/llzk_cli`) against `ternary_two_calls_concrete.mlir`,
`ternary_concrete.mlir`, `three_subcomponents_array_concrete.mlir`, and
`mux2_1`/`mux3_1`/`mux4_1_concrete.mlir` — all completed cleanly.
`ternary_two_calls_concrete.mlir`'s `@Num2Ternary_1` macro gained exactly
`Num2Bits_17_364#0.in`/`#0.out`/`#1.in`/`#1.out` and the same for
`Num2Bits_18_416`, matching the target example exactly.
`three_subcomponents_array_concrete.mlir` (compile-time-constant-indexed
component arrays, already uniquely named as `last_0`/`last_1` at the
`.core` level) correctly gained zero new entries — confirming the
"already handled elsewhere" filter works for both shapes, not just the
loop-driven one.

## Files changed

| File | Change |
|------|--------|
| `src/execution/signal_renaming.py` | Implemented `extract_calls`, `extract_component`, `extract_vars_info_from_concrete_call`; fixed two indexing bugs and the unescaped prefix-strip in `process_components` |
| `tests/test_signal_renaming.py` | Replaced the broken stub with `TestSignalRenaming` (18 tests) |
| `tests/aux_files/ternary_two_calls_concrete.json` | New fixture — the real generated JSON for the existing `ternary_two_calls_concrete.mlir` fixture |
| `PROGRESS.md` | New §30 |
| `DECISIONS.md` | New decision 20 |
