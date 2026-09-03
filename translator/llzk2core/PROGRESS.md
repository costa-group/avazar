# Session Progress

Work done in this session on the LLZK → Core translator (`src/llzk_dialects/`,
`src/execution/`). Verified throughout against `ternary_concrete.mlir`,
`mux4_1_concrete.mlir`, `mux2_1_concrete.mlir`,
`three_subcomponents_array_concrete.mlir`, and (partially — see §13-17)
`circomlib_examples/babypbk_test_concrete.mlir` and
`circomlib_examples/escalarmulw4table_concrete.mlir`, plus the existing
pytest suite (348 tests, all passing at the end of the session) and, for
§17, a full sweep of every file under `circomlib_examples/*.mlir` (not just
the pytest suite — see §17 for why that mattered). §19-24 (a later session)
were verified against `circomlib_examples/poseidon3_test_concrete.mlir` and
bring the suite to 389 tests. §27 (a later session still) fixed `global.def`/
`global.read` parsing and translation, verified against a regenerated
`poseidon3_test_concrete.mlir` whose circom-llzk frontend now hoists repeated
round-constant tables into module-level globals (a shape the file didn't
exercise as of §19-26), bringing the suite to 400 tests.

## 1. `array.insert` implementation

`ArrayInsert.to_core` (`array.py`) was a stub. Implemented it: since arrays
are flattened to 1-D, inserting a sub-array is a contiguous run inside the
flattened array. Computes `start`/`length` from the array's shape and the
given (partial) indices, then emits a Core `repeat` loop
(`_emit_container_field_copy`) that copies element-by-element, since Core has
no dedicated partial-array-copy instruction.

Initial version resolved `start` via `ctx.var2const` (a Python-side
constant). Found this was wrong for indices coming from an `scf.while`
loop-carried variable — `ctx.var2const` only reflects a variable's *initial*
value and goes stale once it's reassigned by a non-constant expression, so
every insert silently targeted the same offset. Fixed by generalizing
`_linearise_indices` to accept a partial index set (fewer indices than
dimensions) and always compute the position symbolically, never assuming a
Python-resolvable constant.

## 2. Structure-of-arrays for pod/struct-element arrays

Core only supports `ff` and `arr<N> of ff` — no way to store an array of pod
or struct values directly. Previously, `array.read`/`array.write` on such
arrays only did Python-side bookkeeping keyed by a compile-time-constant
index (`array_pod_entries` / `array_struct_entries`), and no real storage was
ever created (`array.new` was a no-op for these element types). This meant:
non-constant indices silently no-op'd or produced stale data, and the
generic assignment fallback (`array.copy`) referenced arrays that were never
declared.

Replaced with a real structure-of-arrays (SoA) design:

- **`_flatten_container_fields`** (`array.py`) recursively expands a pod or
  struct element type into `(field_path, leaf_type)` pairs — one real
  flattened Core array per leaf. Pod fields come from `_parse_pod_fields`
  (`pod.py`); struct fields come from the struct's own output args
  (`ctx.core_func2args`, resolved via `_struct_out_args`). Recurses through
  nested pod/struct fields; empty pods (`!pod.type<[]>`) contribute nothing.
  A leaf that is itself array-typed (e.g. a struct's `@out: arr<2>` member)
  just multiplies its own size into the per-field array's total length.
- **`ArrayNew`, `ArrayRead`, `ArrayWrite`** all fan out through this
  uniformly now, using real per-field arrays with symbolic (not
  constant-required) indices.
- **`ArrayExtract`** implemented (was `NotImplementedError`) as the
  read-direction counterpart of `ArrayInsert`, sharing the same
  `_emit_container_field_copy` helper.
- **`core_utils.translate_assignment_core_with_ctx`** gained a branch for
  "array of pod/struct" assignment, copying each flattened per-field array
  independently instead of the single (invalid, for these types)
  `array.copy` fallback.
- **`ctx.array_pod_entries` / `ctx.array_struct_entries`** removed —
  superseded entirely by real per-field storage.
- **`PodNew`** now allocates real backing storage (via the same
  `_flatten_container_fields` logic) for struct/pod-typed fields *not* given
  an initial value — not to populate them with real data yet, but so a later
  copy into/out of them (e.g. writing the pod into an array) reads from
  defined storage instead of an undefined variable. (A struct field is often
  only computed later, e.g. once a countdown reaches zero — the fresh
  storage may briefly hold meaningless data, which is fine as long as it's
  *defined*.)

## 3. `scf.for` no longer unrolls

`SCFFor.to_core` (`scf.py`) used to fully unroll in Python: call `to_core` on
the body once per iteration, with body-defined SSA names suffixed
`_it0`/`_it1`/... to avoid collisions. Changed to translate the body once,
wrapped in a Core `repeat N { ... }` block — matching how `scf.while` is
already translated, and matching the request to not unroll for loops. The
induction variable is now explicitly initialized before the loop
(`%iv = {lb}`) and advanced at the end of the body
(`%iv = felt.add %iv {step}`), since Core's `repeat` has no implicit counter
and (per Core's flat per-function variable namespace) the same LLZK name can
be reused as the induction variable of an unrelated loop earlier in the same
function — relying on stale leftover state would be wrong.

One test (`test_scf_parse.py::test_for_to_core_unroll`, renamed
`test_for_to_core_repeat`) updated to match the new output shape.

## 4. Bug fixes found while validating against real files

- **`mux4_1_concrete.mlir` crash (`KeyError` in `pod.read`)**: the new
  "array of pod/struct" assignment branch in `core_utils.py` used a naive
  `"array" in type_.name` substring check. A *plain* (non-array) pod whose
  own fields happen to be arrays (e.g.
  `!pod.type<[@c: !array.type<16 x ff>, ...]>`, as carried by an `scf.while`
  loop variable) was mistaken for an array-of-pod, dropping its
  `ssa2pod_var` registration and causing a later `pod.read` to `KeyError`.
  Fixed by adding `is_array_type` (`utils.py`) — anchored to the start of
  the type string, so it only matches when the type itself is an array,
  not when an array merely appears nested inside it. Same class of bug
  guarded against (with an explicit `assert`, since unexercised) in the new
  `PodNew` storage-allocation code.
- **`FunctionDef` header-parsing bug**: the header regex captured the
  signature as `[^{]*` up to the first `{`. Any function argument with an
  inline attribute dict (`{llzk.pub}`, `{function.arg_name = "..."}`) — which
  `mux4_1_concrete.mlir` uses pervasively — truncated the signature right
  there, silently dropping every argument declared after it. Fixed with a
  bracket-stack scan (`function.py`) that finds the real body-opening brace
  regardless of how many balanced `{...}` groups (attribute dicts, a
  trailing `attributes {...}` clause) appear in the signature first.
- **Empty-pod scalar read (`array.copy` from an undefined variable)**: in
  `ternary_concrete.mlir`, `pod.read` on an empty-pod-typed field (e.g.
  `@params: !pod.type<[]>`) fell through every case in
  `translate_assignment_core_with_ctx` to the generic `array.copy` fallback,
  copying from a source that was never assigned (an empty pod has no leaves
  to populate it). First attempt (a blanket "empty pod → no-op" branch in
  `core_utils.py`) was too broad and broke a real, already-tested chain
  (`subcomponents_simple_concrete.mlir`'s
  `%pod = pod.new : <[]>` → `%pod_0 = pod.new {@params = %pod}` pattern,
  where the existing `ssa2pod_var` propagation already handles it correctly
  because `%pod` was independently registered by its own `pod.new`).
  Reverted that and fixed the actual gap at its source instead: `ArrayRead`
  now explicitly registers an empty-pod-typed field's storage name in
  `ctx.ssa2pod_var` when extracting a pod from an array — something a fresh
  `pod.new` gets "for free" via its own initial-value assignment chain, but
  a pod read out of an array never had.

## 5. `mux2_1_concrete.mlir`: cross-`scf.while` alias collision

`mux2_1_concrete.mlir` failed with `array.copy mux.s_@out %pod_0_@comp_@out`
— `mux.s_@out` was never defined. Root cause: `SCFWhile.parse` (`scf.py`)
renames each `scf.while`'s own body-defined SSA results with a fixed
`_bef`/`_aft` suffix to avoid collisions *within* the loop. But two
**sibling** `scf.while` blocks in the same function each start their body's
SSA numbering from whatever the LLZK compiler assigned — which can overlap
(both defining a `%18`, say) — so both got renamed to the exact same
`%18_aft`, even though they mean completely different things. Since
`ctx.ssa_to_name` is a single dict spanning the whole function, an alias
registered for the first while's `%18_aft` (there, `%18` was
`pod.read %arg3[@s]`, aliased to the semantic name `"mux.s"`) leaked into the
second while's unrelated `%18_aft` (there, a function call's own result).
`translate_assignment_core_with_ctx`'s top-of-function alias resolution
picked up the stale `"mux.s"` alias for the call result, and the `!struct`
branch's recursive naming then produced `"mux.s" + "_@out"` instead of the
correct `member.out_arg` name (`"mux.out"`).

Fixed by tagging `before_rename`/`after_rename`'s suffixes with `cursor` (the
`scf.while`'s own header line — unique per occurrence in the source), so
sibling `scf.while` blocks never produce the same renamed name.

## 6. `function.arg_name` tracking (unused for now)

Recent `.mlir` output annotates input parameters with a
`{function.arg_name = "..."}` attribute (e.g. `%arg0 -> "c"`). Added
`FunctionDef.in_arg_names` (parses this from the same raw signature text
`in_args` already uses) and `ctx.param_arg_names: Dict[str, str]`
(`core.py`), populated in `FunctionDef.to_core`. Not consumed by any
translation logic yet. Caveat: since Core's variable namespace is
per-function but `param_arg_names` is a single dict spanning the whole
translation, and SSA parameter names like `%arg0` are reused across
different functions, later functions' entries overwrite earlier ones for
the same name — fine while unused, but relevant whenever this gets wired
into something.

## 7. `FunctionDef.in_args`/`in_arg_names`: broken by multi-attribute dicts

`three_subcomponents_array_concrete.mlir` crashed with an `IndexError` in
`in_args`. Root cause: argument declarations were split with a naive
`.split(', ')`, and the type itself was taken as everything after the first
`:` with no further cleanup. This breaks in two ways once an argument
carries more than one attribute, e.g.
`%arg0: !array.type<2,2 x !felt.type<"bn128">> {function.arg_name = "in", llzk.pub}`:
the comma *inside* the attribute dict gets mistaken for an argument
separator (splitting one argument into two bogus fragments, the second
missing a `:` entirely — hence the `IndexError`), and even in the
single-attribute case the trailing `{...}` text was never stripped, so it
leaked into the parsed `Type` itself.

Fixed by:
- Extending `split_top_level_commas` (`utils.py`) to also track `{`/`}`
  bracket depth (previously only `<`, `[`, `(`), so a comma inside an
  attribute dict is correctly recognised as non-top-level.
- Adding `_parse_in_arg` (`function.py`), which splits a single argument
  declaration into `(name, type_str, attrs_str)` by scanning from the end of
  the string for a balanced trailing `{...}` group, rather than a plain
  string split — so the attribute dict is cleanly separated from the type
  regardless of how many comma-separated attributes it contains.
- `in_args` and `in_arg_names` both now use `split_top_level_commas` for the
  top-level argument-list split and `_parse_in_arg` for the per-argument
  split, instead of duplicating ad hoc string splitting.

## 8. `PodNew` storage allocation: scalar struct-output fields wrongly allocated as arrays

Also in `three_subcomponents_array_concrete.mlir`: `%pod_18_@comp_@out_last`
was allocated via `array.new 1 %pod_18_@comp_@out_last` — but
`lastComponent_0`'s only output member, `out_last`, is `ff` (a plain scalar),
not an array. The later `array.write %pod_18_@comp_@out_last %array_@comp_@out_last[%arg1]`
then tried to write this array value into a single array slot — a type
mismatch, since `array.write`'s source must be a scalar.

Root cause: the storage-allocation loop added to `PodNew` (see §2) computed
`leaf_size = array_total_size(leaf_type.name) or 1` for every leaf from
`_flatten_container_fields`, then unconditionally emitted
`array.new {leaf_size} {field_var}` — the `or 1` conflated "this leaf isn't
array-shaped at all" (`array_total_size` returns `None`) with "this leaf is
an array of size 1", when for a single pod instance (no outer array) a
scalar leaf should never become an array in the first place. (This
computation is correct in `ArrayNew`'s own analogous allocation — there
`leaf_size = outer_count * (array_total_size(leaf_type.name) or 1)`, and the
`or 1` correctly means "no per-element multiplier," still producing one real
array sized to the *outer* array's count. `PodNew`'s allocation has no outer
array, so the same formula degenerates to `array.new 1 ...` for a scalar,
which is wrong.)

Fixed: `PodNew` now checks `array_total_size(leaf_type.name)` directly —
`None` (scalar leaf) emits a plain placeholder assignment
(`{field_var} = 0`) instead of `array.new`; otherwise (an array-typed leaf,
e.g. a struct's `arr<N>`-typed output member) it still allocates via
`array.new {leaf_size} {field_var}` as before.

## 9. Subcomponent naming lost for arrays-of-components

The translator tracks which signal name a subcomponent call's inputs/output
should be shown under (e.g. `mux.s`, `n2ba.out`) so the emitted Core reads
like the original circuit instead of raw SSA names. This worked for a scalar
subcomponent (one `struct.member` per instance, as in
`three_subcomponents_concrete.mlir`'s `@last1`/`@last2`) but was completely
lost once subcomponents were held in an `!array.type<N x !struct.type<...>>`
member instead — `call @lastComponent_0(%25) to %26_@out_last` instead of
`call @lastComponent_0(last1.in1_last) to last1.out_last`. Fixed in two
stages, covering the two shapes this pattern actually appears in.

### 9a. Constant-indexed array (`three_subcomponents_array_concrete.mlir`)

Here each instance is unrolled at a known index (`array.read %array_0[0]`,
`array.read %array_0[1]`, from `felt.const`/`cast.toindex` literals) — the
compiler fully unrolls a small, statically-known component count. Two
existing pre-pass mechanisms in `struct.py`'s `_build_component_naming_maps`
needed extending to reach into arrays:

- `ctx.input_pod_to_member` (`pod_ssa -> member base name`, used by `PodNew`
  for a scalar `$inputs` pod) already got an entry keyed by the *array*
  SSA (`%array_0 -> "last"`) for free, since Part 1's registration doesn't
  care whether the written value is a scalar pod or an array of pods.
  `ArrayRead.to_core` (`array.py`) now checks this map for the array it's
  reading and, when the index is a compile-time constant, names the
  extracted element `"{member}_{idx}"` (e.g. `"last_0"`) instead of a raw
  SSA-derived name — mirroring `PodNew`'s own `"{member}.{record}"`
  convention for the fields inside it.
- A new `_find_array_component_bases` (`struct.py`) detects the "counting
  pod" array that backs an array-of-*subcomponent* member (not `$inputs`):
  it's populated at the end of `compute` by a bulk-copy `scf.for` reading
  each element's `@comp` field into the array that's then `struct.writem`'d
  into the member. This tells us `counting_array_ssa -> member_base`. A new
  `_annotate_array_component_reads` then finds every constant-indexed
  top-level read of that counting array and feeds `"{base}_{idx}"` into the
  *same* `pod_to_member` map that `_annotate_function_calls` already
  consumes for `FunctionCall._member_hint` — no changes needed to that
  annotation pass itself.

### 9b. Loop-instantiated array (`ternary_concrete.mlir`)

Here `Num2Bits_16_325`'s instances are created inside a real `scf.while`
(Circom's `for (var i = 0; i<n; i++)` loop over subcomponents), so the array
index is a genuine runtime value (`%arg4`), never a compile-time constant.
There's no single instance to name at translation time, so per discussion
with the user the target is the bare member name (`"Num2Bits_16_325.in"` /
`"Num2Bits_16_325.out"`) — the "_0"/"_1" per-instance suffix is left for the
user to reconstruct externally via their own symbolic execution of the
emitted `repeat` loop. This needed two further fixes:

- `ctx.input_pod_to_member` only had an entry for the `$inputs` array's
  *original* SSA name (e.g. `%array_1`, from before the `scf.while`) — but
  code *inside* the while body refers to the same array by its own
  block-argument name (`%arg3`), a different SSA name entirely. Added
  `while_iter_args` tracking in Part 1 so every `scf.while` iter-arg's
  block-arg name is aliased to the same base as its (possibly
  multi-hop-traced) initial value.
- Naming can't reuse `ctx.var2const` for "is this index a compile-time
  constant" here: `SCFFor`/`SCFWhile` (`scf.py`) deliberately treat their
  own loop-carried variables as a constant in `ctx.var2const` for
  structural reasons (step-count math, nested-loop bounds) — e.g. a
  `scf.while`'s block arg gets `ctx.var2const[lhs.name] = const` from its
  *initial* value assignment and is never invalidated once the loop body
  (translated once, generically, as one `repeat N` block) starts. Naively
  reusing that here would have named every iteration `"Num2Bits_16_325_0"`.
  Fixed by giving the naming pre-pass its own scope-safe static fold
  (`_fold_index_constants`, reused from 9a) that never touches
  `ctx.var2const` and never treats an `scf.for`/`scf.while` block/induction
  argument as a constant (those are never themselves the *result* of a
  `felt.const`/`arith.constant`, so the fold can't be fooled by them). New
  `_annotate_input_array_reads` walks the whole compute body with this fold
  and stamps the resolved name directly onto each `ArrayRead` node as
  `_semantic_base` (`None` if `arr_ref` isn't a registered component array,
  else `"base_idx"` or bare `"base"`) — `ArrayRead.to_core` just reads this
  precomputed field instead of computing anything from `ctx.var2const`.

Both recursive pre-pass walks (`_annotate_array_component_reads`,
`_annotate_input_array_reads`) copy the constant map down into each nested
scope rather than sharing one mutable dict, so two sibling loops that
happen to reuse the same LLZK-level SSA name for their own induction
variable (seen in `ternary_concrete.mlir`: two separate top-level
`scf.for %arg1 = ...` loops) can't leak a folded constant into each other.

Naming convention settled on `"{member}_{idx}"` (not `"{member}[{idx}]"`,
an earlier iteration) so it reads as a plain identifier and composes
cleanly with the bare (no-suffix) name used for the symbolic-loop case —
the two can never collide, since one always carries a numeric suffix and
the other never does.

## 10. Unroll loops containing a function.call, subindex their component names

§9b left a gap: a subcomponent instantiated inside a genuine runtime loop
(`ternary_concrete.mlir`'s `Num2Bits_16_325`, inside an `scf.while`) could
only ever get one shared, unindexed name (`Num2Bits_16_325.in`/`.out`) — the
loop's body is translated once, wrapped in a Core `repeat N { ... }` block,
so there was no way to tell which iteration a given call belonged to.

Changed `SCFFor.to_core` / `SCFWhile.to_core` (`scf.py`) to branch on a new
`_contains_function_call` check (recursive, same nested-body walk already
used by `_annotate_function_calls`): a loop body with no call keeps today's
single-`repeat` translation, byte-for-byte unchanged; a body containing a
call is instead unrolled into one literal copy of the body per iteration
(no `repeat` wrapper), with each loop's own per-iteration mechanics (`SCFFor`
already knows each concrete `iv` value from `lb`/`step`; `SCFWhile`'s
existing per-iteration init-arg reassignment just runs `steps` times instead
of once) reused as-is. Per the user's instruction, ordinary variables are
**not** given a per-iteration suffix (unlike the old pre-`repeat` unroll from
§3, which suffixed every body-defined name `_it0`/`_it1`) — they're simply
reused/reassigned identically in each copy, since Core's `repeat` already
had this exact "same names, re-run N times" semantics; only a component's
*semantic* name needs to distinguish iterations, because that's what
downstream tooling keys off.

That distinguishing is done via a new `ctx.unroll_index: Optional[int]`
(`core.py`), set only while translating one copy of a loop that got
unrolled for this reason, plus a new `LoopIndexedName(base)` marker
(`core.py`) with a `resolve(unroll_index)` method returning `"{base}#{idx}"`
if unrolling, else the bare `base`. `struct.py`'s `_annotate_input_array_reads`
/ `_annotate_array_component_reads` (from §9) now store `LoopIndexedName(base)`
instead of a bare string for the "index not constant" case — the
constant-index case (a plain `"{base}_{idx}"` string) is untouched.
`ArrayRead.to_core` (`array.py`) and `FunctionCall.to_core` (`function.py`)
each gained a two-line `isinstance(x, LoopIndexedName)` resolve right after
reading `self._semantic_base` / `self._member_hint`; everything downstream
of that line in both methods is unchanged. This keeps the pre-pass (§9)
fully decoupled from whether unrolling actually happens: `resolve(None)`
degrades to exactly the old bare-name behavior.

Verified end-to-end: `ternary_concrete.mlir`'s `repeat 2 { ... }` around the
`Num2Bits_16_325` loop (previously at the line the user pointed at) is gone,
replaced by the body written out twice — `call @Num2Bits_0(Num2Bits_16_325#0.in)
to Num2Bits_16_325#0.out` in the first copy, `Num2Bits_16_325#1.in`/`.out` in
the second, with every other line (e.g. `%7_aft95 = felt.add %arg2 %6_aft95`)
identical between copies. `three_subcomponents_array_concrete.mlir`'s output
(no loop there contains a call) is byte-for-byte unchanged.

Checked for the one flagged risk (a component-array read and the
`function.call` that consumes it living in *different* loops, which would
resolve against the wrong `ctx.unroll_index`): not observed in either
example — the read and its call are always co-located in the same loop. No
`# TODO` was needed; noted below in case a future example splits them.

## 11. `scf.while` bug: a reassigned array-typed loop-carried value lost its contents

Found via `ternary_modified_concrete.mlir` (`Num2Ternary`'s `aux_out =
Num2Bits(2)(...)`, reassigned to a fresh array each loop iteration instead
of being mutated in place). `SCFWhile.to_core`'s yield-reassignment step —
`for yield_val, (before_in_arg, type_) in zip(yield_op.operands,
self.init_args): ... translate_assignment_core_with_ctx(before_in_arg,
yield_val, type_, ctx)` — destructured `self.init_args`' second tuple
element as `type_`, but `init_args` is `List[Tuple[SSAVar, SSAVar]]`
(`(block_arg, initial_value)`): that "type_" was actually the *initial-value
SSAVar*, not a `Type`. `translate_assignment_core_with_ctx`'s `is_ff =
"array" not in type_.name and ...` then checked for the substring "array"
inside an SSA name string (e.g. `"%nondet_2"`) instead of an actual type
name — almost never true by coincidence — so an array-typed reassignment
silently emitted a scalar `%arg2 = %22_aft103` instead of
`array.copy %22_aft103 %arg2`, dropping the array's actual contents.

This stayed invisible in every previously-seen example (including
`ternary_concrete.mlir`'s own array-typed `$inputs`-array loop-carried
value) because the buggy call only runs when `yield_val.name !=
before_in_arg.name` — every other array-typed loop-carried value seen so
far is yielded back *unchanged* (mutated in place, same name in and out),
so the mistyped branch was never reached until an example reassigned one to
a genuinely different name.

Fixed by zipping in `in_types` (`self.func_type[0]`, already computed
earlier in `to_core` and positionally aligned with `self.init_args` — the
same list already used correctly for the *initial* per-arg assignment a few
lines above) instead of reusing `init_args`' own tuple. Added a regression
test (`test_while_to_core_reassigned_array_loop_carried_value_uses_array_copy`,
`test_scf_parse.py`) constructing exactly this shape — a second loop-carried
argument, array-typed, yielded back under a different SSA name — and
confirmed it fails against the pre-fix code and passes with the fix.

## 12. `_emit_container_field_copy`: extract-shaped call sites had source/dest offset backwards

Found via `ternary_modified_concrete.core`: `array.new 2 %13_aft103_@comp_@out`
followed by a copy loop, appearing twice (once per unrolled iteration, §10)
— but the second copy's write offset (derived from the 2nd instance's
index) targeted the *freshly allocated, size-2* `%13_aft103_@comp_@out`
itself, an out-of-bounds write.

Root cause, in `array.py`'s shared `_emit_container_field_copy(src_arr,
dest_arr, start, length, base)`: it only ever supported one shape — copy
`src_arr[0..length)` into `dest_arr[start..start+length)`, offset always on
the destination. That's the right shape for *inserting* a small, per-instance
value into a bigger structure-of-arrays backing array (`ArrayWrite`,
`ArrayInsert` — both correct, already offsetting the big array they write
into). It's the *wrong* shape for *extracting* a slice back out of that
backing array into a freshly `array.new`'d, correctly-sized small array
(`ArrayRead`'s container branch, `ArrayExtract`'s both branches) — there,
the offset needs to land on the *source* read (picking the right instance
out of the big array), while the destination is always written 0-based.
All three extract-shaped call sites passed `(big_array, small_array,
instance_offset, ...)` into the insert-shaped helper, so the offset
silently applied to the small destination instead: every instance read the
same first `leaf_size` elements of the backing array (ignoring which one
was actually wanted), and every instance past the first wrote out of bounds
on its own local array.

This is not something the unrolling change (§10) introduced — the same
mistranslation already existed in the `repeat`-wrapped, non-unrolled form,
it would just misbehave once the emitted Core actually *executed* the
repeat block with a changing offset each pass, rather than being visible as
duplicated, obviously-wrong text. Confirmed the identical bug (now fixed)
in `ternary_concrete.mlir`'s own `Num2Bits_0`-instantiating loop too — the
first place §10's unrolling made it observable, not the only place it
existed. Never caught because none of `ArrayRead`/`ArrayWrite`/
`ArrayExtract`/`ArrayInsert` had any unit test exercising this
"nested array-typed field, non-trivial `leaf_size`" branch at all —
`ArrayExtract`/`ArrayInsert` had no `to_core` tests whatsoever before this.

Fixed by adding an `offset_src: bool = False` parameter to
`_emit_container_field_copy` (default preserves the existing, correct
insert behavior) and passing `offset_src=True` at the three extract-shaped
call sites (`array.py`: `ArrayRead`'s container branch, `ArrayExtract`'s
container and plain branches). Added `to_core` tests for all four ops
against this exact branch (`test_array_parse.py`), including two
(`ArrayExtract`, `ArrayInsert`) that had none before.

## 13. `array.new` with initial elements

`babypbk_test_concrete.mlir` uses `array.new %e0, %e1 : <2 x !felt.type<...>>`
(a felt array initialised inline) — a form `ArrayNew` never actually
supported: its docstring/regex assumed a syntax
(`array.new : (%x, %y) : !type`) that, it turns out, never matches real LLZK
output; the real syntax has no leading colon or parentheses. Fixed the regex
(matching each element with `[^\s,]+` so a trailing comma isn't swallowed
into the token) and updated the two existing tests that encoded the wrong
assumed syntax. `ArrayNew.to_core` no longer raises `NotImplementedError`
for felt arrays with initial elements — it emits `array.new {dim} {result}`
followed by one `array.write {elem} {result}[{i}]` per element (Core allows
writing a value, constant or otherwise, directly into an array slot). Pod/
struct arrays with initial elements still raise `NotImplementedError` (not
exercised by any current example).

## 14. `arith.constant true`/`false`: boolean literals crashed the parser

Also in `babypbk_test_concrete.mlir`: `%true = arith.constant true` crashed
`ArithConst.parse` in two ways. First, boolean constants carry **no type
annotation at all** in real output (no trailing `: i1`), but the regex
required one — made it optional, defaulting to `i1` when absent. Second,
`ArithConst.to_core` did `int(self.value)`, which fails on the literal string
`"true"`/`"false"` — mapped those to `1`/`0` before falling back to
`int(value)` for everything else.

A second, independent call site hit the exact same `int(op.value)` gap:
`struct.py`'s `_fold_index_constants` (a pre-pass that folds compile-time-
constant indices ahead of `ctx.var2const` being populated, feeding
`_annotate_array_component_reads` from §9) did its own `int(op.value)` for
every `ArithConst` it sees, independently of `ArithConst.to_core`. Surfaced
while verifying `scf.execute_region` (§15) — `babypbk_test_concrete.mlir`
got past `scf.execute_region` entirely and crashed here instead. Rather than
duplicating the `"true"/"false" -> 1/0` mapping ad hoc a second time,
extracted it into a shared `parse_arith_const_value` (`arith.py`) and had
both `ArithConst.to_core` and `_fold_index_constants` call it.

## 15. `scf.execute_region` implementation

`scf.execute_region` (used in 19 `circomlib_examples/*.mlir` files, 2–48
occurrences each) was entirely unimplemented — parsing aborted with "no
operation matches the statement." Two research passes over the real files
confirmed it's a pure **grouping/let-binding** construct: always exactly one
region, no operands, no condition or loop bound, executed exactly once
unconditionally, terminated by a plain `scf.yield` whose operands become the
op's own result(s). All branching inside it is ordinary nested `scf.if`;
looping is done by whatever `scf.while`/`scf.for` it's embedded in. Three
shapes recur: zero results (side-effect-only, e.g. `constrain.eq` checks),
two pod-typed results (an "index selector" picking between two
subcomponent-holding pods via a nested `scf.if`), and a single scalar result
(a multiplexer chain of nested `scf.if`/`else`).

Implemented by generalizing existing mechanisms rather than inventing new
ones, per the two-pod-result case's actual need:

- **`SCFYield.to_core` fix (the real unlock)**: it computed
  `type_.to_core()` (only ever `"ff"`, `"arr<N>"`, or `None`) and asserted it
  wasn't `None`, so it could never yield a pod/struct-typed value.
  `SCFCondition.to_core`, a few hundred lines below in the same file,
  already solves this by calling `translate_assignment_core_with_ctx` — the
  same central dispatcher used everywhere else (plain values, structs,
  arrays of pod/struct). Rewrote `SCFYield.to_core` to do the same. Verified
  this produces identical output for the existing felt/array cases (adds
  constant propagation as a strict improvement) and unlocks pod propagation
  via the dispatcher's existing `ctx.ssa2pod_var` branch — the same branch
  already exercised by `scf.while`-carried pod values (§5). This also fixes
  pod-typed yields for `scf.if` itself "for free," which the real example
  needs anyway (the nested `scf.if` inside the two-pod-result
  `execute_region` yields pod values). Traced by hand that both `scf.if`
  branches register `ctx.ssa2pod_var` under the identical key (derived from
  the *shared* result name both branches assign into) — no cross-branch
  staleness, mirroring how this already works for felt/array multi-results.
- **New `SCFExecuteRegion` block op** (`scf.py`): header/type parsing
  modeled on `SCFIf`'s (including its parenthesized-vs-bare multi-type
  handling), but with a single region and no condition/`else` — so
  `to_core` needs **no Core-level wrapper syntax at all**: it inlines every
  body statement except the last, then hands the terminating `scf.yield` off
  exactly like `SCFIf._translate_branch` does for one branch (set
  `ctx.scf_result = self.results` around it).
- **`_collect_result_names`**: added an `SCFExecuteRegion` branch (mirroring
  the existing `SCFIf`/`SCFFor`/`SCFWhile` ones) so `SCFWhile.parse`'s
  cursor-tagged `_bef`/`_aft` renaming (§5) also renames an
  `execute_region`'s own result name when nested inside a `scf.while` body —
  exactly the real example's structure. Without this, the existing generic
  `hasattr(op, 'body')` fallback would still recurse into its body and
  rename interior names, but would miss the op's own `%34`-style result,
  risking the same class of cross-scope collision fixed in §5.

Added `tests/test_scf_parse.py` coverage for all three real shapes
(zero-result, single-scalar-result, multi-pod-result) plus a regression test
confirming `SCFIf` can now yield a pod-typed value.

Verified: full suite green (318 tests), no regressions across
`ternary_concrete.mlir`, `mux4_1_concrete.mlir`, `mux2_1_concrete.mlir`,
`three_subcomponents_array_concrete.mlir`. `babypbk_test_concrete.mlir`
itself progresses past `scf.execute_region` entirely; with §14's second
call site also fixed, it now gets past that too and hits `SCFWhile`'s
`infer_n_repetitions_from_expressions` (`core_utils.py`), a different,
unrelated, and more substantial gap — see below. Expected, given 19 files
use `scf.execute_region` and this session has repeatedly found one gap only
to surface the next.

## 16. Support "pure functions" (a `poly.template` with no `struct.def`)

`escalarmulw4table_concrete.mlir` crashed inside `FunctionDef.to_core`
(`ctx.core_func2args[None]`) for `pointAdd_1` and `EscalarMulW4Table_0` — both
`poly.template` blocks whose *only* child is a bare `function.def`, with no
`struct.def` wrapping it, unlike every prior example (always
`struct.def { function.def @compute(...); function.def @constrain(...) }`).
Root cause: `ctx.current_core_function`/`ctx.core_func2args` were populated
*only* inside `StructDef.to_core`, from `struct.member` declarations —
`PolyTemplate.to_core` unconditionally dispatched its one child's `to_core`
directly, so a bare `FunctionDef` ran with neither ever set.

Fixing this exposed a second, immediately-blocking problem in the same
file: `EscalarMulW4Table_0` (line 2) calls `pointAdd_1::pointAdd_1` (line
101, inside a nested `scf.while`) — but `pointAdd_1` is declared *after* it
(line 165). Every struct-to-struct call in prior examples has been
correctly ordered (callee's `struct.def` always translated first), and
`ModuleOp.to_core` (`llzk.py`) just iterates its body in file order with no
pre-pass, so this forward reference would immediately crash on
`ctx.llzk_func2core[KeyError]` right after the registration gap above was
fixed — not a "different, later gap" to defer, but a direct consequence of
the exact feature being added.

Per the user's framing — a pure function's inputs and outputs are arbitrary
values, not named struct signals — fixed by:

- **`_register_pure_function`** (`poly.py`, new): registers a pure
  function's signature the same way `StructDef.to_core` registers a
  struct's `@compute`, but sources out-args from the function's own
  `function.return` operands — kept as their own SSA names (e.g.
  `"%nondet"`), never `@`-prefixed struct-member names — instead of
  `struct.member` declarations. Idempotent (checks `ctx.llzk_func2core`
  first), so it's safe to call both ahead of time (pre-pass, below) and
  again, redundantly, right before emitting the function's own body.
  Registration only reads the already-fully-parsed `FunctionDef` itself, no
  dependency on any other function being registered first.
- **`PolyTemplate.to_core`** now branches on its one child's type: a bare
  `FunctionDef` goes through `_register_pure_function` + emits its body
  directly (no struct members, no separate `@constrain`); a `StructDef`
  child is unchanged.
- **`FunctionDef.to_core`**'s `signature_out` construction stripped a
  leading character unconditionally (`arg[1:]`), assuming every out-arg is
  `@`-prefixed. Made it conditional — strip only if `arg.startswith('@')` —
  so a pure function's out-arg keeps its `%` prefix, consistent with how its
  *input* args already keep theirs in the signature. Also removed a stray
  debug `print(core_name, ctx.core_func2args)` left in this method.
- **`FunctionCall.to_core`** always built output names from `@`-prefixed
  member names (`f"{member}.{out_arg[1:]}"` / `f"{result.name}_{out_arg}"`),
  assuming a struct's `@compute`. Detects a pure callee by checking whether
  its registered out-args are `@`-prefixed at all (never mixed for one
  callee), and if not, uses the call's own result name(s) directly via the
  *existing* multi-component convention (`SSAVar.to_core_component`,
  already used by `scf.while`/`scf.for`/`scf.execute_region`) — `"%40"` for
  a single result, `"%40#0"`/`"%40#1"` for more than one — with no
  semantic-name lookup and no `ctx.ssa_to_name` registration (nothing
  downstream needs one; the file already just uses the result directly,
  e.g. `array.read %40[%41]`).
- **`ModuleOp.to_core`** (`llzk.py`) gained a pre-pass: before translating
  any body, scan the top-level module for every `poly.template` wrapping a
  bare `function.def` and register it via `_register_pure_function`.
  Registration has no cross-function dependencies, so a single unordered
  scan is enough — no dependency graph or topological sort needed.
  Struct-based templates are untouched — they still require callees
  declared first, as before. `Main_0` (the actual `llzk.main` entry point)
  is unaffected — it's still struct-wrapped, and `_yield_main_function`'s
  `"::@compute"`-based lookup didn't change.

Verified `pointAdd_1` translates correctly in isolation (correct signature
`def @pointAdd_1(%arg0: ff, ...) -> %nondet: arr<2> { ... }`, correct
elliptic-curve-point-addition body, correct registration with non-`@`
out-args) and that `FunctionCall.to_core`'s new branch produces exactly
`call @pointAdd_1(%29,%31) to %40` (single result) and
`call @foo(%1) to %50#0,%50#1` (multi-result), both matching the file's
actual downstream usage (`array.read %40[%41]` directly, no signal lookup).
Added tests to `test_poly_parse.py`, `test_function_parse.py`, and
`test_llzk_parse.py` (full suite: 325 tests, up from 318).

`escalarmulw4table_concrete.mlir` itself progresses well past both the
original crash and the forward-reference issue, then hits the same
`infer_n_repetitions_from_expressions` "two expressions" limitation
documented below (already found via `babypbk_test_concrete.mlir`) —
expected, not a regression. (Generalized in §17 below; that limitation no
longer applies as such, though this file still doesn't fully translate, for
a different reason — see §17's "Known pre-existing" notes.)

## 17. `infer_n_repetitions_from_expressions`: generalized to conditions referencing more than one variable

Previously assumed a while's exit condition reduces to exactly one "ground
variable" compared against a literal constant, raising
`NotImplementedError("While condition relies on two expressions to be
computed")` otherwise — hit by `babypbk_test_concrete.mlir` and
`escalarmulw4table_concrete.mlir` (see §16).

Root cause turned out to be two different things bundled into one symptom:

- The bound may reference a variable that isn't loop-carried at all — e.g.
  `escalarmulw4table_concrete.mlir`'s while condition `arg3 < arg1*4`, where
  `arg1` ("k") is the *enclosing function's own parameter*, not a loop
  variable and not a literal. The old backward-walk in
  `_process_while_variables` couldn't distinguish "an outside value that
  might be knowable" from "a second loop-carried variable" and just failed.
- Separately, the "leftover set" that walk produces (previously the only
  signal available for detecting "more than one variable") is not actually a
  reliable way to identify *which* name is the loop-carried variable: when
  that variable's own recurrence collapses entirely to constants (e.g. it's
  unconditionally reset to a literal each iteration rather than incremented
  — seen in `mux1_1_concrete.mlir`'s while at line 199, whose `scf.yield`
  reassigns its counter to a hardcoded `1`), the walk fully consumes it and
  it never survives as a leftover, even though it's still a bona fide
  loop-carried variable. This was silently masked before because the old
  code never actually used the leftover set for variable identification
  (only for a `len() <= 1` sanity check) — it identified the "variable" side
  of the comparison via `isinstance(var2expression[lhs.name], FeltConst)`
  directly. An initial fix attempt that leaned on the leftover set for
  identification (to solve the first bullet) broke `mux1_1_concrete.mlir` as
  a regression — caught only by re-running the full example sweep, not the
  unit suite, since no existing test exercised this shape. Fixed by
  identifying the loop-carried variable directly from the condition's own
  operands via `initial_values` membership instead (only ever populated for
  the while's own declared loop-carried arguments).

New design (`core_utils.py`):

- `infer_n_repetitions_from_expressions` no longer takes a `ground_variables`
  parameter (removed as dead/misleading — the caller's backward-walk result
  was never actually needed here). It identifies the loop-carried variable
  via `initial_values` membership, then collects any free variables the
  *bound* side references (`_collect_free_var_names`) that aren't defined
  anywhere inside the while, resolving each via a new `var2const` parameter
  when known (folded in as a `FeltConst` leaf, same as a literal) or
  recording it as unresolved otherwise.
- If every free variable resolves: unchanged behavior — evaluate the bound
  to a concrete int (now via `construct_function_from_expressions`, not a
  raw `isinstance(..., FeltConst)` check, so this transparently covers a
  resolvable *expression* bound too, e.g. `k*4` once `k` turns out to be
  known — not just a bare literal) and simulate as before.
- If some free variable is unresolved: falls back to a `SymbolicSteps`
  result (a small dataclass: the operations needed to precompute the bound
  once, the bound variable, initial value, predicate, and which side the
  loop variable is on) — a Core arithmetic formula for the iteration count,
  assigned to a fresh variable and used directly as `repeat`'s operand,
  rather than a Python int. Only supported when the loop variable's own
  per-iteration update is a simple `+1`/`-1` step (detected by probing the
  update function at two points, `_detect_affine_step`); anything else
  raises a clear `NotImplementedError` naming the unresolved variable(s). Per
  Core's own grammar (`CORELLZK.md`: `sexp := id | Z`), `repeat`'s operand
  must be a plain identifier or literal — hence assigning the formula to a
  fresh variable first, not embedding an expression directly.

`scf.py`: `SCFWhile` now stores its own `cursor` (already computed at parse
time, already used to disambiguate `_bef{cursor}`/`_aft{cursor}` renames) to
mint a collision-free fresh variable name for a symbolic step count.
`_extract_step` threads `ctx` through so `ctx.var2const` reaches the new
resolution logic. `to_core` emits the setup operations once before a
`repeat <fresh var> {`, in the same "single repeat block" branch as a
concrete int — a symbolic count can never drive the *unrolling* branch (a
Python `for i in range(steps)`, used when the body contains a
`function.call`), since there's no concrete count to loop over; this raises
an explicit `NotImplementedError` instead.

Verified via a full sweep of every `circomlib_examples/*.mlir` file (not
just the pytest suite) comparing pass/fail before and after: no
regressions — every example that passed before still passes, including
`mux1_1_concrete.mlir` (the regression this sweep caught and drove the
`initial_values`-based redesign above). `escalarmulw4table_concrete.mlir`
and `babypbk_test_concrete.mlir` now correctly progress *past* the old
"two expressions" failure, but each still fails end-to-end for reasons
outside this fix's scope (see below) — expected, not a regression, and the
algorithm fix stands on its own regardless.

Added `tests/test_core_utils.py` (new — direct unit tests of
`infer_n_repetitions_from_expressions` and its helpers) and extended
`tests/test_scf_parse.py` with `SCFWhile.to_core`-level coverage of the
symbolic-steps path (lt/le, an expression bound needing setup ops, the
var2const-resolved case staying concrete, and the function-call-body error).
Full suite: 348 tests, up from 325.

## 18. `bool.and`-combined while conditions: min() of independently-inferred halves

`infer_n_repetitions_from_expressions` (§17) still only handled a condition
that's a single `BoolCmp`, raising `AssertionError: For now, only BoolCmp
whiles are handled` for a condition like `bool.and(cmp1, cmp2)` — hit by
`eddsa_test_concrete.mlir` and `pointbits_loopback_concrete.mlir`.

Generalized: a `bool.and` condition is now handled by inferring each half's
iteration count independently (exactly as a lone `BoolCmp` would be) and
taking the `min()` — the loop stops as soon as either half first goes false.
This is correct regardless of whether the two halves reference the same or a
different loop-carried variable, since each count already fully accounts for
its own condition's failure point in isolation (verified by reasoning through
the monotonicity assumption already implicit in `count_iterations`).

No changes were needed in `scf.py`: `SCFWhile._extract_step`'s existing
backward walk (`_process_while_variables`) is already fully generic over
`operation.operands` — since `BoolBinary.operands` returns `[lhs, rhs]`
exactly like any other op, it already correctly populates `var2expression`
entries for both `BoolCmp` halves of a `bool.and` today, with zero
modification needed. The whole change is isolated to `core_utils.py`:
`infer_n_repetitions_from_expressions` now dispatches on whether the
condition is a `BoolCmp` or a `BoolBinary("bool.and", ...)`; the former's
existing logic (unchanged) was mechanically extracted into
`_infer_from_comparison`, called once per half for the latter, combined via
a new `_combine_min_steps` (plain `min()` when both halves resolve to a
concrete int; an explicit `NotImplementedError` if either needs the
`SymbolicSteps` fallback — combining a symbolic count via `min()` would need
emitting a Core-level conditional to pick the smaller at runtime, a
materially bigger feature not needed by any known example, so deliberately
out of scope here).

**Investigated before implementing, and confirmed this would *not* rescue
either motivating example**: both `eddsa_test_concrete.mlir` and
`pointbits_loopback_concrete.mlir` hit the identical `bool.and` inside a
shared `sqrt_0` (Tonelli–Shanks modular square root) helper, which has three
separate, compounding blockers unrelated to AND-handling: (1) both halves use
predicate `ne`, which `infer_n_repetitions_from_expressions` has never
supported (only `lt/le/gt/ge`); (2) the compared variables' own *initial
values* are `felt.pow(n, ...)` results (`n` being `sqrt_0`'s own parameter),
never tracked in `ctx.var2const`, so neither is recognized as "the
loop-carried variable" via `initial_values` membership; (3) their
per-iteration update flows through a *nested* `scf.while`'s result, invisible
to the backward-walk since `SCFWhile` doesn't override `Operation.result` —
would hit a raw `KeyError`, not a clean error. This loop's true iteration
count is genuinely data-dependent on `n` at runtime — not expressible as
either a concrete int or a `SymbolicSteps` formula under the current
architecture, independent of `bool.and`-handling. Implemented anyway, per
explicit decision: correct and useful in its own right for any future/other
`bool.and` case built from ordinary `lt/le/gt/ge` comparisons on affine
counters, even though it doesn't unblock these two specific files.

Verified via the same full `circomlib_examples/*.mlir` sweep methodology as
§17: no regressions (every example's pass/fail status is unchanged), and
`eddsa_test_concrete.mlir`/`pointbits_loopback_concrete.mlir` now fail with
the precise, predicted error (`AssertionError: Only inequalities are
implemented`, from blocker (1) above) instead of the old generic "only
BoolCmp" message.

Added `tests/test_core_utils.py::TestBoolAndCondition` (same loop variable,
different loop variables, `gt`/`ge` normalization combined with `lt`, the
symbolic-combination `NotImplementedError`, a non-`BoolCmp` operand) and one
`SCFWhile.to_core`-level integration test in `tests/test_scf_parse.py`.
Full suite: 356 tests, up from 348.

## 19. Pod-in-pod inside `scf.while`: two unanchored substring checks plus a missing recursive registration

`circomlib_examples/poseidon3_test_concrete.mlir` crashed with
`KeyError: '%573_aft362208'` in `PodRead.to_core` — combining pods inside
pods inside an `scf.while` (e.g. `%573 = pod.read %arg3[@idx_0]` followed by
`%574 = pod.read %573[@in]`, where `@idx_0`'s own type is itself a non-empty
pod `!pod.type<[@in: !array.type<3 x !felt.type<...>>]>`). Three independent
bugs compounded into this one symptom, found by instrumenting `ctx.ssa2pod_var`
and re-testing after each fix in isolation:

- **`utils.py`: `array_dimensions`/`array_felt_dimensions` not anchored.**
  Both used an unanchored `re.search`, so a pod field whose type merely
  *contains* a nested felt array (e.g. the `@idx_0` type above) matched the
  `<3 x !felt.type<...>>` pattern buried inside it and was misread as if the
  field itself were a plain felt array — `PodNew`'s storage-allocation loop
  then took the wrong branch entirely (`array.new 3 %pod_@idx_0` instead of
  recursing into it as a pod) and never touched `ctx.ssa2pod_var` for it at
  all. `is_array_type` (§4) had already been anchored to guard against
  exactly this trap — its docstring even calls it out — but the two sibling
  functions doing the equivalent felt-array check were never given the same
  treatment. Fixed by anchoring both the same way: strip an optional
  `!array.type` prefix, then `re.match` (not `re.search`) from the start of
  what's left.
- **`core_utils.py`: `translate_assignment_core_with_ctx`'s struct check not
  anchored.** Same class of bug, one level up: `if "!struct" in type_.name:`
  matched a *pod* type that merely contains a struct-typed field (e.g.
  `!pod.type<[@count: index, @comp: !struct.type<@Ark_0::@Ark_0<[]>>, ...]>`,
  from `poseidon3_test_concrete.mlir`'s `%pod_35 = pod.new {@idx_0 = %pod_20,
  ...}`), treating the whole pod as if it were itself that struct's output —
  looking up `"<Struct>::@compute"` in `ctx.llzk_func2core` and copying that
  struct's own out-args under the pod's name instead of the pod's actual
  fields, silently skipping `ssa2pod_var` registration entirely. Fixed by
  anchoring to `type_.name.strip().startswith("!struct.type")`.
- **`pod.py`/`array.py`: nested pod registration was genuinely missing, not
  just masked by the two bugs above.** Verified by reverting only this piece
  (via `git stash`) after the two anchoring fixes: the original `KeyError`
  still reproduced. `PodNew` and `ArrayRead` only ever registered the
  *first* level of a pod's fields in `ctx.ssa2pod_var` — a non-empty pod
  nested inside another pod never became a key itself (only its ultimate
  leaf, via `_flatten_container_fields`, got real storage), so a later
  `pod.read`/`pod.write` chained through that intermediate pod had nowhere
  to resolve to. This matches a limitation already called out in this file's
  "Known pre-existing" list below (§16 era) — not previously exercised by
  any example. Fixed by adding `_register_nested_pod_vars` (`pod.py`,
  recursive): registers `ctx.ssa2pod_var[var_name]` for a pod-typed
  variable using the same naming convention already used one level up
  (SSA-derived `"<base>_<field>"`, or, for a struct-member's semantically
  named pod, `_semantic_field_var`'s dot-then-underscore convention), then
  recurses into any field that is itself pod-typed. Called from `PodNew`'s
  storage-allocation loop and from `ArrayRead`'s pod-extraction branch
  (replacing that branch's previous empty-pod-only special case, which is
  now just the base case of the general recursion).

Also removed two stray leftover `print()` debug statements in
`PodRead.to_core` found in the same file while tracing this.

With all three fixes, `poseidon3_test_concrete.mlir` progresses roughly
480,000 (generated) lines further — past the reported crash and its whole
`scf.while` entirely — before hitting an unrelated, pre-existing gap:
`llzk.py`'s `nondet` handling doesn't recognize a nested
pod-of-pod-of-struct type (`ValueError: llzk.nondet transformation for not
recognized expression: ...`). Left as-is; out of scope for this fix.

Added regression coverage for all three bugs: `tests/test_array_parse.py`
(`array_felt_dimensions`/`array_felt_first_dimension` anchoring, a new
`TestArrayDimensions` class for `array_dimensions` — previously untested —
plus its own anchoring case, and two `ArrayRead.to_core` tests for recursive
nested-pod registration under both SSA and semantic naming) and
`tests/test_pod_parse.py` (`PodNew` recursive registration under both SSA
and semantic/member naming, the exact array-leaf-not-misread-as-array
shape, a full `PodNew`→`PodRead`→`PodRead` chain resolving without
`KeyError`, and the `core_utils.py` struct-anchoring fix exercised through
`PodNew`'s init-value assignment path). Confirmed all ten new tests fail
against the pre-fix code (checked via `git stash` on just the three fixed
files) and pass with it restored — not tautological. Full suite: 370 tests,
up from 356.

## 20. `LLZKNondet.to_core`: generalized array handling, `NotImplementedError` instead of `ValueError`

Follow-up to §19's "Known pre-existing" note above (`llzk.nondet` on a
pod-of-pod-of-struct type). Per explicit instruction, simplified and
generalized `LLZKNondet.to_core` (`llzk.py`): check whether the type is
`!felt.type` (initialize to `0`) or an array of *any* element type and any
dimensionality (initialize via `array.new` to its total element count, all
zeros — same "no explicit per-element write needed" convention `ArrayNew`
already uses for a plain `array.new` with no initial elements); anything
else now raises `NotImplementedError` (previously `ValueError`), naming it
explicitly as a case we may want to handle later rather than a hard error.

Previously this only special-cased a *felt* array specifically
(`array_felt_first_dimension`), so a non-deterministic array of index, pod,
or struct elements (any element type other than felt) would have fallen
through to the same `!felt.type` substring check and then to the error
branch instead of being recognized as an array at all. Replaced with the
element-type-agnostic `is_array_type` (anchored — see §4/§19) to detect any
array shape, and `array_total_size` (§19 — also anchored) to compute its
total element count regardless of dimensionality. The `!felt.type` check
itself is now also anchored (`.strip().startswith(...)`, not a plain `in`
substring test) — required for correctness given the array check now runs
unconditionally after it: an array-of-felt type (e.g.
`!array.type<3 x !felt.type<...>>>`) contains `"!felt.type"` as a substring
too, so an unanchored check would have wrongly taken the scalar branch for
it instead of the array one, exactly the bug class fixed twice already in
§19.

`poseidon3_test_concrete.mlir` still fails at the identical spot (the
pod-of-pod-of-struct `llzk.nondet` from §19's "Known pre-existing" note) —
expected, since that type is still neither a felt nor an array and this was
never meant to unblock it, only to make the rejection explicit
(`NotImplementedError`, naming the unrecognized type) and correct the
generalization for every array shape that *is* now handled correctly.

Added `tests/test_llzk_parse.py::TestLLZK` coverage: felt scalar, 1-D and
2-D felt arrays (2-D verifies `array_total_size`'s product-of-dims, not
just the first dimension), a non-felt (struct) array and a pod array (the
actual generalization), a plain pod and a bare `index` correctly raising
`NotImplementedError`, and the pod-with-nested-felt-array-field anchoring
case (must not be misread as either a felt or an array). Full suite: 378
tests, up from 370.

## 21. `LLZKNondet.to_core`: pod-typed results, assigned like `pod.new`

Follow-up to §20: `poseidon3_test_concrete.mlir` also has `llzk.nondet`
results typed as a pod (the same pod-in-pod / pod-with-struct-and-empty-pod
shapes §19 fixed `PodNew`/`PodRead`/`PodWrite` for), which §20 correctly
routed to `NotImplementedError` since a plain pod is neither felt nor array
— but per explicit instruction, generalized further: a pod-typed `llzk.nondet`
result is now assigned exactly as `pod.new` would assign a field it was
given no initial value for, recursing through nested pod fields the same
way.

Extracted `PodNew.to_core`'s two pieces of per-pod logic into standalone
functions in `pod.py` so they can be shared with `LLZKNondet` (and any
future caller) instead of duplicated:
- `_register_pod_top_level(ctx, var_name, fields)`: the top-level
  `ctx.ssa2pod_var` registration (SSA-derived `"<base>_<field>"` names, or
  semantic `"<member>.<field>"` names when `ctx.input_pod_to_member` applies)
  — previously inlined at the top of `PodNew.to_core`.
- `_allocate_pod_field_storage(ctx, var_name, type_)`: the per-field
  storage-allocation logic — previously `PodNew.to_core`'s loop body for a
  field with no initial value (array → `array.new`; struct/pod → recurse via
  `_flatten_container_fields`, registering nested pod fields via
  `_register_nested_pod_vars`, §19). Deliberately preserves `PodNew`'s
  existing behavior exactly, including its one pre-existing gap: a plain
  scalar (felt/index) field with no initial value still gets no placeholder
  assignment at all — matching "as done with `pod.new`" precisely rather
  than introducing new, unrequested scalar-zeroing semantics here.
- New `register_and_allocate_pod(ctx, var_name, type_str)`: parses the pod's
  fields and applies both of the above to every field (a nondet pod has no
  operands at all, so *every* field is in the "no initial value" case,
  unlike `PodNew` which only does this for fields the op wasn't given a
  value for). `PodNew.to_core` itself now just calls these three pieces
  instead of inlining them, with no behavior change.
- `LLZKNondet.to_core` (`llzk.py`) gained a third branch, checked after felt
  and array: `type_name.strip().startswith("!pod.type")` (anchored, same
  reasoning as §20) calls `register_and_allocate_pod`.

`poseidon3_test_concrete.mlir` now progresses past both pod-typed `nondet`
occurrences that previously hit §20's `NotImplementedError` (480,056
generated lines now, up from 479,999) before hitting a new, unrelated gap:
`SCFCondition.to_core`'s `type_.to_core()` returns `None` for a pod type
(only felt/array are supported there), tripping its
`assert to_core_type is not None` when a `scf.while`'s condition passes a
pod-typed loop-carried value through `scf.condition`. Out of scope here —
a different code path (`SCFCondition`/`Type.to_core`, not pod registration
or `nondet`) — not investigated further this session.

Added `tests/test_llzk_parse.py` coverage: a pod with a plain scalar field,
a pod with a felt-array field, the exact pod-in-pod shape from the real
file (asserting the same recursive `ssa2pod_var` registration §19 added),
and the struct-plus-empty-pod-field shape. Full suite: 380 tests, up from
378.

## 22. `SCFCondition.to_core`: removed a stale `Type.to_core()` assert (never actually fixed alongside `SCFYield`, §15)

Follow-up to §21's "Known pre-existing" note (the `SCFCondition` crash on a
pod-typed `scf.while` condition). Investigated first whether this was
somehow tied to the oddly double-suffixed variable name in the crash
(`%571_bef362465_aft362275`), since that looked like a nested-loop artifact
worth understanding before touching anything:

- **The double suffix is real, but harmless — not the bug.** `SCFWhile.parse`
  (`scf.py`) tags its `_bef{cursor}`/`_aft{cursor}` renames with its own
  header line number so *sibling* whiles reusing the same LLZK SSA numbers
  don't collide (§5) — but `_collect_result_names` recurses into a nested
  inner `scf.while`'s body uniformly with every other nested construct, so
  when an *outer* while's rename pass runs, it also re-renames an *inner*
  while's already-cursor-tagged names (e.g. `%571` → `%571_bef<inner
  cursor>` → `%571_bef<inner cursor>_aft<outer cursor>`). This is
  functionally harmless (the rename mutates the same `SSAVar` object in
  place everywhere it's referenced, so every definition/use site inside the
  affected subtree stays consistent — just under a longer name); no code
  path in `SCFWhile.to_core` looks anything up by a stale single-suffix
  name. It was simply never exercised before (no existing test builds a
  nested `scf.while` through `.parse()`) or discussed in comments (which
  only ever mention siblings, never nesting). Left as-is — not a bug, just
  a previously-undocumented emergent behavior, now written down here.
- **The actual bug**: `SCFCondition.to_core` still computed
  `to_core_type = type_.to_core()` and asserted it wasn't `None` before
  calling `translate_assignment_core_with_ctx` — but `to_core_type` was
  never used for anything else, and `Type.to_core()` (`core.py`) only ever
  recognizes a felt scalar or felt array, returning `None` for any pod or
  struct type. `translate_assignment_core_with_ctx` (called on the very
  next line regardless) already dispatches on pod/struct/array-of-pod/
  struct types independently of `Type.to_core()` — it didn't need this
  check at all. §15 already removed the identical dead check from the
  sibling function `SCFYield.to_core` for the exact same reason, but that
  same §15 entry *mistakenly stated `SCFCondition.to_core` "already
  solves this"* — it never actually did, and two later sessions (including
  §21) rediscovered the resulting crash and logged it as out-of-scope
  without fixing it.

Fixed by deleting the dead `to_core_type`/assert pair (and the now-false
comment above it claiming `translate_assignment_core_with_ctx` "isn't
considered" here, when the very next line calls it) from
`SCFCondition.to_core` — a pure deletion, no behavior change beyond
un-blocking the pod/struct case the surrounding call already handled. Also
removed a leftover debug `print(result)` in the same method (same class of
stray debug statement already cleaned up twice this session, in `pod.py`).

`poseidon3_test_concrete.mlir` now progresses past this crash too (489,456
generated lines, up from 480,056) before hitting a new, unrelated gap: a
`KeyError: '@count'` in `pod.py`'s `PodRead.to_core`/`PodWrite.to_core`
(`ctx.ssa2pod_var[pod_ref][record]`) — a different pod-registration gap,
not investigated further this session.

Added `tests/test_scf_parse.py::TestSCF` coverage: `SCFCondition.to_core`
with a plain felt arg (symmetry/no-regression check), and with a mixed
pod-and-felt arg list mirroring the exact crashing shape — asserting it
produces correct output instead of raising. Full suite: 382 tests, up from
380.

## 23. `scf.while`/`scf.for` own block-arg/induction-variable names: cursor-tagged, same as body-computed names

The user asked to investigate the `KeyError: '@count'` (§22's "Known
pre-existing" note) further, suspecting recursive pod registration (§19)
wasn't working. It wasn't — §19's mechanism is correct. Investigation
(grepping every `scf.while` occurrence declaring `%arg7`/`%arg8` in the real
file, plus direct `ctx.ssa2pod_var` instrumentation during a real
translation run) found something more fundamental: **`scf.while`'s own
block-argument names are never disambiguated across occurrences**, even
though `ctx.ssa2pod_var`/`ctx.var2const`/`ctx.ssa_to_name` are flat,
whole-program dicts keyed by them.

Confirmed directly against the file: three **sibling** `scf.while` loops, all
nested inside one outer while's after-body, each declare their own `%arg8`
block argument with a completely different pod shape — an 8-entry
`@count/@comp/@params`-shaped pod (Ark rounds, line 362466), a 7-entry
`@in`-only-shaped pod (line 362715), and, in a different, deeper-nested
while, a 57-entry `@count/@comp/@params`-shaped pod (MixS rounds, line
364048). `SCFWhile.parse` (`scf.py`) already tags body-*computed* SSA result
names with `_bef{cursor}`/`_aft{cursor}` specifically because "sibling
scf.while blocks... may independently reuse the same LLZK-level SSA numbers"
(§5's fix) — but that rename **deliberately excludes** `init_args`'/
`after_args`' own block-arg names ("after_args names are the declared
entry-point variables of the after region — exclude them so they keep their
original names"), correct for keeping one while's own before/after regions
in sync, but leaving those names globally un-disambiguated *across different
while occurrences*. `SCFFor.parse` has the identical gap for its
`iv`/`iter_args`, and additionally had **no** cursor-tagging at all for its
own body-computed results (unlike `SCFWhile`) — a nested `scf.for`'s names
were only ever disambiguated incidentally, if it happened to sit inside an
enclosing `scf.while` whose own rename recursed into it.

Fixed by extending the *existing* cursor-tagging convention one level
further, rather than inventing a new scoping/save-restore mechanism on
`TranslationContext`:
- `SCFWhile.parse`: a new `block_arg_rename` dict (`name + f"_w{cursor}"`)
  built from `init_args`'/`after_args`' own block-arg names, applied via
  `op.update_variables(...)` over both regions (reaching every reference —
  `scf.condition`/`scf.yield`/`pod.read`/nested constructs — the same way
  `before_rename`/`after_rename` already do), plus direct mutation of the
  `init_args`/`after_args` tuples themselves (they're plain tuples, not
  `Operation`s, so `update_variables` never reaches them). `init_val` (the
  incoming value from the enclosing scope) is deliberately left untouched —
  mirrors the existing asymmetry already in `SCFWhile.update_variables`.
  Keys are provably disjoint from `before_rename`/`after_rename`'s (one is
  op *results*, the other is block-arg *bindings* — under single-assignment
  MLIR a name can't be both), so the new dict is applied independently, no
  merge/ordering concerns. `SCFCondition` needed no code change: it has no
  `update_variables` override, so it inherits the base `Operation`'s, which
  already walks `self.operands` (a property including `self.args`).
- `SCFFor.parse`: the same `block_arg_rename` treatment for `iv`/`iter_args`
  (tagged `_f{cursor}`), plus the missing body-result cursor-tagging it
  never had (mirroring `SCFWhile`'s single-region case). If a `scf.for` sits
  inside an enclosing `scf.while`/`scf.for`, names may end up
  double-suffixed by the ancestor's own rename pass too — harmless, same as
  the already-accepted nested-while double-suffix behavior from §22's
  investigation.
- `struct.py`'s `_build_component_naming_maps`/`while_iter_args` and
  `SCFWhile._extract_step`/`_process_while_variables` both continue to work
  unchanged — verified by reading both: they operate purely on `.name`
  attributes read from the same, now-renamed `SSAVar` objects post-parse,
  with no literal-string-pattern assumptions anywhere in either.

Added `tests/test_scf_parse.py` coverage: updated five existing `.parse()`-
based tests whose literal expected names changed (`test_while_basic`,
`test_while_with_after_block_args`, `test_for_basic`, `test_for_iter_args`,
`test_for_to_core_repeat`); added new regression tests reproducing the exact
bug — two sibling `scf.while`s and two sibling `scf.for`s each reusing a raw
block-arg/iv name, a nested-while variant, and an end-to-end `to_core` test
that parses two sibling whiles sharing "%arg8" with different pod shapes,
runs both through the same registration step `SCFWhile.to_core` itself uses,
and confirms neither's `PodRead` collides with the other's `ctx.ssa2pod_var`
entry (confirmed this fails against the pre-fix code via `git stash` on just
`scf.py`, passes with it restored). Also removed another stray leftover
debug `print(self.result, self.record_name, self.pod_ref.name)` in
`PodRead.to_core`, found while re-instrumenting `pod.py` during this
investigation. Full suite: 386 tests, up from 382.

**This fix is real and necessary — confirmed via the tests above, which
reproduce an actual, independently-verified collision in the real file — but
it does not by itself unblock `poseidon3_test_concrete.mlir`'s specific
crash.** Re-running the same translation after this fix hits the *identical*
`KeyError: '@count'` at the *identical* line count (489,456) as before —
tracing it (see the new "Known pre-existing" bullet below) found a
*different*, previously-undiscovered bug already present at this exact spot
regardless of the block-arg fix. The two are independent: this fix closes a
real, confirmed hole (three sibling whiles reusing `%arg8`); the file's
specific crash is caused by something else that happens to sit at the same
point in the file.

## 24. `ctx.ssa_to_name`/`ctx.ssa2pod_var`/`ctx.var2const` scoped to each `scf.if` branch (correcting §23's "per-iteration" speculation)

The user asked to investigate the `ctx.ssa_to_name` staleness noted above,
explicitly proposing "restart per block region" vs. "rename per iteration"
as candidate fixes. **§23's "likely needs per-iteration scoping" guess was
wrong, and this investigation corrects it with direct evidence** before
picking a fix: re-instrumented `ctx.ssa_to_name` against the real file,
logging `ctx.unroll_index` and full stack traces at every conflicting
write to `"%755_..."`. All three writes happened at `unroll_index == 0` —
within a **single** loop iteration — with stack traces showing 7-9 nested
`SCFIf.to_core`/`_translate_branch` calls (alternating `then`/`else`). This
is a deeply nested `scf.if`/`else` cascade (compiled from a switch-like
`idx_56, idx_55, ..., idx_0` construct), not an iteration boundary at all.
`SCFIf.to_core` always translates *both* branches unconditionally (Core
needs both as real runtime code; the condition is never resolved
statically), so a raw LLZK SSA number gets independently reused across
mutually-exclusive branches — valid under SSA scoping (only one branch
executes at runtime) but a genuine key collision in the three flat,
whole-translation dicts, which have no per-branch scoping. Also directly
ruled out extending `ctx.unroll_index`/`LoopIndexedName` (§10): it only
disambiguates a *value string* at two call sites (`array.py`, `function.py`),
never a *dict key* — structurally incapable of fixing a key collision
between two different SSA definitions sharing one literal name.

Fixed by adding `scoped_branch_registrations` (`core_utils.py`, a
`@contextmanager`): snapshots `ctx.ssa_to_name`/`ctx.ssa2pod_var`/
`ctx.var2const` on entry, restores them on exit — except for whatever the
block itself registered under one of its own declared `results`' component
names (`SSAVar.to_core_component`), which is exactly what a trailing
`scf.yield` writes and must survive. Wrapped around `SCFIf._translate_branch`
(both `then`/`else`) and, for consistency, `SCFExecuteRegion.to_core`'s
single body (not strictly required there — no sibling-branch alternative —
but the same "declared escaping result vs. block-local temporaries" shape).
Since `_translate_branch` is the one universal call site for translating any
`scf.if` branch anywhere in the codebase, this single change transitively
covers every nested `scf.if`, at any depth, inside any construct
(`scf.while`/`scf.for`/another `scf.if`) — matching exactly the deep cascade
found above. `scf.while`/`scf.for`'s own before/after-body pairs are *not*
mutually-exclusive alternatives (both always execute, every iteration), so
they don't need this treatment themselves.

Before finalizing, stress-tested the design (via a Plan agent instructed to
validate/refute, not just review) against the live code:
- Reproduced the exact bug and confirmed the fix resolves it against the
  real `SCFIf`/`PodRead` classes, not a mockup.
- Found a real edge case: a `pod.write` into an *already-existing* key (not
  a declared result) from inside a branch would have its effect reverted by
  the restore. Verified this is currently harmless — every such write's
  registered shape is derived purely from `lhs.name`
  (`f"{lhs.name}_{record}"`), independent of which branch performed it —
  by checking every writer of the three dicts. Documented as an explicit,
  commented assumption in the helper's docstring rather than solved with
  extra machinery, flagging a future op that needs branch-dependent
  mutation of a pre-existing key to extend the allow-list.
- Benchmarked an alternative ("track key-sets, delete only newly-introduced
  keys") that seemed like it should be cheaper — it was actually **2.4-4.3x
  slower** at realistic sizes (CPython's C-level `dict.copy`/`clear`/`update`
  beats Python-level set-tracking + scanning). Shipped the plain
  snapshot/restore version.
- Ran the entire test suite with the exact diff applied before it was
  written into this repo: 386/386 passed, no measurable slowdown.

Added three regression tests to `tests/test_scf_parse.py`
(`test_if_sibling_branches_do_not_leak_ssa_to_name`,
`test_if_escape_hatch_preserves_declared_result_not_branch_local_temp`,
`test_if_sibling_branches_do_not_leak_ssa2pod_var`) reproducing the exact
sibling-branch collision and the escape-hatch case; confirmed all three fail
against the pre-fix code (`git stash` on `scf.py`/`core_utils.py`) and pass
with it restored. Full suite: 389 tests, up from 386.

Re-ran `poseidon3_test_concrete.mlir`: the exact `KeyError: '@count'` this
section set out to fix is gone, but translation now progresses only to
480,107 lines (fewer than §23's 489,456) before a **new, distinct** crash —
see the updated "Known pre-existing" bullet below. This is expected, not a
regression: the fix demonstrably closes the collision it targeted (proven
by the unit tests, independent of this one file), and — per this session's
established pattern (§19→§20→§21→§22→§23) — removing one blocker simply
exposes whatever the *next* one is, at whatever point in the file it
happens to sit.

## 25. `poseidon3_test_concrete.mlir`'s `KeyError` on a member-backed nested pod: semantic names clobbered by raw derived ones

Follow-up to §24's own residual bullet: after §24 fixed the sibling-branch
collision, `poseidon3_test_concrete.mlir` progressed further but still
crashed — `KeyError` on a renamed `%598`-like name inside `PodRead.to_core`
(`ctx.ssa2pod_var[self.pod_ref.name][self.record_name.name]`). Root-caused
with live instrumentation (dict-write tracing + traceback-locals
inspection), then independently re-validated by a Plan agent (monkeypatched
in-process, confirmed against the real file before writing any code).

The crashing shape: `poseidon3_test_concrete.mlir` has a pod-typed
`scf.while` block arg (`arg9`) backing a struct member `"ark"`
(`ctx.input_pod_to_member`, set in `struct.py`'s
`_build_component_naming_maps`). Each of `arg9`'s 8 top-level fields
(`@idx_0`..`@idx_7`) is itself a nested pod (one level deep, its own `@in`
field). Two interacting gaps combined to strand a name nothing could
resolve through:

- `_register_pod_top_level` (`pod.py`) — unlike its sibling
  `_register_nested_pod_vars` — never recursed into a pod-typed field, so
  even when a semantic name like `"ark.idx_7"` was computed, it was never
  registered as its own top-level `ctx.ssa2pod_var` key.
- `translate_assignment_core_with_ctx`'s "Assign pod vars" branch
  (`core_utils.py`) unconditionally rebuilt `lhs`'s whole entry from
  `rhs`'s shape, dispatching purely on whether `rhs`'s own per-field value
  happened to be semantic. `arg9`'s initial value (and every yield-back)
  traces back to a raw-SSA `llzk.nondet` result, so this derived fresh raw
  names (`%arg9_..._@idx_7`) for every field instead of preserving `arg9`'s
  own semantic destination (`"ark.idx_7"`) — clobbering it the very first
  time any field's underlying value wasn't itself semantic.

**Fix** (`pod.py`, `core_utils.py`):
- `_register_pod_top_level` now recurses into pod-typed fields by
  delegating to `_register_nested_pod_vars` (no new helper), so a
  member-backed semantic name is always given its own recursive
  registration the moment it's computed.
- `translate_assignment_core_with_ctx`'s pod-copy branch now (a) lazily
  registers a member-backed `lhs` via `_register_pod_top_level` the first
  time it's assigned (rather than starting from nothing), and (b) prefers
  `lhs`'s own pre-existing semantic destination over deriving/aliasing from
  `rhs`, for every field — fixing both the initial while-copy and every
  yield-back in one change point.
- Bundled a third, adjacent, independently-confirmed bug in the same
  nested-pod machinery: `_allocate_pod_field_storage` allocated a nested
  pod's storage line via `_container_field_var` (which never strips the `@`
  sigil), while `_register_nested_pod_vars`'s own semantic naming does
  strip it — so for a semantic base the registered name and the allocated
  storage line silently disagreed (e.g. `"ark.idx_0_in"` registered vs.
  `"ark.idx_0_@in"` allocated). Added `_resolve_pod_field_var`, which walks
  `ctx.ssa2pod_var` through the field path to resolve the *actually
  registered* name (falling back to `_container_field_var` past the last
  registered prefix, e.g. once a field path crosses into a struct-typed
  field — keeping the plain-struct case byte-for-byte unchanged).

Added regression tests: `tests/test_pod_parse.py` (a direct
`translate_assignment_core_with_ctx` preserve-semantic-dest test with a
chained `pod.read`/`pod.read`, a `PodNew`-with-`init_records` analog, and an
assertion on the *emitted* `array.new` line matching the registered name)
and `tests/test_scf_parse.py` (an end-to-end `scf.while` regression with a
member-backed nested-pod block arg, a raw-named init value, and a
yield-back to a second raw-named pod — asserting the semantic destination
survives both the init-copy and the yield-back). Full suite: 392 tests, up
from 389, all passing.

Re-ran `poseidon3_test_concrete.mlir`: it now translates **to completion** —
4,702,717 lines emitted, no exception at all (not just "a different, later
bug" per this session's established §19→§24 pattern — this is the first
time this file has fully translated).

## 26. `FunctionReturn.parse`: an N-D array return type's own dimension comma silently corrupted by a naive split

While translating `poseidon3_test_concrete.mlir` end-to-end (post-§25), the
emitted Core file contained the literal string `"None"` as a function's
return type: `def @POSEIDON_M_2(%arg0: ff) -> %1: None {` (and identically
for `@POSEIDON_P_3`). Both are pure functions (`poly.template` with no
`struct.def`) returning a `!array.type<17,17 x !felt.type<...>>` (a 17×17
matrix).

Root cause: `FunctionReturn.parse` (`function.py`) split its type-annotation
string on every comma (`m["types"].split(",")`) instead of using the
codebase's existing bracket-aware `split_top_level_commas` (already used by
`FunctionDef.in_args` a few lines away, and designed for exactly this). A
single returned array type's own dimension list (`"17,17"`) contains a
comma that is *not* a type separator — the naive split broke
`"!array.type<17,17 x !felt.type<...>>"` into two malformed fragments
(`"!array.type<17"` and `"17 x !felt.type<...>>"`); `zip` in
`poly.py`'s `_register_pure_function` then paired the return operand with
only the *first*, malformed fragment. `Type("!array.type<17").to_core()`
matches neither the array case nor the felt-scalar case, so it silently
returned `None` — which then leaked into the emitted signature via
`FunctionDef.to_core`'s f-string.

**Fix** (`function.py`): `FunctionReturn.parse` now builds its `types` list
with `split_top_level_commas(m["types"])` instead of `m["types"].split(",")`
— a one-line change, since `split_top_level_commas` was already imported.

Added regression tests: `tests/test_function_parse.py`
(`test_return_nd_array_type_not_split_on_dimension_comma`, asserting the
parsed type and its `to_core()` directly) and `tests/test_poly_parse.py`
(`test_poly_template_to_core_pure_function_nd_array_return`, an end-to-end
`PolyTemplate.to_core()` check asserting `"None"` no longer appears in the
output and the correct `arr<289>` signature is emitted). Full suite: 394
tests, up from 392, all passing.

Re-ran `poseidon3_test_concrete.mlir` again: still translates to completion
(4,702,717 lines), and the emitted file now contains zero occurrences of the
literal string `"None"` (verified by grepping the full output) — both
`@POSEIDON_M_2` and `@POSEIDON_P_3` now emit `-> %1: arr<289> {`.

## 27. `global.def`/`global.read`: array-literal parsing bug, plus both stubs implemented

A regenerated `poseidon3_test_concrete.mlir` (circom-llzk now hoists a
struct's repeated round-constant tables into a module-level `global.def`,
read back via `global.read` at each use site, instead of embedding the same
literals inline via `felt.const` at every occurrence as the version §19-26
tested against did) crashed immediately: `GlobalDef.parse` (`global_.py`)
raised `ValueError`. Its regex captured the initial value with `(?P<val>\S+)`
— a single non-whitespace token — which only ever worked for the existing
scalar test cases (`= 0`, `= 17`); a real array value is a bracketed,
comma-separated list of felt-attribute literals spanning many tokens
(`[#felt<const N : <"bn128">> : !felt.type<"bn128">, ...]`). Separately, both
`GlobalDef.to_core` and `GlobalRead.to_core` were still `NotImplementedError`
stubs.

Fixing the parse also surfaced an ordering wrinkle: `global.def` can appear
*textually after* the struct that reads it (confirmed in the file — a
`struct.def` at line 318800 reads `@vcp_array_const_0` at 318805, but that
global isn't declared until line 318861, right after the enclosing
`poly.template` closes). Since these are module-level symbols, not SSA, this
is legal, but it means every `global.def`'s value must be registered before
any struct body is translated, not in body order — the identical shape of
problem `ModuleOp.to_core` already solved once for pure-function templates
(`_register_pure_function`, §16), so the fix follows that same pattern.

**Fix:**
- `GlobalDef.parse`'s regex now captures the value greedily (`.+`, not `\S+`)
  so the whole bracketed literal is kept intact.
- New helpers in `global_.py`: `_parse_felt_literal` (a plain int, or a
  `#felt<const N : ...>`-wrapped one, via a small regex) and
  `_parse_global_value` (dispatches to a flat `List[int]` for a bracketed
  array — split on top-level commas via the existing `split_top_level_commas`,
  since each element carries its own nested `<...>` — or a scalar `int`
  otherwise), and `_register_global_def`, which stores the parsed value in a
  new `ctx.global2value: Dict[str, Union[int, List[int]]]` (`core.py`).
  Deliberately parses off the value's own bracket syntax rather than the
  declared type, so it works the same regardless of what type annotation the
  `global.def`/`global.read` pair happens to carry.
- `GlobalDef.to_core` calls `_register_global_def` and emits nothing (mirrors
  `FunctionReturn.to_core`'s no-op-emission idiom); `ModuleOp.to_core`'s
  existing pre-pass loop (§16) now also calls `_register_global_def` for
  every top-level `GlobalDef`, exactly mirroring `_register_pure_function`'s
  own idempotent-registration-called-twice pattern (dict assignment is
  naturally idempotent here, so no guard was needed).
- `GlobalRead.to_core` looks up the registered value and translates it "as an
  assignment," matching the existing conventions for each shape: a scalar
  felt becomes `"{result} = {value}"` plus a `ctx.var2const` registration
  (mirroring `FeltConst.to_core`); a uni- or multi-dimensional array (detected
  via the existing `array_felt_first_dimension`, which returns the flattened
  total size regardless of dimensionality) becomes `array.new {dim} {result}`
  followed by one `array.write {value} {result}[{i}]` per element, literal
  values written directly into each slot (mirroring `ArrayNew`'s own
  literal-initialization path, §13) — no special-casing needed between 1-D
  and N-D, since the source list is already row-major flattened.

Added `tests/test_global_parse.py` coverage: a `GlobalDef` parse test for the
bracketed array literal, `to_core` tests for `GlobalDef` (scalar and array,
asserting `ctx.global2value`) and `GlobalRead` (scalar, 1-D array, and a 2-D
array confirming the total-size flattening isn't special-cased differently
from 1-D). Full suite: 400 tests, up from 394, all passing.

Verified end-to-end against the regenerated `poseidon3_test_concrete.mlir`:
`LLZKParser.parse()` no longer raises, and `to_core` fully drains (over 1.1M
generated lines) with all four registered globals resolving correctly —
confirmed `def @Ark_0` emits `array.new 81 %0` followed by direct literal
`array.write` lines for its global round-constant table, with the struct's
own local array (`array.new 3 %nondet`) unaffected.

`GlobalWrite.to_core` remains an unimplemented stub — out of scope here, not
exercised by this file (no `global.write` occurrences).

## 28. Tied nested loops: a nested loop's bound resolving only once an
    enclosing loop is unrolled

`babypbk_test_concrete.mlir` (lines 6274-6379): an outer `scf.while` (2
concrete iterations over `%arg6`, already unrolled because its body contains
`function.call`s) computes, per iteration, `%17 = scf.if %16 -> (ff) {
yield 249 } else { yield 4 }` (selecting a constant based on comparing
`%arg6` against `1`), then derives `%20 = (%17 - 1) uintdiv 3 + 1` from it
via plain `felt` arithmetic. Two inner `scf.while` loops — each themselves
containing a `function.call`, so each also needs to unroll — are bounded
directly by `%17` and by `%20 * 3` respectively.

This crashed (`NotImplementedError: Cannot unroll a while loop whose body
contains a function.call when its iteration count is symbolic...`) because
three gaps compounded:

- `FeltBinary`/`FeltUnary.to_core` (`felt.py`) never wrote into
  `ctx.var2const`, even when both operands were already known constants —
  only `FeltConst`, `ArithConst`, `global.def`, `ArrayDim`, and
  copy-assignment (`translate_assignment_core_with_ctx`) did. So `%18`/`%19`/
  `%20` never became known constants even once `%17` was.
- `BoolCmp.to_core` (`bool.py`) never wrote into `ctx.var2const` either — a
  decidable condition's own boolean result was never itself treated as a
  known value.
- `SCFIf.to_core` (`scf.py`) had a latent, previously-invisible bug: it
  always translates both branches unconditionally (correct — Core has no
  compile-time branching), but `ctx.var2const` for the if's own declared
  result ended up holding *whichever branch was translated last* (the else
  branch, via `scoped_branch_registrations`' snapshot/restore-except-
  declared-results mechanism), regardless of the condition's actual value.
  Confirmed directly: with `%16` forced `true` (then-branch is the real
  one, value should be `249`), the pre-fix code returned `4`. This was
  invisible before this fix only because nothing yet folded an `scf.if`
  result through arithmetic into a loop bound — once `FeltBinary` folding
  was added, it would have become *actively* wrong the moment it was
  relied on, not just untested.

The existing free-variable resolution for `scf.while` bounds
(`infer_n_repetitions_from_expressions`/`_infer_from_comparison`,
`core_utils.py`) already resolves an unresolved free name by checking
`ctx.var2const` — so fixing the three gaps above was sufficient; no changes
were needed to that machinery's logic. `SCFFor`'s bound check
(`ctx.var2const.get(...)` + `assert`) benefits the same way, automatically,
with no changes to `SCFFor.to_core` either.

**Fix:**
- `FeltBinary.to_core`/`FeltUnary.to_core` (`felt.py`) now fold into
  `ctx.var2const` via the op's own existing `to_function()` (already used by
  `core_utils.py`'s symbolic-step machinery) when all operands are known,
  guarded by a narrow `try/except (ZeroDivisionError, ArithmeticError)` — an
  `scf.if` always translates *both* branches, including one that may be
  dead-for-this-iteration precisely because a guard prevents e.g. a
  division-by-zero in the real circuit; eagerly folding it must not crash
  translation.
- `BoolCmp.to_core`/`BoolBinary.to_core`/`BoolNot.to_core` (`bool.py`) gained
  the same fold (new `to_function()` on each, mirroring `felt.py`'s
  `_BINARY_FNS`/`_UNARY_FNS` pattern), representing the result as `1`/`0`
  (matching the existing `arith.constant true/false` convention).
  `BoolBinary`/`BoolNot` folding isn't needed by this example (its condition
  is a bare `BoolCmp`) but closes the same gap for a `bool.and`/`bool.not`-
  gated `scf.if` elsewhere, at essentially no cost.
- `SCFIf.to_core` (`scf.py`) now captures each branch's own post-translation
  `ctx.var2const` value for every declared result key right after that
  branch's `_translate_branch` call, then — after both branches — keeps the
  *taken* branch's value if `ctx.var2const.get(self.condition.name)` is
  itself known, or explicitly pops the key if it isn't (rather than leaving
  whatever the last-translated branch happened to compute). No change to
  what Core text is emitted, only to this compile-time side channel.

**Optimization** (avoiding rediscovering "is this variable free" on every
outer-loop iteration, per explicit request): the structural parts of
`SCFWhile._extract_step` and of the `_contains_function_call`
unroll-vs-repeat check are pure functions of the already-parsed body and
never change between iterations — only the *value* lookup varies.
- `_contains_function_call(self.body)` (`SCFFor`) /
  `_contains_function_call(before_body) or _contains_function_call(after_body)`
  (`SCFWhile`) is now computed once in `__init__` and cached
  (`self._contains_call` / `self._needs_unroll`); `to_core` reads the cached
  attribute. Safe to compute eagerly — it's a pure `isinstance` walk over
  the already-fully-parsed body, unaffected by any later SSA renaming.
- `SCFWhile._extract_step`'s construction of `var2expression`/
  `condition_var` (the `_process_while_variables` backward walk plus the
  yield-linking and cond_arg-linking loops) is now split into a **lazily**
  memoized `self._structural_analysis()`. Lazy is required, not just an
  optimization detail: at `__init__` time (during parsing), an *enclosing*
  `scf.while`/`scf.for`'s own `before_rename`/`after_rename`/
  `block_arg_rename` has not run yet — `update_variables` mutates this
  object's already-built `before_body`/`after_body` SSAVar names in place,
  from the outside, only after `__init__` returns. Caching eagerly would
  freeze `var2expression` against pre-rename names, permanently mismatched
  with the post-rename names `ctx.var2const` is actually populated under at
  translation time. `_extract_step` now takes a fresh shallow `dict(...)`
  copy of the cached template on every call before handing it to
  `infer_n_repetitions_from_expressions` — required, not cosmetic:
  `_infer_from_comparison` mutates its `var2expression` argument in place to
  fold a newly-resolved free variable in as a constant leaf, and reusing the
  same cached dict object across outer-loop iterations would let one
  iteration's resolved value leak into the next. Confirmed by direct repro
  (see commit history / test below): reusing one dict object across two
  calls with different bound values returned the *first* call's value both
  times; a fresh copy per call correctly returned each call's own value.

Verified via a direct monkey-patch repro against the real classes before
writing any of the above into the codebase (arg6=0 → `%17=249, %20=83`;
arg6=1 → `%17=4, %20=2`; a genuinely non-decidable condition correctly
leaves no stale value), then again against the actual fix once applied.
`babypbk_test_concrete.mlir` now progresses from 251,173 generated lines
(the old `NotImplementedError` crash site) to 269,307 lines before hitting a
**different, unrelated, pre-existing gap**: a `KeyError` in `PodRead.to_core`
(`ctx.ssa2pod_var[pod_ref][record]`) on a pod-typed variable from a nested
loop iteration that was never registered — matching this file's own
previously-documented "pod-variable-tracking gap in unrolled nested-loop
bodies, unrelated to loop-iteration counting" note from an earlier session.
Expected, not a regression, per this project's established pattern: fixing
one blocker exposes whichever gap sits next in the file.

Full pytest suite: 433 tests, up from 400 (new coverage in
`tests/test_felt_parse.py`, `tests/test_bool_parse.py`, and
`tests/test_scf_parse.py`, including a canonical hand-built nested-`scf.while`
regression mirroring this exact shape, and a dedicated test proving the
memoization's shallow-copy-per-call is load-bearing — confirmed to fail if
the copy is dropped). Confirmed all new `SCFIf`/`FeltBinary`/`BoolCmp` tests
fail against the pre-fix code and pass with it restored.

Verified via a full sweep of every `circomlib_examples/*.mlir` file (49 of
50; `poseidonex_test_concrete.mlir` hit this sweep script's own 90s
per-file timeout post-fix — a sweep-script limitation on a ~56MB file, not
investigated further, and not compared against its pre-fix timing): of the
16 files that fail post-fix, 13 fail with the *exact same* error before and
after (this fix had no effect on them — they hit an unrelated, still-open
gap, such as the unsupported `ne`
predicate or a `SymbolicSteps`-plus-call combination rooted in an external
function parameter rather than an enclosing loop's own induction
variable); 3 (`babypbk_test_concrete.mlir`, `eddsamimc_test_concrete.mlir`,
`eddsaposeidon_test_concrete.mlir`) now progress further before hitting a
different, unrelated gap, as described above. No previously-passing file
started failing.

One file that *passed both before and after* — `escalarmulany_test_concrete.mlir`
— produces different output: the same "segmented scalar multiplication"
shape as `babypbk_test_concrete.mlir` (an `scf.if`-selected constant
feeding a derived loop bound), just not combined with a
function-call-plus-symbolic-bound crash. Diffing the two full outputs
showed the post-fix version contains one additional, complete unrolled
loop-body copy mid-file (`SegmentMulAny_9`/`SegmentMulAny_10` call count:
428 → 514) — i.e. **this file was silently under-counting a loop's
iterations and dropping a whole segment's worth of Core code before this
fix**, without ever crashing. This wasn't part of the motivating bug report
but is the same root cause, confirmed as a genuine correctness improvement
(not a regression) by inspecting the diff directly: the inserted block is a
structurally-complete extra copy of the existing per-segment logic, not
garbage or a duplicate. A handful of other, smaller passing files
(`mux1_1_concrete.mlir`, `mux4_1_concrete.mlir`, `sum_test_concrete.mlir`,
`mimc_sponge_hash_test_concrete.mlir`) were diffed byte-for-byte and are
unchanged, confirming the fix is a true no-op wherever this exact pattern
isn't exercised.

## 29. Loop unrolling removed entirely — naming deferred to `llzk_cli`

Per an explicit product decision, subcomponent/signal naming for anything
touched by a loop is no longer this translator's job — it's resolved
afterwards by `llzk_cli` (the `-ru` flag removal in commit `5a3e46a`,
"Remove -ru flag to avoid missing signal names," was the first, already-
landed piece of this). `scf.for`/`scf.while` go back to translating their
body as one generic iteration only — never unrolling into N literal
per-iteration Python-side copies — while still correctly determining the
bounded number of iterations (a concrete int, or a `SymbolicSteps` Core
expression when the bound isn't statically known but is still computable,
per §17-§18). This removes the entire `_contains_function_call`-driven
"unroll vs. repeat" decision, `ctx.unroll_index`, and the `LoopIndexedName`
per-iteration member-naming mechanism it fed (§10-§13 in this file;
decisions 10-14 in `DECISIONS.md`, now superseded) — none of it is needed
once no loop is ever unrolled.

**What was removed** (`scf.py`, `core.py`, `array.py`, `function.py`):
- `_contains_function_call` (whole function), `SCFFor._contains_call`,
  `SCFWhile._needs_unroll`, and the unroll-vs-repeat branch splits in both
  `SCFFor.to_core`/`SCFWhile.to_core` — each now always takes what used to
  be the "no call" branch (single generic body, wrapped in `repeat`).
  `SCFWhile.to_core`'s `if needs_unroll: raise NotImplementedError(...)`
  guard (inside the `SymbolicSteps` case) is gone too — a symbolic bound now
  always drives `repeat %steps_N { ... }` regardless of whether the body
  contains a `function.call`, since there's no unroll path left to reject
  it for.
- `TranslationContext.unroll_index` and the `LoopIndexedName` dataclass
  (`core.py`) — `ArrayRead._semantic_base`/`FunctionCall._member_hint` are
  now always `Optional[str]` (previously `Optional[Union[str,
  LoopIndexedName]]`); their two consumers (`ArrayRead.to_core`,
  `FunctionCall.to_core`) dropped the `isinstance(x, LoopIndexedName):
  x.resolve(ctx.unroll_index)` branch entirely.
- `SCFWhile`'s memoization added alongside §28's fix
  (`_structural_analysis`/`_cached_structural_analysis`, and the
  `_contains_call`/`_needs_unroll` caching) — it was justified only by
  "avoid redundant work on every outer-loop iteration during unrolling," a
  concern that no longer exists once no loop unrolls (each instance's
  `_extract_step` now runs at most once regardless). Folded back into a
  plain, uncached `_extract_step`, matching its pre-memoization shape.

**What was explicitly kept, unchanged**: §28's `FeltBinary`/`FeltUnary`/
`BoolCmp`/`BoolBinary`/`BoolNot` constant folding into `ctx.var2const`, and
the `SCFIf.to_core` branch-value bug fix — neither is "unrolling
complexity": the `SCFIf` fix corrects a pre-existing, independent
correctness bug (confirmed via direct repro in §28), and the folding is a
generically useful constant-propagation improvement. Also kept, contrary to
a first-pass reading of "resolving member names" as something to strip
out entirely: `_fold_index_constants`, `_find_array_component_bases`,
`_annotate_array_component_reads`, `_annotate_input_array_reads`,
`_annotate_function_calls`, and the `while_iter_args`/`trace_source`
block-arg aliasing in `struct.py`'s `_build_component_naming_maps` — these
determine whether a *source-level* array index is a compile-time constant
(e.g. `array.read arr[2]`) and alias a while's own block-arg name to its
semantic base, both independent of whether this translator ever unrolls a
loop. Only the "index isn't a compile-time constant" branch of the two
`LoopIndexedName`-producing functions changed, from constructing a
`LoopIndexedName(base)` wrapper to just using the bare string `base`
directly — a **pure simplification with zero output change**, since
`LoopIndexedName(base).resolve(None)` already returned the bare `base`
string, and `ctx.unroll_index` is now always `None` (nothing sets it).

**Verified**: full pytest suite green (423 tests, down from 433 — mostly
straight deletions of now-inapplicable unroll-decision/`LoopIndexedName`
coverage in `test_scf_parse.py`, `test_array_parse.py`, and
`test_function_parse.py`, each replaced 1:1 or 2:1 with a smaller
equivalent covering the new "always translates like a call-free body"/
"no longer raises" behavior; `test_struct_parse.py`'s two affected tests
were edited in place, so its count is unchanged). Full sweep of every
`circomlib_examples/*.mlir` file (49 of 50; `poseidonex_test_concrete.mlir`
previously hit the sweep script's own timeout and is included below since
it now completes): **zero regressions** — every file that previously
translated successfully still does (with substantially more compact
output for any file with an unrolled loop, as expected — e.g.
`aliascheck_test_concrete.mlir` dropped from 5562 to 251 generated lines;
the four `binsub_test*` variants, which previously emitted differently-
sized output depending on their bit-width-driven trip counts, now all
collapse to the identical, compact 361-line shape). Two direct, positive
effects of removing the unroll-vs-symbolic-bound conflict:
- `escalarmulw4table_concrete.mlir` and its `_test`/`_test3` variants
  (previously blocked by the exact `NotImplementedError` documented below)
  now translate to completion.
- `poseidonex_test_concrete.mlir` (previously timed out under the sweep
  script's 90s budget, likely because unrolling inflated its output) now
  completes in well under that budget.

`escalarmul_min_test_concrete.mlir`/`escalarmul_test_concrete.mlir`/
`escalarmul_test_min_concrete.mlir`/`pedersen_test_concrete.mlir` newly
progress past their old `NotImplementedError` into the same pre-existing
pod-variable-tracking `KeyError` already documented for
`babypbk_test_concrete.mlir` — expected, not a regression, per this
project's established pattern.

## 30. `signal_renaming.py`: per-iteration SMT variable naming, implemented

With loop unrolling removed (§29), a component instantiated inside a loop
is called exactly once, textually, in the `.core` output, even though it
executes N times at runtime — disambiguating *which* concrete SMT variable
binding belongs to which iteration is now `llzk_cli`'s job, not this
translator's. `llzk_cli` already annotates each concrete call site in its
emitted SMT formula with a `:meta-data "call ... (...) to ..."` triple plus
`:in-vars-info "{...}"`/`:out-vars-info "{...}"` payloads (JSON-encoded
maps from a call's core-level signal names to the actual SMT variable(s)
bound for that one occurrence) — one triple per concrete call, in document
order.

`src/execution/signal_renaming.py` (a skeleton already sketched, with all
three extraction helpers as `pass` stubs and two indexing bugs in the
driver) is the post-processing step that turns this into the final
per-macro `vars_info`: for a component called N times inside a loop (an
array-of-components member, i.e. one whose `member_to_struct`-derived
`components_info` already has `#i`-suffixed keys — unrelated,
pre-existing, unaffected by this work), add `vars_info` entries
`"{component}#{i}.{signal}": smt_var` for each of its N occurrences,
without touching the existing flat (ambiguous, last-occurrence-wins)
entry.

**Implemented, in the file's existing structure:**
- `extract_calls`/`extract_vars_info_from_concrete_call` share one
  compiled regex (`_CALL_ANNOTATION_RE`) matching the
  `:meta-data/:in-vars-info/:out-vars-info` triple as a unit, using the
  standard "quoted string with escapes" group `(?:[^"\\]|\\.)*` for each
  payload — required, not cosmetic: confirmed directly against the real
  formula that a plain `[^"]*` stops at the payload's first *escaped*
  quote, not its true closing one, since the payload is itself
  JSON-encoded and so carries one extra level of `\"` escaping once
  `formula` itself has already been JSON-decoded. `extract_calls` filters
  to matches whose meta-data starts with `"call "`. Decoding a payload is
  `json.loads(codecs.decode(raw, "unicode_escape"))` — confirmed directly
  against the real payload text that this works with **no** `.strip('"')`
  needed (the stub's own hint comment), because capturing the payload
  *without* its surrounding quotes in the first place means there's
  nothing left to strip.
- `extract_component` parses `"call <callee> (<inputs>) to <outputs>"` and
  returns the text before the first `.` in whichever input/output is
  `component.signal`-shaped; `warnings.warn(...)` + returns `None` for
  metadata that doesn't parse at all, or where nothing is dotted (e.g. a
  macro's own top-level `main(...)`/template-instantiation call, whose
  inputs/outputs are plain names) — exactly the stub's own instruction.
- `process_components`: fixed the two indexing bugs found while reading
  the real JSON schema (macros live at `smt_json["macros"][macro_name]`,
  not `smt_json[macro_name]`; a new entry is written to
  `extended_smt_json["macros"][macro_name]["vars_info"]`, not
  `extended_smt_json["macros"]["vars_info"]`). Skips a call outright when
  `extract_component` returns `None`. Replaced the original's unescaped
  `re.sub(f"{component_name}\.", "", core_var)` prefix-strip with a
  `startswith` check + plain slice (skips, rather than crashes on, a
  `core_var` that doesn't share the call's component prefix — a case the
  original's `re.sub` would have silently mishandled rather than a real
  observed failure, but worth guarding since nothing else validates that
  invariant). Everything else (the per-macro `Counter`, the
  `f"{component}#{i}" in components_info` membership gate, the
  unconditional counter increment) is exactly the sketch, once the bugs
  above are fixed.

**Verified two ways.** Unit tests per function
(`tests/test_signal_renaming.py`, new — `TestSignalRenaming`, since the
stub's `class SignalRenaming` wouldn't be pytest-collected even completed)
using both synthetic strings and the *exact* real fragment text captured
from `tests/aux_files/ternary_two_calls_concrete.mlir`'s generated JSON.
Then end-to-end, twice: (a) a trimmed-but-real `process_components` test
built from that file's actual `components_info` and its 4 real call
fragments (not the full ~50KB formula, which is 99% unrelated SMT
clauses); (b) the full real pipeline, run live
(`src/llzk2core.py -s tests/aux_files/ternary_two_calls_concrete.mlir`,
actually invoking `lean/llzk_cli`) plus a handful of other loop-heavy
examples (`ternary_concrete.mlir`, `three_subcomponents_array_concrete.mlir`,
`mux2_1`/`mux3_1`/`mux4_1_concrete.mlir`). All ran cleanly (only the
expected, correct `main`-call warning). `ternary_two_calls_concrete.mlir`'s
`@Num2Ternary_1` macro gained exactly the 8 entries the user specified:
`Num2Bits_17_364#0.in`/`#0.out`/`#1.in`/`#1.out` and the same for
`Num2Bits_18_416`. `ternary_concrete.mlir` (the original single-array
example from earlier sessions) gained the analogous
`Num2Bits_16_325#0.in`/`#0.out`/`#1.in`/`#1.out`.
`three_subcomponents_array_concrete.mlir` is a valuable negative check: its
array-of-components members use **compile-time-constant** indices, so its
`.core`/SMT call sites are *already* uniquely named per instance
(`last_0.in1_last`/`last_1.in1_last`, decision 1's underscore convention —
a different mechanism entirely from this `#i` one) — correctly produced
**zero** new entries, since `extract_component` derives `"last_0"`/
`"last_1"` from those already-distinct names, and neither
`"last_0#0"` nor `"last_1#0"` is a key in `components_info` (which only
has `"last#0"`/`"last#1"`), so the membership gate correctly skips them.
This is the same "arrays of components already handled elsewhere don't
need this" filter working as designed, not a special case.

Full pytest suite: 441 tests, up from 423 (18 new).

## 31. `translate_assignment_core_with_ctx`'s pod branch: dispatch made
    type-driven instead of registration-driven, fixing a broken `.core`
    file for `poseidon3_test_concrete.mlir`

The user reported that translating `poseidon3_test_concrete.mlir` and
running the result through `llzk_cli` failed with:

```
seArrayCopy: failed to get array variable: Variable '%602_aft328575_aft328385#1_@idx_0' not found
```

i.e. the emitted `.core` file itself was broken — it contained an
`array.copy` referencing a variable that was never allocated anywhere.
Reproduced directly (`python3 src/llzk2core.py -s
poseidon3_test_concrete.mlir`, which runs `llzk_cli` as its last step) and
root-caused with a monkeypatch trace on `translate_assignment_core_with_ctx`.

**Root cause.** `@ark` (a struct member) is a pod with named fields
`@idx_0`..`@idx_7`, each itself a nested pod
(`!pod.type<[@count: index, @comp: !struct.type<@Ark_N::@Ark_N<[]>>, @params: !pod.type<[]>]>`,
the "counting pod" shape from §19/§9a). The file has a deep
`scf.if`/`scf.else` cascade (an idx-selector switch, same shape as §24)
that reassigns this pod one level of nesting at a time. The "Assign pod
vars" branch of `translate_assignment_core_with_ctx` (`core_utils.py`)
only recursed into a pod's fields when its **source value was already a
registered `ctx.ssa2pod_var` key**:

```python
elif rhs.name in ctx.ssa2pod_var:
```

— unlike the `!struct.type` branch and the array-of-pod/struct branch
immediately above it in the same function, both of which are
unconditionally type-driven. When one nested `scf.if`'s own recursive call
(this branch calls itself per-record, via `dest = f"{lhs.name}_{record}"`)
produced a fresh pod-typed name that was itself never registered — because
*its own* source (one level deeper) also wasn't registered at that point
— the recursive call silently fell through every branch to the generic
scalar/`array.copy` fallback at the bottom of the function instead of
recursing into `@count`/`@comp`/`@params`. Traced directly: this happened
identically at every level of the cascade (`%603...#1` → `%602...#1` →
`%601...#1`, confirmed via instrumentation logging each fallthrough), each
one flattening one level too short and never registering its own `dest`
either — compounding down the chain. Confusingly, *other* branches of the
same cascade (the ones that actually update one `@idx_N` slot) correctly
flatten all the way to `@count`/`@comp_@out`, via the unrelated "counting
pod" bulk-copy mechanism in `struct.py` — so the same pod ended up
flattened to different depths depending on which branch of the cascade
produced it, and the shallow ones referenced storage that was never
allocated.

**Fix** (`core_utils.py`, `translate_assignment_core_with_ctx`): the
"Assign pod vars" branch now also triggers when `type_` itself is a plain
pod type (anchored: `type_.name.strip().startswith("!pod.type")`), not
only when `rhs.name` is already registered; when `rhs.name` isn't
registered, it's lazily registered first via the existing, already-tested
`_register_pod_top_level(ctx, rhs.name, _parse_pod_fields(type_.name))`
(`pod.py`) — the same on-demand-registration pattern §25 already uses for
`lhs` a few lines below, now given to `rhs` too. Once `rhs.name` resolves
to a real entry, the existing per-record recursion already flattens
correctly at every depth, since every level's own recursive call now
registers its own `dest` the same way — the fix is self-healing at any
nesting depth, not just the first one. See `DECISIONS.md` §21 for why this
dispatches on `type_` rather than on prior registration, and why that
principle is worth applying to any future call site with the same shape.

Verified: added `tests/test_core_utils.py::TestAssignPodVarsTypeDriven`
(three tests — full flattening with neither side pre-registered, recursive
registration of both `rhs` and the nested `@comp`-derived pod at every
level, and a no-regression check that a pre-registered `rhs` still takes
this branch exactly as before); confirmed the first two fail against the
pre-fix code and pass with it restored. Full pytest suite: 444 tests, up
from 441, all passing (one pre-existing, unrelated failure in
`test_signal_renaming.py::test_extract_component_no_dot_anywhere_warns_and_returns_none`
is present identically before and after this change — not investigated,
out of scope).

Re-ran the full real pipeline on `poseidon3_test_concrete.mlir`
end-to-end: the `array.copy %603..._@idx_0 %602..._@idx_0`-shaped bogus
lines are gone from the emitted `.core` (0 occurrences, previously
present), `llzk_cli`'s symbolic execution completes with no error
(previously failed with `seArrayCopy: ... not found`), and the full
pipeline (translation → `llzk_cli` → SMT JSON post-processing) runs to
completion.

## 32. `ctx.ssa2pod_var`/`ctx.var2const` never cleared between functions —
    cross-struct SSA-name collisions, fixed in `FunctionDef.to_core`

The user asked to check whether `pedersen_test_concrete.mlir` hits the same
bug as §31, and whether the "type-driven, not registration-driven" dispatch
principle from that fix generalizes across the codebase's pod handling.
Reproduced directly: `pedersen_test_concrete.mlir` crashed with `KeyError:
'@in'` inside `PodRead.to_core` (`pod.py:351`), during a struct's plain
top-level `@compute` body — no loop involved, unlike §31.

**Root cause — a different bug, not the same class as §31.** Traced with
instrumentation (logging every `ctx.ssa2pod_var` write/read touching a
specific colliding SSA name). LLZK/MLIR SSA numbers restart from
`%0`/`%1`/`%2`/... independently in *every function* — `%5` in one struct's
`@compute` and `%5` in a completely unrelated struct's own `@compute` are
different values that just happen to share a name. `ctx.ssa_to_name` and
`ctx.input_pod_to_member` are already correctly cleared around each
struct's compute (`struct.py`'s `StructDef.to_core`, both before and
after) — but `ctx.ssa2pod_var` and `ctx.var2const` are flat,
whole-translation dicts that were **never cleared anywhere**. Concretely:
struct `@EscalarMul_65`'s own `@compute` registers `ctx.ssa2pod_var["%5"]`
(shape `{@in, @sel}`, its own `windows$inputs` pod). Later, unrelated
struct `@EscalarMul_129`'s own `@compute` *also* produces a `%5` — this
time its `windows` counting-pod (`{@count, @comp, @params}`) — and reads
one of its own fields (`%6 = pod.read %5[@in]`) one statement after
`%5` itself was reassigned (via §31's now-type-driven "Assign pod vars"
branch, correctly, to the `{@count,@comp,@params}` shape) — because the
value it was read from, `%2#1`, was *itself* already a stale cross-struct
leftover one level up (`%2` being an even more common low SSA number,
reused in nearly every struct).

**Verified this is the actual mechanism**, not a guess: a standalone script
monkeypatching `StructDef.to_core` to additionally call
`ctx.ssa2pod_var.clear()`/`ctx.var2const.clear()` at its start made
`pedersen_test_concrete.mlir` translate to completion (168,728 lines, no
crash) with zero other changes.

**Answering the generality question directly**: no, this is *not* fixable
by extending the §31 type-driven-dispatch principle to
`PodRead.to_core`/`PodWrite.to_core` (`pod.py:351`, `438`) — both are still
100% registration-driven (`ctx.ssa2pod_var[pod_ref.name][record]`, no
`.get()`, no fallback), unlike the now-type-driven branches in
`translate_assignment_core_with_ctx`. But adding a type-driven fallback
there would be the *wrong* fix and would make failures quieter-and-wrong
rather than loud-and-wrong: unlike "Assign pod vars" (which is *defining* a
fresh destination, so synthesizing a name from `type_` is exactly correct),
a `pod.read`/`pod.write` reads from storage that must already exist —
synthesizing a name when `pod_ref` isn't registered would silently
reference storage nothing ever allocated, the same class of bug as §31
reintroduced from the opposite direction. The two ops' own type annotations
(`self.pod_type`, `self.result_type`/`self.value_type`) are useful only as
a *consistency check*, not a substitute value source. The real fix here is
scope lifetime, not dispatch logic — and it isn't pod-specific:
`ctx.var2const` has the identical flat, never-cleared shape and is exposed
to the same class of collision for constant folding (silently wrong folded
values from a stale cross-struct entry, not yet observed crashing, but the
same root cause), so it was fixed at the same time.

**Fix** (`src/llzk_dialects/function.py`, `FunctionDef.to_core`): added
`ctx.ssa2pod_var.clear()` and `ctx.var2const.clear()` at the very start,
before anything else. Anchored here rather than in `StructDef.to_core`
(where `ssa_to_name`/`input_pod_to_member` are already cleared) because:
`FunctionDef` is LLZK's own `IsolatedFromAbove` scope boundary per its own
docstring/traits, so this is the semantically correct place independent of
the empirical fix; it's the single common entry point for *every*
translated function body, both a struct's `@compute` (via
`StructDef.to_core` → `compute_op.to_core`) and a bare pure function
(`poly.template` wrapping a `function.def` directly, §16) — `StructDef.to_core`'s
own clearing only covers the struct path; confirmed `FunctionDef.to_core`
is never called recursively/nested (a `function.call` doesn't re-enter the
callee's own `to_core`), so a plain clear at its start can't clobber an
enclosing call's state.

Added `tests/test_function_parse.py::TestFunction::test_to_core_clears_stale_ssa2pod_var_and_var2const_from_a_prior_function`
— pre-registers `ctx.ssa2pod_var["%5"]`/`ctx.var2const["%5"]` with a
foreign shape before calling `to_core` on a small `FunctionDef` that itself
defines and reads its own, differently-shaped `%5`; asserts the foreign
entry doesn't leak in. Confirmed it fails against the pre-fix code (leaves
the stale `var2const` entry live) and passes with the fix restored. Full
pytest suite: 445 tests, up from 444, all passing (the one pre-existing,
unrelated `test_signal_renaming.py` failure is unchanged).

**Verified end-to-end**: `pedersen_test_concrete.mlir` no longer crashes in
Python; `poseidon3_test_concrete.mlir` re-confirmed unaffected (still
translates and passes `llzk_cli` symbolic execution cleanly). Ran a full
sweep of all 50 `circomlib_examples/*.mlir` files (translation +
`llzk_cli`, distinguishing a genuine Python `llzk_dialects` traceback from
a downstream `llzk_cli`/JSON failure): **zero regressions** — every file
that fully succeeded before still does (31 of 50 fully complete, including
`llzk_cli`). The remaining 19 fall into two buckets, both pre-existing and
unrelated to this fix:
- 4 files (`eddsa_test_concrete.mlir`, `pointbits_loopback_concrete.mlir`,
  and newly-observed `smtprocessor10_test_concrete.mlir`/
  `smtverifier10_test_concrete.mlir`) hit the identical, already-documented
  `AssertionError: Only inequalities are implemented` (`core_utils.py`'s
  `ne`-predicate limitation, §17/§18's known gap) — a Python translation
  limitation, but the exact same one already on record, not something this
  fix touches.
- 15 files now get **past Python translation entirely** (previously 9 of
  them — `babypbk`, `eddsamimc`, `eddsaposeidon`, `escalarmulfix`,
  `escalarmul_min`, `escalarmul_test`, `escalarmul_test_min`, `pedersen`,
  `pedersen2` — were blocked by the exact `KeyError` in `pod.py` this fix
  targets, per this file's own former "Known pre-existing" list) and now
  fail inside `llzk_cli` itself instead, in three distinct, unrelated
  ways: `seArrayCopy: ... not found` (5 files: `babypbk`, `eddsamimc`,
  `eddsaposeidon`, `escalarmulfix`, `pedersen2` — the same *symptom* as
  §31's original bug, a `.core` reference to a variable nothing allocated,
  but a different specific shape not exercised by this fix's regression
  test — a real, separate, follow-up gap, not investigated further this
  session), `Variable '%steps_N' is a symbolic` (7 files, an `llzk_cli`
  limitation with a `SymbolicSteps`-driven `repeat` count, §17's
  machinery — unrelated to pod handling), and `Spec for function ... not
  found` (3 `sha256*` files, an unrelated missing-spec gap). None of these
  15 involve an `llzk_dialects` Python frame — confirmed via the
  traceback's own call stack, not inferred.

## 33. Heterogeneous array-of-components (`@idx_N` pod) naming: `ark#N.in`/`ark#N.out`

The homogeneous array-of-components mechanism (§9-§10) only fires when
every element of a Circom collection shares one LLZK struct type — LLZK
types the whole thing as `!array.type<N x !struct.type<...>>`. The user
pointed at a second shape in `poseidon3_test_concrete.mlir`: `@ark`
(Poseidon's round-constant components), where each index instantiates a
*different* template (`Ark_0`, `Ark_2`, `Ark_4`, `Ark_5`, `Ark_6`, `Ark_65`,
`Ark_66`, `Ark_67` — Circom compiles a fresh template per unique
parameterization, here the round constants). LLZK can't type this as a
real array (an array requires one shared element type), so it lowers the
member to a pod with one field per index instead:
`!pod.type<[@idx_0: !struct.type<@Ark_0::...>, @idx_1: !struct.type<@Ark_2::...>, ...]>`.

Investigated (two parallel Explore passes over `signal_renaming.py` and
`struct.py`/`pod.py`/the real `@ark` LLZK body) before writing any code.
Found the actual state was worse than the user's own framing assumed:

- **`.in` came out as `ark.idx_5_in`** — but only by accident, as a
  side effect of the fully generic pod-flattening machinery
  (`ctx.input_pod_to_member` + `pod.py`'s `_register_pod_top_level` /
  `_register_nested_pod_vars`), which has no concept of `@idx_N` meaning
  anything special. It happens to produce a plausible-looking name because
  a member-backed pod's field always dot-joins (`"ark.idx_5"`) and a
  nested pod field always underscore-joins one level further
  (`"ark.idx_5_in"`).
- **`.out` (the `Ark_N::compute` call results) had no name at all** — it
  fell back to a raw SSA name (e.g. `%584_@out`). The existing
  array-of-components detector (`pod_comp_read`, part of
  `_build_component_naming_maps`'s Part 2) only matches a top-level
  `struct.writem` whose value is *directly* a `pod.read[@comp]` result.
  `@ark`'s own top-level write packs 8 already-extracted `@comp` values
  through a fresh `PodNew` (`%pod_740 = pod.new {@idx_0 = %538, ...}`), so
  the match never fires and nothing downstream (`_annotate_function_calls`)
  ever tags the calls.

The key structural fact that shapes the fix: **`@idx_N` is always a
compile-time-literal pod field name**, never a genuine runtime index — LLZK
has no syntax for `pod.read %p[@idx_%runtime_var]`. This is fundamentally
different from the homogeneous case's genuinely-symbolic loop index, which
is why `signal_renaming.py`'s `#i` post-processing mechanism (§30) exists
at all. Confirmed with the user (and via `CORELLZK.md`'s own identifier
grammar — `id := [_,a-z,A-Z,%,@,.] [_,a-z,A-Z,0-9,%,@,#,.]*`, `#` valid
anywhere but the first character) that this should be resolved entirely at
translation time, producing `ark#5.in`/`ark#5.out` as real, literal `.core`
identifiers, with **zero changes to `signal_renaming.py`**.

Two-part fix:

- **`pod.py` (the `.in` side)**: `_is_idx_pod_fields` (new) detects a pod
  whose fields are *all* literal `@idx_N` records. `_register_pod_top_level`,
  when building a member-backed pod that's idx-shaped, joins each record
  with `"#"` instead of `"." ` (`_idx_pod_child_name`, e.g. `"ark#5"`
  instead of `"ark.idx_5"`) — scoped to the semantic-naming path only (a
  raw, unregistered pod's own field naming is an implementation detail
  nothing downstream reads, so it's left untouched — confirmed by an
  existing regression test that specifically exercises that path).
  `_register_nested_pod_vars` gained a `top_level_join` parameter: once an
  `@idx_N` record has been collapsed into `"{base}#{idx}"`, its *own*
  fields should read as `"{base}#{idx}.field"` (ordinary member.signal
  convention), not `"..._field"` — so the one level of recursion
  immediately below an idx collapse dot-joins, and any deeper nesting
  falls back to the pre-existing underscore convention.
- **`struct.py` (the `.out` side)**: `StructDef.to_core`'s existing
  struct.member scan gained a branch (`_is_idx_pod_component_member`) that
  recognizes a member's pod type as a heterogeneous-components collection
  (every field `@idx_N`, every field's *value* type `!struct.type` —
  distinguishing it from the `$inputs` companion pod, whose `@idx_N`
  fields are themselves `!pod.type`), building a `member -> {@idx_N: struct
  Type}` map fed into `_build_component_naming_maps` as a new parameter. A
  new pre-pass, `_annotate_idx_pod_component_reads`, walks the whole
  `compute` body (any nesting depth — no bound needed, since unlike the
  homogeneous case there's no constant-folding involved at all) looking for
  `pod.read[@idx_N]`, matching each one by its own declared **RESULT**
  type (`_idx_read_matches_member`) rather than by comparing its source
  pod type against the member's declared shape. This distinction mattered
  in practice: the member's own final declared type
  (`!pod.type<[@idx_0: !struct.type<...>, ...]>`) is only ever exposed
  once, straight-line, at the very end of `compute` — every read that
  actually feeds a `function.call` (inside the `scf.while` that computes
  each slot, or inside a runtime-index `scf.if`/`scf.execute_region`
  dispatch ladder LLZK uses to compile a *runtime-selected* heterogeneous
  field access) instead reads a "counting pod" (`@count`/`@comp`/
  `@params`) collection — the exact same bookkeeping idiom §9's homogeneous
  case already uses, just one level of pod-nesting deeper. Matching on the
  read's own result type's `@comp` field (present or absent, structurally)
  finds every one of these, feeding the *same* `pod_to_member` map §9's
  `_annotate_function_calls` already consumes unchanged.

Found and fixed a genuine latent bug while implementing this:
`_allocate_pod_field_storage` (`pod.py`) independently called
`_register_nested_pod_vars` a *second* time for the same pod-typed field,
unconditionally — every call site (`PodNew`, `register_and_allocate_pod`)
already registers a field's nested vars via `_register_pod_top_level`
first, so this second call was always redundant, silently re-deriving the
same plain underscore-joined name. Harmless before this fix (both
computations agreed); once `_register_pod_top_level` started choosing a
`top_level_join=True` name for an idx-pod field, this redundant call
silently clobbered the correct dot-joined name back to the wrong one —
caught by a unit test, not by inspection. Fixed with an `if var_name not
in ctx.ssa2pod_var` guard.

Verified: 23 new unit tests (`test_pod_parse.py`'s `TestIsIdxPodFields`/
`TestIdxPodInputNaming`, `test_struct_parse.py`'s
`TestIsIdxPodComponentMember`/`TestIdxReadMatchesMember`/
`TestAnnotateIdxPodComponentReads`/`TestBuildComponentNamingMapsIdxPods`).
Full pytest suite green (the one pre-existing, unrelated
`test_signal_renaming.py` failure — `test_extract_component_no_dot_anywhere_warns_and_returns_none`,
confirmed to fail identically on the unmodified branch — is unchanged).
Ran the real translator end-to-end against
`poseidon3_test_concrete.mlir` (parse + `to_core` directly, no `llzk_cli`
invocation): every one of the 8 `Ark_N::compute` calls now shows
`ark#N.in`/`ark#N.out` (`N` 0-7), zero raw-SSA fallbacks remaining.
Confirmed zero regressions: regenerated `.core` output for
`ternary_concrete.mlir`, `three_subcomponents_array_concrete.mlir`,
`mux2_1_concrete.mlir`, `mux4_1_concrete.mlir`,
`ternary_two_calls_concrete.mlir` is byte-for-byte identical to a
pre-this-change baseline (the *committed* `.core` files for three of these
were already stale versus even the unmodified branch — unrelated
pre-existing drift, confirmed via `git stash`, not something this change
touched).

## 34. `$inputs` array/pod through nested `scf.while`: `while_iter_args` collection made recursive

Follow-up to §33, same file. The user reported that `@MixLast_68::@compute`
(inside `@PoseidonEx_69`, backing `struct.member @mixLast : !array.type<1
x !struct.type<@MixLast_68::...>>` — the *homogeneous* array-of-components
case, §9/§10, not §33's heterogeneous one) has its output correctly named
`mixLast_0.out`, but its input falls back to a raw SSA name instead of the
expected `mixLast_0.in`.

Traced directly against `@mixLast`'s real population code:

- **Why `.out` works**: produced by `_find_array_component_bases` /
  `_annotate_array_component_reads` (Part 2b of
  `_build_component_naming_maps`, §9a/§10). `@mixLast`'s bulk-copy
  `scf.for` sits at the top level of `compute`
  (`scf.for %arg2 = %c0 to %c1 { array.read %array[%arg2]; pod.read[@comp];
  array.write %array_732[%arg2] }`, matching the existing detector
  exactly), and `_annotate_array_component_reads` is a genuinely recursive
  whole-body walk — so it correctly finds the constant-indexed read of the
  counting-pod array *deep inside a doubly-nested `scf.while`* and stamps
  `pod_to_member[...] = "mixLast_0"`, which the (also recursive)
  `_annotate_function_calls` then turns into `FunctionCall._member_hint`.
- **Why `.in` doesn't**: a *different* mechanism — Part 1
  (`ctx.input_pod_to_member`), consumed by `_annotate_input_array_reads`
  to stamp `ArrayRead._semantic_base` (confirmed in `array.py`:
  `ArrayRead.to_core` silently falls back to a raw SSA-derived pod field
  name whenever `_semantic_base` is unset). Part 1 built its
  `while_iter_args` alias list — the `(block_arg_name, init_val_name)`
  pairs used to alias a loop's own block-arg name to the same registered
  member base — with a loop scanning only the *top level* of `compute`:
  `for op in body: if isinstance(op, SCFWhile): ...`.

  `@mixLast$inputs` is threaded through **two** nested `scf.while` loops:
  an outer one (`%422:2 = scf.while (%arg2 = %array_117, ...)`, itself
  top-level and correctly aliased) whose `do`-body contains a *second*,
  inner `scf.while (%arg4 = %arg2, ...)` — and the read that actually
  matters (`%588 = array.read %arg4[%587]`, feeding `pod.read %588[@in]` →
  the call's input) uses the *inner* loop's own block-arg name, `%arg4`.
  Since the inner `scf.while` is only reachable by recursing into the
  outer's `after_body`, the top-level-only loop never visits it — `%arg4`
  never gets an alias, `_semantic_base` is never stamped, and the read
  falls back to a raw name.

  `ternary_concrete.mlir` (the file this mechanism was originally built
  and verified against, §9b/decision 6) only nests its `$inputs` array one
  level deep, which is why this gap was never exercised before — a genuine
  depth limitation, not something specific to `@mixLast`.

Fixed with a single, narrowly-scoped change: extracted the per-`SCFWhile`
pairing computation shared by both maps into `_while_iter_arg_pairs(op)`,
then replaced the top-level-only `while_iter_args` collection with a new
recursive `_collect_while_iter_args`, mirroring the exact `('body',
'then_body', 'else_body', 'before_body', 'after_body')` walk pattern
already used by every other pre-pass in this file. It visits an op's own
iter-args *before* recursing into its sub-bodies, so an outer while's
alias is always collected before any nested while's — the existing
single-pass alias-resolution loop (unchanged) then resolves a chain of
*arbitrary* nesting depth, one level at a time, since each level's alias
only ever depends on its immediately enclosing level's, already registered
by a prior list entry (confirmed by hand-tracing the real two-level
`@mixLast` chain). `result_to_init` (the separate map `trace_source` uses)
deliberately stayed top-level-only: it's only ever queried from a
top-level `struct.writem`'s own value, and a nested while's result can
only reach that top-level value by first being yielded into its
enclosing, already-top-level while's own declared result — there's no
chain `trace_source` would ever need to follow through a nested while's
result name directly.

Verified: new `TestBuildComponentNamingMapsNestedWhileInputs` in
`test_struct_parse.py`, constructing the exact two-level `@mixLast` shape
and asserting both `ctx.input_pod_to_member["%arg4"]` and the inner read's
`_semantic_base` resolve to `"mixLast_0"`. Full pytest suite green (471
passing, same one pre-existing unrelated failure). End-to-end: regenerated
`poseidon3_test_concrete.mlir` now shows `call @MixLast_68(mixLast_0.in)
to mixLast_0.out` (previously a raw SSA name on the input side only).

While re-verifying end-to-end after this fix, found a **third**, distinct
naming gap — not fixed this session, see "Known pre-existing" below.

## 35. Generalized array-of-components naming to N dimensions; unified the separator on `#`

Follow-up to §33/§34, driven by two things: the 2-D gap §34's own
end-to-end sweep surfaced (`@sigmaF` in `poseidon3_test_concrete.mlir`),
and a second real fixture the user provided,
`multidimensional_components.circom` / `multidimensional_components_concrete.mlir`
— the heterogeneous counterpart: `Num2Bits(2)`'s `component
components[2][2]` (each slot a different `Num2Ternary(i+1)`
instantiation) lowers to `struct.member @components : !pod.type<[@idx_0_0:
!struct.type<@Num2Ternary_0::...>, @idx_0_1: ..., @idx_1_0: ..., @idx_1_1:
...]>` — the same idx-pod shape as `@ark` (§33), just with **two** numbers
baked into each field name (`@idx_{i}_{j}`) instead of one. Read the whole
real body: nothing structurally new versus the 1-D heterogeneous case —
two nested `scf.while`s (one per dimension) populate it, through an
`scf.if`/`scf.execute_region` dispatch ladder testing both indices via
`bool.and`, using the identical `@count`/`@comp`/`@params` counting-pod
idiom already handled.

The user wanted one convention, for any number of dimensions, covering
both the homogeneous (real-array, compile-time-constant index) and
heterogeneous (idx-pod) cases: `component#idx1#idx2....signal`. Confirmed
explicitly: this **replaces** the homogeneous case's existing separator
too — decision 1's `"last_0"` becomes `"last#0"` — not just adding N-D
support alongside the old `_` convention. This is a deliberate
naming-convention change, not merely a bug fix; every codebase test/doc
asserting `"last_0"`-style names needed updating.

Three-part generalization, none of it changing any function's contract or
call sites:

- **`pod.py` (heterogeneous idx-pod field pattern)**: `_IDX_FIELD_RE`
  generalized from `@idx_\d+` to `@idx_\d+(?:_\d+)*` (one or more
  underscore-separated numbers). `_idx_pod_child_name` fixed to split the
  numeric remainder on `_` and `#`-join each piece individually (it
  previously appended the whole multi-number remainder as one segment,
  which for `"@idx_0_0"` would have produced `"base#0_0"`, not
  `"base#0#0"`). `struct.py`'s idx-pod consumer side
  (`_is_idx_pod_component_member`/`_idx_read_matches_member`/
  `_annotate_idx_pod_component_reads`, all added in §33) needed **zero**
  changes — none of them parse a record's own numeric content; they
  already delegate entirely to `_idx_pod_child_name`.
- **`struct.py` (homogeneous array-of-components, N dimensions)**:
  `_find_array_component_bases`'s single top-level `scf.for` scan became a
  recursive walk (`_walk_for_bulk_copy_nest`) over a *chain* of nested
  `scf.for`s, one per dimension, checking the bulk-copy triple (array read
  of a counting-pod array / `pod.read[@comp]` / array write into the
  target) at every level against the *full* stack of enclosing induction
  variables collected so far — the triple only actually matches once
  `len(indices)` equals the current stack depth, i.e. at the innermost
  loop for an N-D bulk copy; a non-matching level simply finds nothing and
  recursion carries on. Reduces to exactly the old single-`scf.for`
  behavior when there's no nesting. `_annotate_array_component_reads` and
  `_annotate_input_array_reads` (the `.out` and `.in` sides respectively)
  both dropped their `len(op.indices) == 1` restriction, instead building
  the name from *all* of a read's indices — `"{base}" +
  "".join(f"#{v}" for v in idx_vals)` when every index resolves to a
  compile-time constant, the bare base name if *any* doesn't (a
  partially-resolved index still isn't enough to name one specific
  instance, so it's treated the same as fully-unresolved).
- **`StructDef.to_core`'s `ctx.member_to_struct` registration** (the
  registry `signal_renaming.py`'s `components_info` gating consumes for
  the genuinely-runtime-loop case — a separate, already-`#`-based
  mechanism unrelated to the `pod_to_member`/`_member_hint` naming above):
  its single-dimension-only regex
  (`!array\.type<\s*(\d+)\s+x\s+!struct\.type<`) replaced with the
  existing `array_dimensions` helper (`utils.py` — already N-D,
  element-type-agnostic, already used elsewhere in this codebase) plus
  `itertools.product` over each dimension's `range`, registering one
  `f"{member_name}" + "".join(f"#{i}" for i in combo)` entry per index
  combination.

Verified: 25 new/updated unit tests across `test_pod_parse.py`
(`TestIsIdxPodFields`'s 2-D case, new `TestIdxPodChildName`, a 2-D
`TestIdxPodInputNaming` case) and `test_struct_parse.py` (a 2-D nested-for
`_find_array_component_bases` case plus a negative "mismatched inner index
count" case, 2-D `_annotate_array_component_reads` cases — both
all-constant and partial-constant, a new `TestBuildComponentNamingMapsArraysND`
covering both the `.in` and `.out` sides end-to-end, and a 2-D
`TestBuildComponentNamingMapsIdxPods2D`), plus updating every existing
test that hardcoded the old `"last_0"`-style separator. Full suite green
(484 passing; the one pre-existing, unrelated `test_signal_renaming.py`
failure unchanged).

End-to-end: ran the real translator (parse + `to_core`, no `llzk_cli`)
against `multidimensional_components_concrete.mlir` — all four
`Num2Ternary_{0,1}::@compute` calls now show
`components#{i}#{j}.in`/`components#{i}#{j}.out` for every `(i,j)` in
`{0,1}×{0,1}`. Re-ran `poseidon3_test_concrete.mlir` end-to-end: **zero**
raw-SSA-fallback calls remain anywhere in the 478K-line output (previously
6 of 8 `@Sigma_1::@compute` calls, backing `@sigmaF`) — `@sigmaF`'s calls
now resolve to the bare `sigmaF.in`/`sigmaF.out` (its own indices sit
inside a genuine runtime loop throughout, so — matching the established
"no single instance to name more specifically at translation time"
philosophy already used for `Num2Bits_16_325` in `ternary_concrete.mlir`
— there's no compile-time-constant instance to disambiguate further, just
as `@sigmaP`'s own calls already showed a mix of `sigmaP#0.in`/`.out` and
bare `sigmaP.in`/`.out` before this session even started); `@ark`
(§33) and `@mixLast` (§34) re-confirmed correctly named under the unified
convention (`ark#N.in`/`.out`, `mixLast#0.in`/`.out`). Regenerated
`.core` output for `ternary_concrete.mlir` against its pre-this-change
baseline: byte-for-byte identical (its own array-of-components member is
symbolic-loop-indexed throughout, so the compile-time-constant naming
path this change touches is never exercised there). Regenerated
`three_subcomponents_array_concrete.mlir` and diffed: every changed line
is *exactly* a `"_0"`/`"_1"` → `"#0"`/`"#1"` separator substitution
(`last_0` → `last#0`, `components_1` → `components#1`, etc.) — nothing
else shifted, confirming the naming-convention change is scoped exactly
as intended.

## 36. `signal_renaming.py` generalized to real N-D / arbitrary array traversal order

Follow-up to §35. The N-D naming fix made `.core`-level naming fully
correct, but `signal_renaming.py`'s own post-hoc mechanism (for a member
left at its bare name — genuinely symbolic population loop, e.g.
`poseidon3_test_concrete.mlir`'s `@sigmaF`) still assumed a flat, linearly
incrementing per-call counter (`component2iteration[component_name]`,
i.e. slot `0, 1, 2, ...` in call-trace order) — correct only for a 1-D
member populated by one simple sequential loop. The user identified two
concrete problems: (1) a flat `f"{component_name}#{count}"` produces a
single `"#i"` segment, which can never match an N-D `components_info`
key (`"sigmaF#i#j"`-shaped, from §35) — so `@sigmaF` never got renamed at
all; and (2) more generally, a flat counter silently assumes sequential
`0,1,2,...` visitation, which is wrong for any non-row-major traversal or
for a member populated by more than one separate loop nest. The user
provided a second fixture demonstrating this concretely,
`arbitrary_traversal_array_components.circom` /
`_concrete.mlir`: a `components[5][6]` array populated by **two separate**
loop nests in sequence — first even-`i`/even-`j` slots, then odd-`i`/odd-`j`
— with the real visitation order `#0#0, #2#0, #4#0, #0#2, ...` (even
nest) followed by `#1#1, #1#3, ...` (odd nest), never a simple count.

**Fix, entirely as a new `struct.py` static pre-pass** (confirmed with the
user as the right architecture — no changes to `scf.py`'s `to_core`
methods at all): for each array-of-components member with at least one
genuinely-symbolic population site, statically compute the real sequence
of concrete array-index tuples its population loop(s) actually visit, in
true execution order, and export it (`ctx.array_component_index_sequences`,
mirroring `ctx.member_to_struct`'s own per-struct shape) into the SMT
JSON's `components_index_sequences` field, alongside the existing
`components_info`. `signal_renaming.py`'s `process_components` then
consumes a per-member **cursor** into this sequence (instead of a flat
counter) to build `f"{component_name}" + "".join(f"#{i}" for i in
idx_tuple)` — a direct N-segment generalization of the old single-`#{count}`
format — falling back to the original flat-counter behavior for any
component with no registered sequence (an older JSON, or a population
loop whose bound genuinely isn't statically resolvable).

Reused, rather than duplicated, the existing trip-count machinery:
`core_utils.py`'s `count_iterations`/`_infer_from_comparison` (already
used by `SCFWhile._extract_step` to compute a `repeat N` count) share
their resolution logic with two new siblings — `iterate_values` (the
actual sequence, not just the count) and
`infer_iteration_sequence_from_expressions` — via a small refactor
(`_resolve_comparison_recurrence`, extracted once, consumed by both the
existing count path and the new sequence path) rather than a second,
independently-written copy of the same free-variable/bound-resolution
logic that could silently drift from the original. `scf.py` similarly
gained one new method, `SCFWhile._extract_index_sequence` (a sibling of
`_extract_step`, reusing its own `_build_while_var_expressions` — itself
newly extracted, verbatim, from `_extract_step`'s old body) — `to_core`
and `_extract_step` themselves are completely unchanged.

**A genuinely non-obvious finding, confirmed by reading the real
`arbitrary_traversal_array_components_concrete.mlir` body directly**: an
array read's index list is *not* positionally aligned with its population
loop's own nesting order. The fixture writes `components[i][j]` (array
dimension 0 = `i`, dimension 1 = `j`), but its first loop nest has `i`
driven by the *inner* loop and `j` by the *outer* one — `array.read
%arg5[%7, %8]` has `%7` tracing back to the inner loop's own block-arg and
`%8` to the outer's. So mapping each index to "which enclosing loop
produced it" is done by resolving each index (through `cast.toindex`,
`_trace_to_enclosing_loop`) back to a specific loop's own iv/block-arg
**name**, never by position or nesting depth — confirmed correct against
the fixture's *second* loop nest too, which (per its own Circom source)
nests the opposite way (`i` outer, `j` inner) and was resolved correctly
without any special-casing, purely because the mapping is name-driven.
(This finding does not affect the already-shipped bulk-copy detector,
`_walk_for_bulk_copy_nest` from §35 — that loop is freshly generated by
the LLZK frontend specifically to iterate in natural dimension order,
confirmed separately.)

**A second non-obvious finding, hit and fixed while validating against
the real fixture**: a multi-input-signal component's "ready to call yet?"
check is re-emitted once per input-signal assignment (the backing
`@count` starts at the input count and is decremented at each signal
write), each with its own complete `function.call` + array-write
scaffolding — but only the textually *last* such checkpoint's guard is
ever true at runtime (count reaches exactly 0 only once, after the final
signal). `arbitrary_traversal_array_components.circom`'s `IsZero`
component (2 input signals) exercises this directly: both checkpoints are
structurally indistinguishable "real population writes," but only the
second's `array.write` ever actually executes. First surfaced as a
spurious 2x-duplicated sequence (each nest's 9/6-element sequence
appearing twice). Fixed by collecting *every* structurally-matching
candidate within one loop iteration's own scope
(`_collect_population_write_candidates`, crossing through `scf.if`/
`scf.execute_region` nesting but not into a further-nested loop) and
keeping only the last — sound in general (not just for 2 signals), since
program order within one static loop body always places the true,
count-reaches-zero checkpoint last, regardless of how many inputs the
callee has. A second, unrelated false-positive was also found and fixed
the same way: the array's own initial-fill loop (`array.write
%array[%arg1, %arg2] = %pod_8`, a fresh `pod.new`, never read from first)
structurally matches "non-constant-indexed write into the registered
array" just as well as a real population write — distinguished via
`_is_population_write`, requiring the write's own value to trace back to
an `ArrayRead` of the *same* array (a real read-modify-write), which the
init loop's fresh-`pod.new` value never does.

Verified: 6 new `core_utils.py` tests (`TestIterateValues`,
`TestInferIterationSequence`), 2 new `scf.py`-level tests
(`_extract_index_sequence`), 32 new `struct.py` tests across 7 classes
covering every stage of the new pre-pass in isolation and end-to-end
(including both non-obvious findings above as their own dedicated
regression cases), and 4 new `signal_renaming.py` tests (N-D sequence
consumption, flat-counter fallback, sequence-shorter-than-observed-calls,
and missing-field backward compatibility). Full suite green (531 passing,
the one pre-existing unrelated `test_signal_renaming.py` failure
unchanged).

End-to-end, via the full `main_execution.py` pipeline (real `llzk_cli`
invocation, confirmed available at `translator/lean/llzk_cli`): re-ran
`ternary_two_calls_concrete.mlir` (the pre-existing 1-D symbolic case) —
byte-for-byte identical `vars_info` output to before this change,
confirming zero regression (the new sequence path silently activates for
one of its two array members and produces the identical result; the
other falls back to the old counter, also producing the identical
result). Ran `poseidon3_test_concrete.mlir` (the real motivating example,
478K generated `.core` lines) end-to-end through real `llzk_cli` symbolic
execution: `vars_info` now contains exactly 9 `sigmaF#i#j.in`/`.out` pairs
(`i,j` in `0..2`), a **perfect match** with this session's own static
prediction (`components_index_sequences["sigmaF"]` — computed entirely
independently, before `llzk_cli` ever ran); `@ark`/`@mixLast`/`@sigmaP`
re-confirmed still correctly named in the same run.

**A genuinely surprising discovery while attempting the same end-to-end
verification against `arbitrary_traversal_array_components_concrete.mlir`**:
`llzk_cli`'s own SMT encoding contains *zero* `:meta-data "call ..."`
annotations for `IsZero` (the array's callee) at all — confirmed its
compute body is fully **inlined** into `@IsEqual_1`'s own formula (flattened
signal names like `%3_f255_f254_@output_zero1` appear directly, with no
reference to `IsZero_0`/`compute` anywhere), unlike `Num2Bits_0` (has its
own internal loop) or `Sigma_1` (Poseidon's S-box), both of which remain
genuine opaque function calls with real `:meta-data` annotations. This
appears to be an `llzk_cli`-internal optimization for a component simple
enough (here, a single `felt.mul`, no internal control flow) — and it means
the *entire* `:meta-data "call ..."`-based renaming mechanism (both the
pre-existing counter-based one and this session's new sequence-based one)
has nothing to rename for such a component, regardless of correctness on
this translator's own side. Confirmed this is not a bug in this session's
work: the underlying `array_component_index_sequences` computation for
`arbitrary_traversal_array_components_concrete.mlir` was independently
verified correct (parse-and-`to_core`-only, no `llzk_cli`) — `[(0,0), (2,0),
(4,0), (0,2), ...]` for the even nest and `[(1,1), (1,3), (1,5), (3,1), ...]`
for the odd one, matching the user's own hand-derived expected order
exactly — the mechanism simply has no call annotations available to act on
for *this specific* fixture's trivial callee. Not investigated further
this session (an `llzk_cli`-internal inlining heuristic, out of this
translator's own scope) — noted below.

## 37. Pure-function `def`s hoisted and topologically sorted so they always precede any `call` to them

The user found `sha256_2_test_concrete.mlir` translating to a `.core` file
where `call @ssigma1_1(...)` appears *before* its own `def @ssigma1_1(...)`,
expecting a topological-sort pass (from §16, "Support pure functions") to
have prevented this. Investigation showed no such pass ever existed: §16's
`ModuleOp.to_core` pre-pass (`llzk.py`) only registers a pure function's
*signature* early (`_register_pure_function`, `poly.py`) so a forward
`function.call` resolves without a `KeyError` — it never moves the `def`'s
own *text* earlier. The actual emission loop is a straight
`for operation in self.body: yield from operation.to_core(ctx)`, mirroring
source-file order. §16's own comment explicitly argued a dependency
graph/topological sort wasn't needed — true only for signature resolution,
not output ordering. This was never caught before because §16's original
fixture (`escalarmulw4table_concrete.mlir`) never got far enough (blocked
by the §17 limitation) to produce a full `.core` file exercising the gap;
it now fully translates (§17's later generalization resolved that blocker)
and was used as a second regression check for this fix, confirming
`pointAdd_1`'s `def` (forward-referenced by `EscalarMulW4Table_0`) is now
hoisted correctly too.

Confirmed via `grep` on the source that this isn't a single-level forward
reference: `ssigma1_1`/`ssigma0_2`/`bsigma1_3` (declared earlier in the
file) each call `rrot_8` (declared later) — a real, multi-level dependency
chain among pure functions themselves, not just "pure function called
before struct."

**Fix (confirmed with the user as the right design), entirely in
`llzk.py`:**
- **`_collect_function_calls`** (new): recursively yields every
  `FunctionCall` in a list of operations, descending into nested
  `scf.if`/`scf.for`/`scf.while`/`scf.execute_region` bodies the same way
  `scf.py`'s `_collect_result_names` already does (explicit per-class
  checks, falling back to a generic `hasattr(op, 'body')`) — a pure
  function's own call to another one may be nested inside control flow,
  not just at its own top level.
- **`_topo_sort_pure_functions`** (new): given every top-level pure-function
  `poly.template` (as `(template, llzk_name, func_def)` triples, in file
  order), builds each one's direct dependency set (calls to *other* known
  pure functions, via `_collect_function_calls`) and runs a DFS-based
  topological sort — visiting entries in original file order and recursing
  into dependencies first, so any pair with no dependency between them
  keeps its original relative order (stable), and only real forward
  references cause reordering. Raises `ValueError` on a cycle (mutual
  recursion among pure functions isn't supported — matches this codebase's
  fail-loud style, e.g. the `assert` already in `_register_pure_function`).
- **`ModuleOp.to_core`**: the existing registration pre-pass now also
  collects the pure-function triples it registers, sorts them via
  `_topo_sort_pure_functions`, and emits them *first* — ahead of every
  other top-level item (structs etc.), which keep their existing relative
  order unchanged. Safe because nothing depends on a pure function's
  textual position *relative to a struct*, only on it existing (as text)
  before any call to it, wherever that call sits.

No changes to `poly.py`/`function.py`: `PolyTemplate.to_core`'s own
redundant `_register_pure_function` call stays as a safety net (idempotent),
and `FunctionCall.to_core`'s lookup is unaffected.

**Design alternative considered and rejected:** a stable in-place
topological sort over the *entire* top-level body (Kahn's algorithm with
original-index tie-breaking), moving an item only when a forward reference
actually forces it — closer to source order for a human reading the
generated `.core`. Rejected (by the user) as more code/risk for a benefit
(output-position proximity to source) that only matters for readability of
machine-generated output, not correctness.

Added 4 tests to `tests/test_llzk_parse.py`: a 3-level transitive forward
reference (`A`→`B`→`C`, declared in reverse dependency order, mirroring
`ssigma1_1`→`rrot_8`), a stability check (two independent pure functions
keep their original order), a struct calling a pure function declared
later in the body, and cycle detection. Verified end-to-end by regenerating
`sha256_2_test_concrete.mlir` (bypassing the `llzk_cli` subprocess step,
since this only changes already-correct text's emission *order*, not
`signal_renaming.py`/SMT-level behavior) and `escalarmulw4table_concrete.mlir`,
then scripting a check that every `call @X(` in the output has a `def @X(`
at an earlier line — zero violations across 111 and 3 pure functions
respectively (up from at least one violation, `rrot_8`, before the fix).
Full suite: 535 tests, up from 531 (one pre-existing, unrelated failure in
`test_signal_renaming.py` — `test_extract_component_no_dot_anywhere_warns_and_returns_none`
— present before this change too).

## 38. Pure functions whose own loop bound depends on their own parameter: specialized per distinct compile-time-constant call-site value

**Reported:** requested support for `bool.ne`/`bool.eq` while-condition
predicates, motivated by `pointbits_loopback_concrete.mlir`'s `sqrt_0`
helper (Tonelli–Shanks modular sqrt), which uses `bool.cmp ne`.

**Investigated first, per this project's own workflow, and the premise
didn't survive contact with the real file:** traced `sqrt_0`'s parameter
`n` through all 4 of its call sites (2 in `pointbits_loopback_concrete.mlir`,
2 in `eddsa_test_concrete.mlir`) — every one bottoms out, through a
`felt.div`/`felt.sub`/`felt.mul` chain, at `array.read` on the enclosing
component's own 256-bit signal input: a genuine runtime witness, never a
compile-time constant. Even a perfect `bool.ne` implementation couldn't
help, because Core's own `repeat` only accepts a plain identifier or
integer literal (`CORELLZK.md`'s grammar: `sexp := id | Z`) — not a real
"check condition each iteration" loop; a genuinely data-dependent trip
count can't be expressed under the current architecture regardless of
predicate support — this alone is sufficient reason to leave `sqrt_0`
unaddressed, independent of anything about constraints.

**Correction (§39 investigation):** this section originally also
justified leaving `sqrt_0` alone because `out[0] <-- x` in
`circomlib/circuits/pointbits.circom:107` "generates no constraint, so
this has no correctness impact." That's an overstatement, caught while
investigating a follow-up request: `out[0]` is then fed into `babyCheck.x
<== out[0]` and `n2bX.in <== out[0]` (real constraints) inside the same
template, and `pointbits_loopback.circom`'s own `Main` template adds
`b2p.out[0] === in[0]` directly (line 21). The `<--` only means the sqrt
computation *itself* isn't constrained — `out[0]`'s value still matters
for everything downstream. The architectural reason above was always the
real, sufficient justification; this "no impact" framing should not have
been part of it. `bool.ne`/`bool.eq` support was still deliberately
dropped from scope this session (`core_utils.py:485`'s `assert op in
("lt", "le")` was unchanged at the time) — but see §39, which later
extended it for a different, genuinely fixable file.

**Redirected to a genuinely fixable, real, already-documented bug
instead:** `EscalarMulW4Table_0` (`escalarmulw4table_concrete.mlir` and 6
sibling files). Its while loop's bound (`arg3 < arg1*4`,
`escalarmulw4table_concrete.mlir:90-91`) depends on `arg1` ("k" — the
function's own parameter) — structurally the same "bound depends on an
unresolved parameter" shape as `sqrt_0`, but here **every real call site
passes a literal `felt.const`**: a single value (k=0, or k=3 for the
`_test3` variant) in the simpler files, and 64 distinct values (k=0..63,
one per 4-bit window of a scalar multiplication) within the same module
in `escalarmul_test_concrete.mlir` and its two `_min`/`_test_min` siblings.
Already a documented, real bug (not hypothetical): all 7 files translated
in Python via the existing `SymbolicSteps` fallback, but `llzk_cli`'s own
symbolic execution then rejected the result with `Variable '%steps_N' is
a symbolic` (see "Known pre-existing" list) — a function is translated
exactly once, generically, so `k` was never known even though it's
constant at every call site, and `llzk_cli` can't symbolically execute a
`repeat` whose bound isn't a concrete integer.

**Fix:** a new whole-module pre-pass,
`_specialize_loop_bound_parametric_pure_functions` (`llzk.py`), run after
the existing pure-function registration + `_topo_sort_pure_functions`
call (deliberately after — topo-sort must order on the *original*,
unspecialized call graph) and before the emission loop:

1. For each pure function, recursively find every `scf.while` in its body
   (`_collect_while_loops`, same recursive-descent shape as
   `_collect_function_calls`) and check, via the already-existing
   `core_utils._collect_free_var_names`, whether the condition's only
   unresolved free variable(s) trace to the function's own `in_args` —
   "loop-bound-parametric" (`_parametric_params_for_while`).
2. Walk the *whole module* (every pure function body and every struct's
   `@compute`/`@constrain`) for calls targeting it (`_collect_function_calls`,
   reused module-wide, not just within pure-function bodies as before),
   and resolve each call's relevant argument to a concrete int: a new flat
   forward var2expression map over the *calling* function's own body
   (`_build_ops_var2expression`, unconditional — unlike `scf.py`'s
   `_process_while_variables`'s backward-prune-from-target, since the
   target name isn't known in advance here), fed into the **existing**
   `construct_function_from_expressions(arg, map, set())(0)` (unchanged —
   this is the whole point: the concrete-bound resolution logic itself
   never needed to know about specialization). `KeyError`/`NotImplementedError`
   (an `array.read`, `llzk.nondet`, or unmapped external value) means "not
   a constant here" and aborts specialization for the whole function,
   leaving it exactly as today (`sqrt_0`'s case).
3. If every call site resolves: group by the exact resolved value-tuple.
   One distinct value → keep the original core name unchanged (e.g.
   `escalarmulw4table_concrete.mlir`'s single k=0). Multiple → suffix each
   clone `{name}__{arg_display_name}{value}` (e.g. `EscalarMulW4Table_0__k1`,
   `__k2`, ...), using `FunctionDef.in_arg_names` for a readable name.
4. Register each clone in `ctx.llzk_func2core`/`ctx.core_func2args` (same
   shape `poly.py`'s `_register_pure_function` already produces) and
   mutate each resolved `FunctionCall.callee` in place to point at its own
   clone. `poly.py`'s `PolyTemplate.to_core` (extended) emits one `def`
   per clone instead of the single generic body when a new
   `ctx.pure_function_specializations` entry exists for it, each clone
   translated with its own one-shot `ctx.pending_const_seed` (new
   `TranslationContext` field, applied by `function.py`'s
   `FunctionDef.to_core` immediately after its existing `var2const.clear()`,
   then reset) — folding the parameter in as a known constant lets the
   **existing, unmodified** concrete-bound branch of
   `core_utils.py`'s `_resolve_comparison_recurrence` produce a real
   integer `repeat` count.

**A second, genuinely new bug surfaced by this fix's own end-to-end
verification** (a specialized `EscalarMulW4Table_0` clone with k=0
resolves to `repeat 0`, a trip count no prior real example ever exercised):
`SCFWhile.to_core` only ever bound its own *external result name(s)*
(e.g. `%22`/`%22#0`) inside `emit_iteration()` — textually nested inside
the `repeat` block, so a 0-iteration loop left them completely unbound.
Code after the loop then referenced an undefined SMT variable
(`llzk_cli`: `seArrayReadNonConstIdx: failed to get array variable:
Variable '%22#0' not found`). Fixed in `scf.py` by also binding the
result(s) to their initial values right after the existing per-arg
initial-value assignment, before the `repeat` block — mirroring
`SCFCondition.to_core`'s own component-wise pairing exactly, just against
the initial values instead of a live iteration's yielded ones. Harmless
(redundant, immediately overwritten) whenever the loop does run at least
once — confirmed via the full pre-existing test suite and a direct
before/after `.core` diff on unrelated files (`mux4_1_concrete.mlir`,
`poseidon3_test_concrete.mlir`): the only additions are exactly these new
pre-binding lines, nothing removed or reordered.

**A third, small pre-existing bug surfaced along the way:**
`function.py`'s `_parse_in_arg` (used by `FunctionDef.in_arg_names`, whose
readable names this fix's clone-naming relies on) only recognised a
trailing `{attrs}` dict when it was the literal end of the string. Real
`--llzk_plaintext` output attaches its own ` loc(...)` suffix to almost
every argument individually (not just once at the end of the whole
`function.def` line, which `LLZKParser`'s own line-level loc-stripping
already handles) — e.g. `... {function.arg_name = "k"} loc("f.circom":31:28)`
— so in practice `in_arg_names` returned `{}` for essentially every real
multi-arg example, silently, since nothing consumed it before this fix.
Fixed by stripping a per-argument trailing `loc(...)` (reusing
`loc_parser.strip_trailing_loc`, the same utility `scf.py`'s
`_parse_block_args` already relies on for the identical reason) before
checking for the attribute dict. As a side effect, `in_args`' own `Type`
objects are now clean too (no more `{attrs} loc(...)` cruft appended to
the type string) — cosmetic only; `Type.to_core()` already ignored it.

**Verified:** `tests/test_llzk_parse.py::TestPureFunctionSpecialization`
(3 new tests: single-value keeps the original name, multiple distinct
values get suffixed clones with readable `k`-based names, an unresolvable
argument leaves the function entirely untouched) and
`tests/test_scf_parse.py::test_while_to_core_zero_iterations_still_binds_result`
(1 new test). Full suite: 540 tests, up from 536, zero regressions.
Full pipeline (`llzk2core.py`, including a real `llzk_cli` run) now
succeeds end-to-end — no more `Variable '%steps_N' is a symbolic` — for
all 7 files the "Known pre-existing" list named for this exact error:
`escalarmulw4table_concrete.mlir` (`repeat 0`, name unchanged),
`escalarmulw4table_test_concrete.mlir` (`repeat 0`, name unchanged),
`escalarmulw4table_test3_concrete.mlir` (`repeat 12`, name unchanged),
`escalarmul_test_concrete.mlir` / `escalarmul_test_min_concrete.mlir` /
`escalarmul_min_test_concrete.mlir` (64 clones each,
`EscalarMulW4Table_0__k0` through `__k63`, each with the matching
concrete `repeat` count, all 128 call sites per file correctly
redirected), and `pedersen_test_concrete.mlir` (same `EscalarMulW4Table_0`
callee, also now fully resolved). A full Python-only translate sweep across every
`circomlib_examples/*.mlir` file confirms zero regressions: 46/50 still
translate cleanly, and the remaining 4 fail with the exact unchanged,
pre-existing `AssertionError: Only inequalities are implemented.
Operation: ne` (`eddsa_test_concrete.mlir`, `pointbits_loopback_concrete.mlir`,
`smtprocessor10_test_concrete.mlir`, `smtverifier10_test_concrete.mlir`) —
confirming `sqrt_0` and friends are correctly left untouched by this fix,
exactly as designed.

**Incidentally observed, not fixed (pre-existing, unrelated):** pure
function `def` emission order among *independent* siblings (no call
relationship between them) is nondeterministic across separate process
runs — confirmed by re-running the unmodified `_topo_sort_pure_functions`
against `sha256_2_test_concrete.mlir` three times and seeing `bsigma0_6`/
`Ch_4`/`ssigma0_2` reorder relative to each other each time. Root cause:
`name2deps[name]` is a `Set[str]`, and `visit(dep) for dep in
name2deps[name]` iterates it in Python's hash-randomized order
(`PYTHONHASHSEED`), which only affects independent siblings' *relative*
order (dependency edges are still respected) — cosmetic, no known example
depends on a specific order among unrelated defs, not investigated
further this session.

## 39. `bool.ne`/`bool.eq` concrete-bound while conditions, plus field-aware (modulo-prime) constant-folding and trip-count simulation

**Reported:** asked to explore the 4 `outcome.csv` rows whose
`error_message` starts with a raw Python `Traceback` (translation fails
before `llzk_cli` ever runs), reading the corresponding `.circom` sources
in `circomlib/test/circuits/` rather than the `.mlir` files, to save
tokens.

All 4 hit the same symptom (`core_utils.py:485`'s `AssertionError: Only
inequalities are implemented. Operation: ne`), but split into two
unrelated causes:

- `eddsa_test_concrete.mlir` / `pointbits_loopback_concrete.mlir`: `sqrt_0`
  again (§18/§38) — `eddsa.circom` calls `Bits2Point_Strict()` twice
  (decompressing a public key `A` and a signature's `R8`, both genuine
  per-verification witness values). Confirmed unfixable, same as §38; see
  §38's own correction above for the accurate reasoning.
- `smtprocessor10_test_concrete.mlir` / `smtverifier10_test_concrete.mlir`:
  an entirely different, ordinary loop —
  `circomlib/circuits/smt/smtprocessor.circom:210` and
  `smt/smtverifier.circom:95` both read `for (i = nLevels-1; i != -1;
  i--)`, with `nLevels = 10` a literal template argument
  (`SMTProcessor(10)`/`SMTVerifier(10)`). Confirmed directly in the real
  `.mlir`: `bool.cmp ne(%arg8, %felt_const_18446744069414584320)`, where
  `18446744069414584320` is exactly `goldilocks_prime - 1` — how circom's
  `-1` looks after field wraparound.

**A landmine, not just a missing predicate:** naively relaxing the assert
to allow `ne` would not have fixed the second pair — it would have hung
the translator forever. `felt.py`'s constant-folding (`FeltBinary`/
`FeltUnary`'s `_BINARY_FNS`/`_UNARY_FNS`) was plain Python integer
arithmetic with no modular reduction at all, so the existing trip-count
simulation (`count_iterations`, fed by
`construct_function_from_expressions`) would decrement `9, 8, ..., 0, -1,
-2, -3, ...` as real negative Python integers forever, never equal to the
huge positive bound.

**Fix, per explicit user direction — not a narrow eq/ne patch:**

1. `core_utils.py:485`: `assert op in ("lt", "le")` → `assert op in ("lt",
   "le", "eq", "ne")`. `_resolve_comparison_recurrence`'s concrete-bound
   branch gains `compare_func = (lambda x: x == bound_value) if op == "eq"
   else (lambda x: x != bound_value)` for `op in ("eq", "ne")` — symmetric,
   no `variable_is_lhs` branching needed, unlike `lt`/`le`. Scope
   deliberately stays concrete-bound-only: the `SymbolicSteps`
   (unresolved-bound) path still asserts `lt`/`le` only — no known example
   needs a symbolic eq/ne formula, and an eq/ne loop's termination isn't a
   monotonic bound crossing the way `SymbolicSteps`'s formula assumes.
2. New `TranslationContext.prime: int` field (`core.py`), defaulted to the
   goldilocks prime — matches every existing example, so nothing needed
   updating for the default case. New `-p`/`--prime` CLI flag
   (`args_parser.py`), same choices as `complete_avazar.py`'s own
   `--prime`, resolved to the actual prime int in `main_execution.py` via
   a new `core_utils.FIELD_PRIMES` table (values copied verbatim from
   `complete_avazar.py`'s own `PRIMES` dict — a deliberate small
   duplication, not a cross-repo import, since `llzk2core` stays a
   self-contained subproject). `complete_avazar.py`'s own call site
   (previously a raw `argparse.Namespace(source=..., target=...)`, never
   passing its own `--prime` selection through at all) now passes
   `prime=args.prime`.
3. `core_utils.construct_function_from_expressions` gains an optional
   `prime` parameter (default: goldilocks), reducing the result of every
   composed operation modulo it. This is the single, central point of
   correctness: `SCFWhile._extract_step`'s `update_func`/`bound_func` are
   built through this function, so once it's prime-aware, `%arg8`
   correctly becomes `prime - 1` the instant it steps below 0, matching
   the literal bound exactly — no special-casing needed in the eq/ne
   `compare_func` itself. Threaded from `scf.py`'s
   `_extract_step`/`_extract_index_sequence` down through
   `infer_n_repetitions_from_expressions`/`infer_iteration_sequence_from_expressions`/
   `_infer_from_comparison`/`_infer_sequence_from_comparison`/
   `_resolve_comparison_recurrence`.
4. `felt.py`: `FeltConst`/`FeltUnary`/`FeltBinary`'s `to_function()` gain
   the same optional `prime` parameter; their `to_core()` constant-folding
   passes `ctx.prime` through, so every compile-time fold — not just
   while-loop simulation — is consistently correct. Care taken to reduce
   modulo the prime **only genuine field arithmetic**
   (`add`/`sub`/`mul`/`div`/`pow`/`neg`/`inv`) — `felt.shl`/`shr`/
   `bit_and`/`bit_or`/`bit_xor`/`bit_not`/`uintdiv`/`sintdiv`/`umod`/`smod`
   are deliberately left untouched: those operate on a felt-typed value's
   underlying bit pattern (e.g. `Num2Bits`' `felt.shr`/`felt.bit_and`
   bit-extraction loops), not field arithmetic — reducing them modulo the
   prime would be wrong, not just unnecessary.
5. Two ops needed the prime injected *into* their own algorithm, not just
   a `% prime` wrapped around the old one: `felt.inv` was `1 // x`
   (never a real modular inverse — it was never given the modulus it
   needs) and becomes `pow(x, prime - 2, prime)` via Fermat's little
   theorem (every field in `FIELD_PRIMES` is prime), with an explicit
   `ZeroDivisionError` for `x == 0` preserving the existing "skip the fold,
   this may be a dead `scf.if` branch" behavior. `felt.pow` becomes
   Python's 3-arg `pow(x, y, prime)` (true modular exponentiation) instead
   of `x**y % prime`, which would otherwise materialize an astronomically
   large intermediate bigint for a large exponent (routine in field
   arithmetic, e.g. `sqrt_0`'s own Tonelli-Shanks residue checks) purely
   for performance.
6. Defensive iteration cap (`_MAX_SIMULATED_ITERATIONS = 1_000_000`) added
   to `count_iterations`/`iterate_values` — raises a clear `RuntimeError`
   instead of hanging indefinitely if a recurrence still never terminates.
   Cheap insurance against any future non-terminating shape, not specific
   to this fix.

**Verified:** new tests in `tests/test_core_utils.py`
(`TestInferNRepetitions`: eq/ne concrete-bound resolution, eq/ne symbolic
bound correctly rejected; new `TestPrimeAwareSimulation`: a
countdown-to-"prime-1" loop with a small test prime, confirming
`construct_function_from_expressions` reduces modulo the given prime and
defaults to goldilocks; new `TestSimulationSafetyCap`: both
`count_iterations`/`iterate_values` raise instead of hanging, verified
with a monkeypatched small cap) and `tests/test_felt_parse.py` (`felt.inv`
is a real modular inverse and correctly rejects `x == 0`;
`to_function()`'s no-prime path keeps today's old placeholder behavior for
backward compatibility; `felt.bit_not`/`felt.uintdiv` confirmed
*unaffected* by prime-aware reduction; `felt.sub` wraps at the prime;
`felt.pow` matches Python's own modular `pow`). Full suite: 555 tests, up
from 540, zero regressions.

Full pipeline (`llzk2core.py`, including a real `llzk_cli` run) now
succeeds end-to-end for both target files —
`smtprocessor10_test_concrete.mlir` and `smtverifier10_test_concrete.mlir`
translate in ~2s (no hang) and `llzk_cli` produces a valid ~340MB SMT JSON
for each, with zero remaining `%steps_` symbolics. Re-running
`eddsa_test_concrete.mlir`/`pointbits_loopback_concrete.mlir` shows
*expected* progress, not a regression: they now advance past the `ne`
assertion and hit the next, already-documented §18 blocker
(`NotImplementedError: Could not identify the loop-carried variable...` —
`sqrt_0`'s initial values via `felt.pow` were never tracked in
`ctx.var2const`) instead of stopping at the first one. A full Python-only
sweep across every `circomlib_examples/*.mlir` file: 48/50 clean (up from
46/50), with only that same pair still failing, at that same expected
next blocker. A before/after `.core` diff on 5 diverse, unrelated files
(`mux4_1_concrete.mlir`, `poseidon3_test_concrete.mlir`,
`babypbk_test_concrete.mlir`, `escalarmulw4table_concrete.mlir`,
`sha256_2_test_concrete.mlir`) shows 4 byte-identical and the 5th
differing only by the same pre-existing, unrelated pure-function-ordering
nondeterminism already documented above (confirmed via 3 repeated runs of
the *unmodified* code producing different orders) — no content change
anywhere. The new `-p`/`--prime` CLI flag was confirmed to parse and
thread through `main_execution.py` without error (`llzk2core.py -s ... -p
bn128`); the full `complete_avazar.py` pipeline itself couldn't be
exercised end-to-end in this environment (the `circom`/`circom-llzk`/
`avazar_tool` Rust binaries it shells out to aren't built here).

## 40. `SCFWhile`/`SCFFor`/`SCFIf`/`SCFExecuteRegion.update_variables` weren't stripping component/semantic suffixes before matching the rename dict

**Reported:** `outcome.csv`'s `babypbk_test_concrete.mlir` row (and 4
others — see below), failing `llzk_cli` symbolic execution with
`seArrayCopy: failed to get array variable: Variable '%115#1_@in' not
found`, alongside the observation that `%115_aft2780#1_@in` (the correctly
renamed form) already appears elsewhere in the same `.core` file, at
`L2768` — the emitted `array.copy` at `L2773-2774` was the only place
still referencing the stale, unrenamed `%115#1_@in`.

**Root cause**, confirmed directly in the code and against the real
`.mlir`/`.core` text: `SCFWhile.parse` (`scf.py:806-833`) tags every
body-computed result name in a nested block with a `_bef<cursor>`/
`_aft<cursor>` suffix by calling `op.update_variables(rename)` on every op
in that block, where `rename` maps *bare* base names (e.g. `"%115"`) to
their tagged form. Ordinary flat operations resolve this through the base
class (`core.py:296-305`), which uses `_apply_rename` (`core.py:227-239`)
— it strips a trailing `#<idx>[_@field...]` suffix off a name like
`%115#1_@in`, matches the bare `%115` against the rename dict, and
reattaches the suffix. But `SCFWhile.update_variables` (and the identical
pattern in `SCFIf`, `SCFExecuteRegion`, `SCFFor`) instead did a **raw
`if name in rename`** dict lookup on `init_args`/`iter_args`' init-value,
`results`, `condition`, `iv`/`lb`/`ub`/`step` — which can never match a
suffixed name like `%115#1_@in`, since the dict only ever holds bare base
names. Traced the exact real-world shape via `babypbk_test_concrete.mlir`:
an outer `scf.while`'s body defines `%115:2 = scf.if ...` and is
immediately followed by an inner `scf.while (%arg8 = %115#1) ...` — when
the outer while's own `_aft2780` rename pass reaches the inner while
(itself just another op in the outer's `after_body`), `SCFWhile
.update_variables` silently left the inner while's own `init_args` entry
for `%115#1_@in` untouched, while the `scf.if`'s own result (and every
other ordinary-op reference to `%115` in the same scope) got correctly
renamed — producing exactly the observed mismatch.

Also confirmed, per user discussion, that pre-expanding the rename dicts
at construction time (so a plain `in`-check would suffice) is not a viable
simplification: the `_@field` tags are only computed later, during
`to_core` (`_container_field_var`, `array.py:111-113`, driven by
`ctx: TranslationContext`, which doesn't exist yet at `parse()` time), so
they can't be enumerated when the rename dict is built; and even the
purely-numeric `#N` component suffix can't be pre-expanded away, since a
multi-result def is stored as one `SSAVar` with `n_components=2`, not two
separately-keyable objects. `_apply_rename`'s strip-then-reattach approach
at *apply* time is the only point where both pieces of information (the
base name, known early; the full suffixed reference, only known at rename
time) are simultaneously available.

**Fix:** `scf.py` now imports `_apply_rename` from `core.py` and routes
every one of the affected fields — `SCFWhile.results`/`init_args`' init-
value, `SCFFor.results`/`iv`/`lb`/`ub`/`step`/`iter_args`' both halves,
`SCFIf.condition`/`results`, `SCFExecuteRegion.results` — through it
instead of the raw dict-membership check. A strict generalization: for a
name with no `#` or no dict match, `_apply_rename` behaves identically to
the old check.

**Verified:** 5 new tests in `tests/test_scf_parse.py` — one direct
`update_variables` unit test per class (`SCFIf`/`SCFExecuteRegion`/
`SCFFor`/`SCFWhile`), each constructing the op directly and asserting a
component/field-suffixed operand name is correctly renamed while an
un-listed own-binder name is left alone; plus one integration test
(`test_while_parse_nested_while_init_val_sourced_from_outer_if_result_gets_renamed`)
reproducing the exact `babypbk` shape end-to-end through `SCFWhile.parse`
(outer while → `scf.if` defining a multi-result value → inner while
consuming component `#1` as its own init-value), asserting the inner
while's init-value picks up the outer's `_aft0` tag with the `#1_@in`
suffix preserved. Confirmed 4 of the 5 new tests fail on the pre-fix code
(via `git stash`) and all pass after. Full suite: 560 tests, up from 555,
zero regressions.

End-to-end: re-ran the full `llzk2core.py` pipeline (Python translation +
a real `llzk_cli` run) on all 5 previously-failing files
(`babypbk_test_concrete.mlir`, `eddsamimc_test_concrete.mlir`,
`eddsaposeidon_test_concrete.mlir`, `escalarmulfix_test_concrete.mlir`,
`pedersen2_test_concrete.mlir`) — all 5 now complete symbolic execution
and produce valid SMT JSON, with zero `seArrayCopy`/`not found` errors.
`babypbk_test_concrete.core`'s `L2773-2774` now correctly emit
`%115_aft2780#1_@in`/`@base`, matching every other reference to the same
value. A before/after translation-only (`.core`, no `llzk_cli`) diff
across every `circomlib_examples/*.mlir` file confirmed exactly 8 files
differ — the 5 fixed files plus `sha256_2_test_concrete.mlir`/
`sha256_test448_concrete.mlir`/`sha256_test512_concrete.mlir` (whose
`.core` diff was independently confirmed to be pure, pre-existing
pure-function-ordering nondeterminism per §39, unrelated to this change —
re-running the *same*, fixed code twice reproduces that same diff, while
the 5 actually-relevant files are byte-for-byte deterministic across
reruns) — with every fixed file's diff consisting exclusively of the
expected `_bef`/`_aft`/`_w`/`_f`-suffix corrections. The other two known
pre-existing Python-level failures (`eddsa_test_concrete.mlir`,
`pointbits_loopback_concrete.mlir`, §18/§38) are untouched, as expected —
this fix is scoped entirely to `update_variables`'s renaming, not the
`_extract_step` code path those two hit.

## 41. `components_index_sequences` (§36) never actually fired for a real, `llzk_cli`-shaped `scf.while` population site — `sigmaF`/`sigmaP` collapsed to one generic signal name

**Reported:** the user's own generated `poseidon3_new.mlir`/`.json` (unrelated to the `outcome.csv` failures — this file already gets past `llzk_cli` successfully) showed `@PoseidonEx_69`'s `vars_info` collapsing all 24 real `sigmaF#i#j` instances (an 8x3 array of `Sigma()` sub-components) into a single bare `sigmaF.in` entry, with no `.out` entries at all, even though `components_info` already correctly listed all 24 names. The user's own hypothesis ("the counts or something like that still is not resolved correctly") was correct.

**Root cause, part 1 — `array_member_base`'s block-arg blind spot:** `struct.py`'s §36 pre-pass (`_collect_population_write_candidates`, `_walk_array_component_population`) gates a population-write candidate with `op.arr_ref.name in array_member_base`. For a member like `sigmaP` whose counting array *is* iter-arg-threaded through an `scf.while`, the real population write inside the after-region references the array via that region's own block-arg name (e.g. `%arg9`), never the name `array_member_base` was registered under. Nothing resolved the block-arg back to the registered identity, so `components_index_sequences` came out empty for the whole macro (confirmed empirically, not just for `sigmaF`/`sigmaP`).

**Fix, part 1:** added `_while_after_arg_pairs` (`struct.py`) alongside the existing `_while_iter_arg_pairs` — both now share a `_while_flat_result_names` helper rather than duplicating the "flatten `op.results`" computation. `_walk_array_component_population` now builds a locally-extended `array_member_base` when recursing into an `scf.while`'s `before_body`/`after_body`, aliasing that region's own block-arg name to the same registered member wherever the flattened result component it corresponds to is already a known key — threaded through both the `_collect_population_write_candidates` call and the recursive `_walk_array_component_population` call for that sub-body, so it also propagates correctly through further nesting (mirroring `_collect_while_iter_args`'s own identical multi-level requirement for `$inputs` pods).

**Root cause, part 2 — discovered only after part 1 was verified end-to-end:** `sigmaP` came back fully fixed (57/57), but `sigmaF` only resolved 9/24 — exactly its first of four textually-separate population sites in `poseidon.circom` (`PoseidonEx`, lines 84-186: `sigmaF[r][j]` is populated across 4 disjoint loops, not one). A dedicated investigation (instrumenting the real translator against `poseidon3_test_concrete.mlir`) found `array_member_base`'s gate was never actually the blocker for `sigmaF` at all — its counting array (`%array_118`) is a plain, directly-referenced top-level SSA name, not iter-arg-threaded, so part 1's fix was orthogonal here (necessary and correct for `sigmaP`, coincidental for `sigmaF`'s first site). The real remaining gap was in `_trace_to_enclosing_loop`/`_resolve_population_nest_sequence`:
- Sites 2 and 4 (`r` fixed at 3 and 7 — a single value, no loop needed for that dimension): `_resolve_population_nest_sequence` called `_trace_to_enclosing_loop` unconditionally on *every* dimension and aborted the entire write's resolution the instant any one dimension wasn't loop-driven, even though the other dimension resolved fine.
- Site 3 (`r = nRoundsF/2 + r_local`, i.e. `4 + r`, where `r` *is* loop-driven): the index is `felt.add %felt_const_4, %arg5` then `cast.toindex`, not a bare identity cast like the working site 1 — `_trace_to_enclosing_loop` only unwrapped `CastToIndex`/`CastToFelt`, with no handling for a constant affine offset between the loop's own counter and the final index.

**Fix, part 2:** `_trace_to_enclosing_loop` now accepts `const_map` and returns `(loop, offset)` — extended to walk through a `felt.add` hop (either operand order) between a loop's own counter and the final index, accumulating the constant into `offset` (0 for the ordinary identity-chain case, unchanged from before). `_resolve_population_nest_sequence` now allows a dimension to resolve as a plain compile-time constant (via `const_map`, independent of any loop) instead of requiring every dimension to be loop-driven, and applies each loop-driven dimension's own `offset` when combining loop sequences into the final index tuples. A write with every dimension already loop-driven and no offset (today's only previously-supported shape) produces byte-identical output — confirmed via a real-fixture regression check (`arbitrary_traversal_array_components_concrete.mlir`, the original N-D motivating case for §36) showing zero diff before/after.

**Deliberately scoped to `felt.add` only** (per explicit user direction, and recorded in DECISIONS.md): multiplication, subtraction, or any other index transform is out of scope — no real example needs it yet. A future, fully general version would identify index variables and *simulate* their update expressions directly (the same shape as the existing loop-bound trip-count simulator, `core_utils.py`'s `construct_function_from_expressions`/`infer_iteration_sequence_from_expressions`), rather than pattern-matching individual ops one at a time.

**Verified:** 9 new tests — 6 in `TestTraceToEnclosingLoop` (`struct.py`'s existing test class: `felt.add` with either constant-operand order resolves with the correct offset; both-operands-unknown and an unrelated op like `felt.mul` still correctly return unresolved) and 2 in `TestFindArrayComponentPopulationSequences` (an `scf.while` population write referencing the array via its own after-region block-arg name, both directly and nested inside an `scf.if` "checkpoint" — the exact real shape that motivated part 1). Full suite: 566 tests, up from 557 (9 new here, on top of the +5 from §40 earlier this session), zero regressions. End-to-end (Python-level — both real Poseidon files are currently blocked from a real `llzk_cli` run by the separately-deferred dead-branch bug below, on an unrelated code path): re-translating `poseidon3_test_concrete.mlir` now resolves `ctx.array_component_index_sequences["@PoseidonEx_69"]["sigmaF"]` to the full, correct **24/24** entries — `(0,0)` through `(7,2)`, all four r-ranges (`0-2`, `3`, `4-6`, `7`) each with `j=0,1,2`, in true execution order — and `sigmaP` remains **57/57**. A full translate-only sweep across every `circomlib_examples/*.mlir` file shows zero new failures (the same 2 pre-existing, unrelated Python-level failures as before, `eddsa_test_concrete.mlir`/`pointbits_loopback_concrete.mlir`, §18/§38).

**Correction (follow-up investigation, same session) — later itself corrected again, see §42:** first re-checked against `poseidon3_test_concrete.mlir` only and concluded `.out` was already fine (25/25 for `sigmaF`, matching `.in`) as a side effect of the fix above. That check was against a file whose counting array happens *not* to exercise the gap §42 actually found — the user caught this by pointing at a second real file (`poseidon3_new.mlir`) where `sigmaF.out` was confirmed genuinely absent. See §42 for the real root cause and fix; `poseidon3_test_concrete.mlir`'s own `sigmaF`/`sigmaP` `.out` naming was never actually broken (still 25/25 there), so that part of this note stands — only the broader "this generalizes to every file" conclusion was wrong. The `sigmaP#56`/`llzk_cli`-inlining finding immediately below is unrelated to the `.out` mistake and remains independently valid (re-confirmed in §42's own verification).

## 42. `_annotate_array_component_reads`/`pod_to_member` had the exact same `scf.while` aliasing gap as §41's `.in` fix — plus a second, deeper gap only a real second file exposed: sequential *sibling* while loops, not just nesting

**Reported:** the user pointed at `poseidon3_new.mlir`/`.core` (a real file already in the repo, structurally different from `poseidon3_test_concrete.mlir`) and correctly refuted my own prior conclusion in §41's "Correction" note above — `sigmaF.out` was confirmed, via plain `grep`, to be completely absent from that file's `.core` output, contradicting "already fixed."

**Root cause, part 1 (same class of bug as §41, different function):** read `poseidon3_new.mlir:328380-328470` directly. The real `sigmaF` population site there is `%567` (an `scf.while`) nested inside `%415` (another `scf.while`)'s own `after_body`, referencing the counting-pod array via `%567`'s own after-region block-arg (`%arg10`). `pod.write %586[@comp] = %597` (the call's result) is exactly the shape `_annotate_function_calls` expects — but `pod_to_member["%586"]` was never set, because `_annotate_array_component_reads` (`struct.py:184-227`, the function that's supposed to set it from `%586 = array.read %arg10[...]`) had the *identical* unpatched `op.arr_ref.name in array_member_base` gate §41 fixed in a *different* function (`_walk_array_component_population`) — I never touched this one. `poseidon3_test_concrete.mlir` didn't expose it because that file's counting array is a plain, directly-referenced top-level name, never iter-arg-threaded; `poseidon3_new.mlir`'s is.

**Root cause, part 2 (found only after part 1's first fix attempt still left the bug half-fixed):** naively porting §41's per-recursion-level "extend `array_member_base` for this one `scf.while`'s own before/after block-args" approach into `_annotate_array_component_reads` fixed *some* call sites (`sigmaP`, most of `sigmaF`) but not all — direct instrumentation (`_find_array_component_bases`/`_collect_while_region_array_aliases` run standalone against the real parsed `@PoseidonEx_69` body) showed `array_member_base` registers `sigmaF` under `%421#1`, but the broken call sites sit inside `%415`/`%567` — a *completely different* pair of whiles, with **no nesting relationship to `%421` at all**. `sigmaF`'s real population is FOUR disjoint sites (mirroring `poseidon.circom`'s four separate loops over disjoint row ranges), run as sequential **sibling** `scf.while`s — each site's own `while` takes the *previous* site's own result as its own init value, not nested one inside another. Only the *last* site (`%421`) is what the post-loop bulk-copy — and so `array_member_base` — directly registers. A per-`scf.while`, single-direction (parent registers before recursing into child) approach can never resolve the first three sites, because the registered identity is discovered *last* in the chain, not first.

**Fix:** replaced the ad-hoc per-level threading in both `_walk_array_component_population` and `_annotate_array_component_reads` with a single, shared, correct mechanism: `_collect_while_region_array_aliases` (`struct.py`) recursively collects every `scf.while`'s own equivalence pairs — `(before-arg, own result)`, `(before-arg, own init value)`, `(after-arg, own result)`, and critically `(own result, own init value)` — the last one being what lets resolution walk *backward* through a sequential sibling chain, not just forward through nesting. `_build_component_naming_maps` (Part 2b) then resolves these to a **fixpoint** (repeatedly propagating a known member to its paired name, in *either* direction, until nothing changes — not a single forward pass, since the direction that resolves each pair isn't knowable in advance) before either `_annotate_array_component_reads` or `_find_array_component_population_sequences` ever runs; both of those went back to their original, simple `op.arr_ref.name in array_member_base` form, since `array_member_base` is now already fully resolved by the time they see it — mirroring how `ctx.input_pod_to_member` is already fully populated before `_annotate_input_array_reads` runs for the analogous `$inputs`-pod case.

**Verified:** `TestCollectWhileRegionArrayAliases` (3 new tests: single-while equivalence pairs, nested-while fixpoint resolution, and — the case that actually caught this — a 4-site sequential-sibling chain resolving entirely backward from only the last site's registered identity) and `TestBuildComponentNamingMapsArrayOfComponentsNestedWhile` (a full `_build_component_naming_maps` integration test with a real doubly-nested `scf.while` population site, confirming the call inside the inner while's own after-body gets `_member_hint` stamped correctly). Full suite: 570 tests, up from 566, zero regressions. End-to-end against **both** real files this time: re-translated `poseidon3_new.mlir` and confirmed all 8 real `call @Sigma_1(...)` sites in its `.core` output now read `call @Sigma_1(sigmaF.in) to sigmaF.out` / `sigmaP#0.out` / `sigmaP.out` — zero raw `%NNN_..._@out`-shaped fallback names remaining (previously only 2 of 8 resolved even after part 1's first attempt). Re-confirmed `poseidon3_test_concrete.mlir` unaffected (still all 8 sites correctly named) and `arbitrary_traversal_array_components_concrete.mlir`'s own `components_index_sequences` output byte-identical to before this fix (the canonical N-D fixture §36 was built against). `poseidon3_test_concrete.mlir`'s own `sigmaF`/`sigmaP` index-sequence counts (24/24, 57/57) also unchanged. A full translate-only sweep across every `circomlib_examples/*.mlir` file: zero new failures (the same 2 pre-existing, unrelated ones as always, `eddsa_test_concrete.mlir`/`pointbits_loopback_concrete.mlir`).

**Also investigated this session, separately, and explicitly deferred per user direction (not fixed):** Poseidon's `assert(0); return [0];` dead-stub branches (in `poseidon_constants.circom`'s `POSEIDON_C`/`M`/`P`/`S`) surviving into `.core` and tripping the newer `llzk_cli` binary's stricter then/else shape check (`Type mismatch for variable ... in then-branch and else-branch`), affecting `babypbk_test_concrete.mlir`/`eddsamimc_test_concrete.mlir`/`eddsaposeidon_test_concrete.mlir`/`escalarmulfix_test_concrete.mlir`/`pedersen2_test_concrete.mlir`/`poseidon3_test_concrete.mlir`/`poseidon6_test_concrete.mlir`/`poseidonex_test_concrete.mlir`/`smtprocessor10_test_concrete.mlir`/`smtverifier10_test_concrete.mlir`. Extensively investigated (ruled out array-padding via direct `llzk_cli` testing on minimal reproductions; confirmed `llzk_cli` never substitutes real call-site arguments into a callee, so the real fix needs genuine per-call-site specialization of the four `POSEIDON_*` dispatch functions plus new dead-branch elision in `SCFIf.to_core` — both nontrivial, see this session's own investigation notes). Deferred per explicit user direction ("this has to do for now with llzk_cli").

## 43. `pod_to_member` (scalar subcomponent naming) had the identical unaliased `scf.while` gap as §41/§42 — a *third* independent occurrence, so all three registries are now unified onto one mechanism

**Reported:** in `@Poseidon_70` (the `Poseidon(nInputs)` template wrapping `PoseidonEx`), the translated call to `PoseidonEx_69`'s compute was missing the semantic name `pEx.out` on its output — confirmed only in `poseidon3_new.mlir` (`call @PoseidonEx_69(...) to %20_aft341263_@out`, a raw fallback name); `poseidon3_test_concrete.mlir` already translated this correctly.

**Root cause:** `poseidon3_new.mlir`'s real `@Poseidon_70::@compute` body registers `pEx`'s own counting pod correctly at the top level (`%8 = pod.read %pod_0[@comp]; struct.writem %self[@pEx] = %8` → `pod_to_member["%pod_0"] = "pEx"`, Part 2 of `_build_component_naming_maps`, `struct.py:892-906`) — but that same pod is *also* threaded through an `scf.while`'s own iter-args as `%arg2`, and the real, live call site (the one that actually fires, since `nInputs=2` needs two loop iterations) writes into `%arg2[@comp]`, never `%pod_0[@comp]` directly. `pod_to_member` had no entry for `%arg2` — the exact same missing-alias problem §41 fixed for `array_member_base` (array-of-components) and §42 generalized (sequential sibling chains), just in Part 2's separate `pod_to_member` registry, which neither earlier fix touched.

**Fix — unified all three registries onto one mechanism, per explicit user direction** (three independent occurrences of the identical bug class across three separate registries was itself judged sufficient evidence for a general fix, not a fourth ad-hoc patch): extracted the fixpoint-resolution loop into a shared `_resolve_while_region_aliases(aliases, target_dict)` (`struct.py`), and **replaced Part 1's own, narrower, single-pass `_collect_while_iter_args`/`trace_source`/`result_to_init` mechanism** (used for `ctx.input_pod_to_member`, the `$inputs`-pod case) with the same general `_collect_while_region_array_aliases` + fixpoint resolution already proven for `array_member_base` in §41/§42 — since the general fixpoint is a strict superset of what `trace_source`'s single top-level-only chain-walk did (the `(own_result, own_init_val)` equivalence pair already covers exactly that chain, plus arbitrary nesting depth and sequential-sibling chains `trace_source` never handled). `_collect_while_iter_args`/`trace_source`/`result_to_init` were retired entirely (confirmed via `grep` they had no other callers). All three registries — `ctx.input_pod_to_member`, `pod_to_member`, `array_member_base` — now go through the identical seed-then-resolve shape.

**Verified:** new `TestBuildComponentNamingMapsScalarSubcomponentInWhile` (a full `_build_component_naming_maps` integration test with a pod threaded through an `scf.while`'s own iter-args, confirming the call inside the loop gets `_member_hint` stamped). Confirmed the *existing* `TestBuildComponentNamingMapsNestedWhileInputs` test (Part 1's own, previously-passing nested-`$inputs` case) still passes **unchanged** — proves the Part 1 rewrite doesn't regress the one shape that already worked. Full suite: 571 tests, up from 570, zero regressions. End-to-end against both real files: re-translated `poseidon3_new.mlir` and confirmed `@Poseidon_70`'s `.core` output now reads `call @PoseidonEx_69(...) to pEx.out` at **both** call sites (was a raw fallback name at the real, live one). Re-confirmed `poseidon3_test_concrete.mlir` unaffected (still correct at both sites) and — since Part 1 was genuinely rewritten, not just extended — re-ran every check from §41/§42 to confirm zero regression there too: `sigmaF`/`sigmaP` call naming still fully resolved (8/8 `call @Sigma_1` sites, both files), `arbitrary_traversal_array_components_concrete.mlir`'s `components_index_sequences` output still byte-identical. A full translate-only sweep across every `circomlib_examples/*.mlir` file: zero new failures (the same 2 pre-existing, unrelated ones as always).

## 44. `components_info` extended to cover heterogeneous idx-pod members (`ark#i` → `@Ark_i`)

**Reported:** the user asked why `ark#i` (`poseidon3_new.mlir`'s heterogeneous idx-pod array-of-components member, §33) never appears in `components_info` — noting `ark`'s own signal naming was already recognized correctly downstream, just not this metadata field.

**Root cause:** `StructDef.to_core`'s member-scan loop (`struct.py:~1303-1334`) builds `ctx.member_to_struct`/`components_info` only for homogeneous array-of-components members (real `!array.type<N x !struct.type<...>>`) and plain scalar struct members. A heterogeneous idx-pod member (§33's `!pod.type<[@idx_0: !struct.type<@Ark_0...>, ...]>` shape, one genuinely different struct type per index) is detected earlier by `_is_idx_pod_component_member` and `continue`s straight past the `subcomponent_members` registration — captured only into `idx_pod_member_types`, which feeds the separate naming pre-pass (`_annotate_idx_pod_component_reads`) but never the JSON metadata.

**Investigated before changing anything (per explicit "ensure this is general enough, no other point affected" instruction):** traced `signal_renaming.py`'s `process_components` in full for an `ark` call. Since `ark`'s `.core`-level naming is *already* fully resolved at emission time (`_annotate_idx_pod_component_reads` stamps `pod_to_member[...] = "ark#N"` before the call is ever printed, e.g. `call @Ark_0(ark#0.in) to ark#0.out`), `extract_component(metadata)` returns the *already-complete* string `"ark#0"`, and `process_components` unconditionally appends its own `#{occurrence}` suffix on top (there being no `components_index_sequences` entry for idx-pod members), producing a doubly-suffixed `"ark#0#0"` that can never match a `components_info` key of `"ark#0"` — whether or not that key exists. So adding the new entries is **provably inert** with respect to `process_components`'s existing rename logic: no collision, no accidental new match, no behavior change there. This matches the user's own observation that `ark`'s signal naming already works independently of this metadata field. Confirmed no change to `signal_renaming.py` was needed.

**Fix:** extended the member-scan loop's idx-pod branch to also populate `subcomponent_members` for each `@idx_N` field, reusing `_idx_pod_child_name` (`pod.py`) — the *same* function `_annotate_idx_pod_component_reads` already uses to stamp the matching `.core`-level call names, guaranteeing the new `components_info` keys are byte-identical to what's actually emitted — and the same `struct_type_name(...).split("::")[-1]` pattern already used for the homogeneous case (which keeps the leading `@`, matching the user's requested `"@Ark_i"` format):

```python
idx_fields = _is_idx_pod_component_member(type_str)
if idx_fields is not None:
    idx_pod_member_types[member_name] = idx_fields
    for record, field_type in idx_fields.items():
        child_name = _idx_pod_child_name(member_name, record)
        subcomponent_members[child_name] = struct_type_name(field_type.name).split("::")[-1]
    continue
```

**Verified:** new `TestStructDefToCoreComponentsInfoIdxPod` (`tests/test_struct_parse.py`) — a full `StructDef.to_core` integration test (parsed via `LLZKParser`, not hand-built objects — this was the first test exercising this member-scan loop at all) with an idx-pod member alongside a plain scalar member, confirming both land correctly in `ctx.member_to_struct` with no collision. Full suite: 572 tests, up from 571, zero regressions (the 8 pre-existing `test_signal_renaming.py` failures are unrelated — caused solely by the user's own uncommitted `signal_renaming.py` debug scaffolding, confirmed via `git stash` isolating exactly that file). End-to-end against the real file: re-translated `poseidon3_new.mlir`, confirmed `components_info["@PoseidonEx_69"]` now contains all 8 entries (`"ark#0": "@Ark_0"` through `"ark#7": "@Ark_67"`), and cross-checked every one against the actual emitted `.core` call text (`call @Ark_0(ark#0.in) to ark#0.out`, etc.) — exact match at every site.

## 45. Felt `scf.while` trip-count simulation never terminated for a "count down to and including 0" loop (`ge(arg, 0)` after field wraparound)

**Reported:** in `report_zisk_reduced/recursivef_concrete.mlir` (`@VerifyPoW_11::@compute`, `pow.circom`), a small `scf.while` decrementing a `!felt.type` counter (condition `bool.cmp ge(%arg3, 0)`, body `felt.sub %arg3, 1`) never finished translating — `count_iterations` ran past its 1,000,000-iteration safety cap and raised. The user correctly suspected the decrement itself.

**Root cause:** confirmed by extracting the real `@VerifyPoW_11` struct (plus its `poly.template` wrapper and every earlier struct it depends on) into a scratch repro and running it through the real parser + `to_core`. A 64-bit exponent is populated by two sequential sibling `scf.while`s: `%22` (63→42, 22 iterations) translated fine; `%23` (41→0) is exactly where the `RuntimeError` fired. `_resolve_comparison_recurrence` (`core_utils.py`) builds `compare_func` for `ge`/`le` (after `gt`/`ge` normalize to `lt`/`le`) as a *raw, unsigned* Python-int comparison. `construct_function_from_expressions` already reduces every update step modulo the field's prime (correct and required — decrement below 0 wraps to `prime-1`, matching real field arithmetic). Once `%23`'s counter reaches 0 and decrements once more, `felt.sub(0, 1)` wraps to `prime-1` — under the unsigned comparison, `0 <= prime-1` is still `True`, so "the loop should have stopped" never goes false, and the simulation grinds toward the field's own prime (~2^254 for bn128) before hitting the cap.

This is a distinct gap from `TestPrimeAwareSimulation`'s existing `ne`-predicate wraparound test (§ pre-existing): that test's *bound* is itself pre-wrapped (an equality check against the exact wrapped value standing for "-1") — equality is sign-convention-independent, so it never needed this. An *inequality* (`lt`/`le`/`gt`/`ge`) against an un-wrapped bound (the ordinary way a circuit compiler emits "count down to and including 0") genuinely needs to know which side of the field's own midpoint a value falls on — the standard ZK-circuit convention (used pervasively for bounded felt counters) is to interpret a field element `v >= prime/2` as the negative number `v - prime`.

**Fix:** added `_to_signed(value, prime)` (`core_utils.py`) — the canonical signed representative of a raw field element (unchanged below `prime/2`, `value - prime` at or above it) — and applied it to both sides of the `lt`/`le` `compare_func` construction in `_resolve_comparison_recurrence` (`eq`/`ne` untouched — raw-representation equality doesn't depend on sign convention). Since `_ResolvedRecurrence`/`_infer_from_comparison`/`_infer_sequence_from_comparison` (the array-index-sequence pre-pass) all share this one function by design, both the trip-count path and the index-sequence path are fixed together. `_to_signed` is a no-op for any value below `prime/2` — every previously-working loop (nothing in the current suite's counters ever approaches the field's own prime) is unaffected; confirmed empirically that `%22`'s trip count (22) is unchanged by this fix.

**Verified:** new tests in `TestPrimeAwareSimulation`/`TestInferIterationSequence` (`tests/test_core_utils.py`): a `ge`-predicate loop wrapping past 0 (mirrors the real `%23` shape, small `prime=7`) now returns the correct trip count (`3`, was an unbounded runaway before the fix) instead of hitting the safety cap; the mirror `le`-with-bound-on-lhs case; a non-wrapping `ge` case confirmed byte-for-byte unchanged (`22`, matching `%22`'s real shape); the sequence variant (`infer_iteration_sequence_from_expressions`) fixed the same way. Full suite: 554 tests, up from 550 (the same 8 pre-existing `test_signal_renaming.py` failures as always, caused by the user's own uncommitted debug scaffolding, unrelated). End-to-end: re-ran the real `@VerifyPoW_11` reproduction — both `scf.while`s now resolve and the struct's `.core` output shows `repeat 22 { ... }` / `repeat 42 { ... }` exactly as predicted. Ran a full translate-only pass over the *entire* real `recursivef_concrete.mlir` (425,303 lines, 53MB) — completed successfully end to end in ~2 seconds, 261,756 lines of Core emitted, zero errors, confirming no other occurrence of this bug shape remains anywhere in the file.

## Known pre-existing / out-of-scope issues surfaced but not fixed

- **`llzk_cli` inlines a sufficiently trivial subcomponent, leaving no
  `:meta-data "call ..."` annotation for `signal_renaming.py` to act on at
  all** (discovered via §36's end-to-end verification against
  `arbitrary_traversal_array_components_concrete.mlir`'s `IsZero`
  component — a single `felt.mul`, no internal loop). Not something this
  translator's own output controls, and not something `signal_renaming.py`
  can work around (there's no call annotation to consume in the first
  place, regardless of the naming mechanism's own correctness). Not
  investigated further — an `llzk_cli`-internal heuristic, out of this
  translator's own scope. **Second confirmed instance (§41 follow-up):**
  `poseidon3_test_concrete.mlir`'s `sigmaP#56` (the 57th of 57 `Sigma()`
  round instances) — `ctx.array_component_index_sequences` already
  correctly predicts all 57 real indices on the Python side, but the raw
  SMT formula `llzk_cli` produces only ever contains 56 `call @Sigma_1(...)`
  annotations, so `sigmaP#56.in`/`.out` never appear in the final `vars_info`
  regardless of anything this translator does.
- ~~**2-D array-of-components naming**: `poseidon3_test_concrete.mlir`'s
  `@sigmaF : !array.type<8,3 x !struct.type<@Sigma_1::...>>` ... Both
  `_find_array_component_bases` and `_annotate_array_component_reads`
  only handle a single-dimension index ... 6 of the 8 `@Sigma_1::@compute`
  calls fall back to raw SSA names on both `.in` and `.out` as a
  result...~~ — **resolved by §35** (generalized the whole
  array-of-components mechanism, homogeneous and heterogeneous, to N
  dimensions): `@sigmaF`'s calls are now all named (`sigmaF.in`/
  `sigmaF.out`, or `sigmaF#i#j.in`/`.out` for a compile-time-constant
  instance).
- ~~`escalarmulw4table_concrete.mlir`: its while at line 82 ... forces
  per-iteration unrolling ...`~~ — **resolved by §29** (loop unrolling
  removed entirely): `escalarmulw4table_concrete.mlir` and its `_test`/
  `_test3` variants now translate to completion.
- ~~`babypbk_test_concrete.mlir` / `eddsamimc_test_concrete.mlir` /
  `eddsaposeidon_test_concrete.mlir` / `escalarmulfix_test_concrete.mlir` /
  `escalarmul_min_test_concrete.mlir` / `escalarmul_test_concrete.mlir` /
  `escalarmul_test_min_concrete.mlir` / `pedersen_test_concrete.mlir` /
  `pedersen2_test_concrete.mlir`: each hits a `KeyError` in `pod.py`'s
  `to_core` ... a pod-variable-tracking gap ...~~ — **resolved by §32**
  (`ctx.ssa2pod_var`/`ctx.var2const` cleared per function): all nine now get
  past Python translation entirely. Five of them (`babypbk`, `eddsamimc`,
  `eddsaposeidon`, `escalarmulfix`, `pedersen2`) now hit a *different*,
  `llzk_cli`-level `seArrayCopy: ... not found` error instead — see the new
  bullet below, since it's the same *symptom* as §31's original bug but a
  distinct shape not covered by that fix.
- ~~`babypbk_test_concrete.mlir` / `eddsamimc_test_concrete.mlir` /
  `eddsaposeidon_test_concrete.mlir` / `escalarmulfix_test_concrete.mlir` /
  `pedersen2_test_concrete.mlir`: each now translates in Python without
  error, but `llzk_cli`'s symbolic execution rejects the emitted `.core`
  with `seArrayCopy: failed to get array variable: '...' not found` — the
  exact symptom §31 fixed for `poseidon3_test_concrete.mlir` (a reference to
  storage nothing ever allocated), but a different specific shape (surfaced
  by §32's sweep, not investigated further this session — likely another
  nested-pod/`$inputs`-pod flattening gap in the same family as §31, but not
  confirmed).~~ — **resolved by §40** (`SCFIf`/`SCFExecuteRegion`/`SCFFor`/
  `SCFWhile.update_variables` now route every renamed name through
  `_apply_rename` instead of a raw dict lookup): all 5 files now translate
  and pass a real `llzk_cli` symbolic-execution run end-to-end.
- ~~`escalarmul_min_test_concrete.mlir` / `escalarmul_test_concrete.mlir` /
  `escalarmul_test_min_concrete.mlir` / `escalarmulw4table_concrete.mlir` /
  `escalarmulw4table_test_concrete.mlir` / `escalarmulw4table_test3_concrete.mlir` /
  `pedersen_test_concrete.mlir`: each now translates in Python without
  error, but `llzk_cli`'s symbolic execution rejects it with `Variable
  '%steps_N' is a symbolic` — an `llzk_cli`-side limitation with a
  `SymbolicSteps`-driven `repeat` count (§17), unrelated to pod handling;
  not investigated further this session.~~ — **resolved by §38**
  (loop-bound-parametric pure function specialization): all 7 files now
  translate end-to-end through a real `llzk_cli` run, since their shared
  `EscalarMulW4Table_0` callee's `k` parameter is a compile-time constant
  at every one of its call sites.
- `sha256_2_test_concrete.mlir` / `sha256_test448_concrete.mlir` /
  `sha256_test512_concrete.mlir`: each fails `llzk_cli`'s symbolic execution
  with `Spec for function @ssigma1_1 not found` — an unrelated, apparently
  pre-existing missing-spec gap; not investigated this session.
- ~~`smtprocessor10_test_concrete.mlir` / `smtverifier10_test_concrete.mlir`:
  newly discovered (via §32's full sweep) to hit the same already-documented
  `AssertionError: Only inequalities are implemented` (`ne`-predicate
  limitation) as `eddsa_test_concrete.mlir`/`pointbits_loopback_concrete.mlir`
  above — not a new gap, just not previously confirmed against these two
  files specifically.~~ — **resolved by §39** (`bool.ne`/`bool.eq`
  concrete-bound support, plus field-aware/modulo-prime simulation): this
  pair's `ne` turned out to be an unrelated, ordinary compile-time-bounded
  countdown loop, not `sqrt_0`'s runtime-witness shape — see §39.
- `eddsa_test_concrete.mlir` / `pointbits_loopback_concrete.mlir`: both hit
  the identical `bool.and`-conditioned `scf.while` inside a shared `sqrt_0`
  (Tonelli–Shanks modular square root) helper. `bool.and` conditions are now
  handled in general (§18), but this specific loop has three separate,
  compounding blockers of its own: predicate `ne` (unsupported — only
  `lt/le/gt/ge` are handled); the compared variables' initial values are
  `felt.pow(n, ...)` results (`n` being `sqrt_0`'s own parameter), never
  tracked in `ctx.var2const`, so neither is recognized as loop-carried; and
  their per-iteration update flows through a *nested* `scf.while`'s result,
  invisible to the backward-walk since `SCFWhile` doesn't override
  `Operation.result`. This loop's true iteration count is genuinely
  data-dependent on `n` at runtime — not expressible as a concrete int or a
  `SymbolicSteps` formula under the current architecture. See §18 for the
  full trace.

  **§38 update:** confirmed, by tracing all 4 of `sqrt_0`'s call sites
  (2 per file) end to end, that `n` is never a compile-time constant
  either — every call site's argument bottoms out at `array.read` on the
  enclosing component's own 256-bit signal input, a genuine runtime
  witness. So the loop-bound-parametric pure function specialization that
  fixed `EscalarMulW4Table_0` (§38) structurally detects `sqrt_0` as
  loop-bound-parametric too, but correctly aborts and leaves it untouched,
  exactly as designed, since not every call site resolves to a constant.
  Bound to remain unsupported under the current architecture regardless
  (Core's `repeat` only accepts a plain identifier or literal — no true
  per-iteration condition check — so a genuinely data-dependent trip count
  has no representation to fall back to, `bool.ne` support or not).
  Deliberately left unaddressed: confirmed with the user that this
  specific result (`out[0] <-- x` in
  `circomlib/circuits/pointbits.circom:107`) is only ever assigned via
  `<--`, generating no constraint, so this has no correctness impact.

- `struct.writem`'s early-return for struct-typed members (and the
  equivalent pod-typed check) uses a substring check on the member's type
  that would also match an *array* of struct/pod, not just a plain struct
  member. Currently invisible in practice because `@constrain` function
  bodies aren't translated at all yet (a separate, larger gap) — nothing
  currently reads back what these members write. Worth revisiting once
  `@constrain` translation exists.
- A pod field that is itself an *array* of struct/pod (as opposed to a
  scalar struct/pod field) is explicitly asserted against in `PodNew`'s new
  storage-allocation code rather than supported — not exercised by any
  current example, but would need the leaf-size math to account for the
  field's own array dimension on top of its element's flattened size.
- `ctx.input_pod_to_member` and the local `pod_to_member` map (§9) are flat,
  function-wide dicts keyed by SSA/block-arg name. The specific "two loops
  reuse the same block-arg name" collision this bullet used to warn about is
  now resolved as a side effect of §23 (block-arg names are cursor-tagged
  unique at parse time, and `_build_component_naming_maps` reads them
  post-parse) — but a counting-array name collision (the other half of this
  bullet, not a `scf.while` block-arg) is a different, still-flat key and
  wasn't addressed by §23. Not exercised by any current example.
- `GlobalWrite.to_core` (§27) is still an unimplemented stub — no current
  example uses `global.write`, only `global.def`/`global.read`.
- `bool.py`'s `BoolCmp._PRED2CORE` maps both `"le"` and `"ge"` to
  `"bool.ge"` (line ~146) — looks like a copy-paste bug (`"le"` should
  presumably emit a `"bool.le"`-shaped comparison). Spotted incidentally
  while adding §28's constant folding to this file; not fixed here since
  it's a pre-existing, unrelated emission-correctness question (not a
  parsing/folding one) and changing it could alter previously-passing
  examples' emitted Core text — left as a note to revisit deliberately.
