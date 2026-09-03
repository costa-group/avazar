# Design Decisions

Rationale behind non-obvious choices made while extending the component-naming
logic to arrays-of-subcomponents (`array.py`, `struct.py`). Organized by
decision, not chronologically — see `PROGRESS.md` for the narrative of what
was built and in what order.

## 1. Underscore suffix (`last_0`), not bracket-index (`last[0]`)

> **Superseded by decision 28**: the separator itself changed from `_` to
> `#` (`last#0`), unifying with the heterogeneous idx-pod convention
> (decision 23) and generalizing to N dimensions (`last#0#1`). The
> reasoning below for *why a plain-identifier suffix at all*, as opposed
> to `last[0]`, still stands — only the specific character changed.

**Decision:** a compile-time-known instance of an array-of-components member
is named `"{member}_{idx}"` (e.g. `last_0`, `components_1`), not
`"{member}[{idx}]"`.

**Why:** the user's own downstream tooling treats these as plain identifiers
(post-processed via symbolic execution). `[idx]` reads as an array access,
which invites re-parsing it as one; `_idx` reads as a name. It also composes
cleanly with decision 2 below — a name with no numeric suffix at all can
never collide with one that always has one.

## 2. Bare member name for a genuinely symbolic loop index

**Decision:** when a subcomponent array is populated inside a real runtime
loop (`scf.while`/`scf.for` with a non-constant index — e.g.
`ternary_concrete.mlir`'s `Num2Bits_16_325`, instantiated from a Circom
`for` loop translated as `scf.while`), the subcomponent call is named with
the **bare base name only** (`Num2Bits_16_325.in` / `Num2Bits_16_325.out`),
not a guessed or synthetic index.

**Why:** the translator emits the loop body once (a Core `repeat N { ... }`
block represents *all* iterations generically — see decision 4), so there is
no single "instance" to name at translation time; any index we invented
would be fiction. The user's own workflow reconstructs per-iteration names
(`Num2Bits_16_325_0.out`, `Num2Bits_16_325_1.out`, ...) *outside* this
translator, via their own symbolic execution of the emitted loop. Giving them
the plain, unindexed name is the correct handoff point — anything more
specific here would be actively wrong, not just imprecise.

**Superseded for the common case by decision 10**: once a loop's body
contains a `function.call`, the translator now unrolls it instead of
emitting one generic `repeat` body — at which point there *is* a real
instance per copy, and the bare name is resolved into `"{base}#{i}"`
instead (see decision 11 for why `#`, not `_`). The bare name from this
decision is still what you get if such a loop is somehow *not* unrolled
(`LoopIndexedName.resolve(None)`), but that's no longer the expected case
for a loop that instantiates a subcomponent — it would only happen for a
component-array read sitting outside any loop with a call at all.

## 3. A dedicated static constant fold, not `ctx.var2const`

**Decision:** the naming pre-pass (`_fold_index_constants`, and its two
recursive callers `_annotate_array_component_reads` /
`_annotate_input_array_reads`) computes its own notion of "is this SSA value
a compile-time constant," entirely separate from `ctx.var2const`.

**Why:** `ctx.var2const` is *deliberately* imprecise for this purpose.
`SCFFor`/`SCFWhile` (`scf.py`) set `ctx.var2const[iv_or_block_arg] = value`
from the loop's initial value, for legitimate structural reasons (computing
trip counts, asserting nested-loop bounds are known) — and only invalidate
it *after* the whole (single, generic) loop body has been translated, not
per-iteration, because there *is* no per-iteration translation anymore
(decision 4). This makes a genuinely-variable loop index look like a
compile-time constant equal to its lower bound for the entire body. Consuming
`ctx.var2const` for naming (an earlier version of this change did exactly
that) silently mis-labeled every iteration of `ternary_concrete.mlir`'s while
loop as instance `_0`. A from-scratch fold that only ever recognizes
`felt.const`/`arith.constant` literals (propagated through identity casts)
never has this problem, because a loop's own induction/block-arg variable is
never itself the *result* of one of those ops — it's only ever referenced as
an operand, so the fold correctly reports "not constant" for it.

## 4. Naming resolved in a pre-pass, stamped onto the AST node

**Decision:** naming decisions are computed once, before `to_core` runs, and
stored directly on the operation object (`ArrayRead._semantic_base`,
`FunctionCall._member_hint`) rather than recomputed live during `to_core` or
looked up from a `ctx`-level dict at read time.

**Why:** this already was the established pattern for `FunctionCall`
(`_member_hint`, set by `_annotate_function_calls`) before this change; the
array extension just follows it rather than introducing a second scheme.
It also sidesteps a real scoping hazard: two sibling loops in the same
function can reuse the same LLZK-level SSA name for their own induction
variable (`ternary_concrete.mlir` has two separate top-level
`scf.for %arg1 = ...` loops) or the same result name across sibling
`scf.if` branches (the reason `_annotate_function_calls` already builds a
*per-body* SSA def-map instead of one flat one). Stamping the answer onto
the specific Python object, once, from a call site that has full nesting
context, avoids a name collision ever being possible — there's no shared
mutable state that two unrelated branches could clobber. The recursive
folders (`_annotate_array_component_reads`, `_annotate_input_array_reads`)
follow the same discipline one level down: each recursive call gets a
*copy* of the accumulated constant map, not a shared reference, so a
constant folded in one branch can't leak into a sibling.

## 5. Reused `ctx.input_pod_to_member` instead of a parallel map

**Decision:** the array case reuses the existing `ctx.input_pod_to_member`
(originally built for a scalar `$inputs` pod, e.g. `mux.c`) rather than
introducing a separate map for "$inputs array -> member."

**Why:** the existing registration (`struct.py` Part 1, scanning
`struct.writem @member$inputs = value`) already doesn't care whether `value`
is a single pod or an array of pods — the SSA name gets registered either
way. The only genuinely new piece needed was making the *lookup* side
(`ArrayRead`) array-aware, and making sure the registration also covers the
name a loop body actually uses (decision 6). Reusing the map means `PodNew`
and `ArrayRead` share one source of truth for "does this array/pod carry a
semantic name," instead of two maps that could drift apart.

## 6. Aliasing a `scf.while`'s block-arg name to its traced source

**Decision:** Part 1 now also registers `ctx.input_pod_to_member[block_arg]
= base` for every `scf.while` iter-arg, in addition to the pre-existing
registration keyed by the (possibly multi-hop-traced) initial value.

**Why:** code *inside* the while's after-body refers to a loop-carried
array by its own block-argument name (e.g. `%arg3`), which is a different
SSA name from the one the value had before entering the loop (e.g.
`%array_1`) — the two are linked only through `scf.while`'s `init_args`.
Without this alias, `ArrayRead.to_core` (running with `arr_ref.name ==
"%arg3"`) would look up a map keyed by `"%array_1"` and find nothing,
silently falling back to raw naming for every read inside the loop — which
is exactly the bug this whole change is about, just recurring one level
down. The alias is resolved through the existing `trace_source` chain
(already needed for `scf.while` result chaining), so multi-hop cases are
handled the same way as the pre-existing scalar-pod case.

## 7. Counting-pod-array member naming reuses `pod_to_member`, not a new hint field

**Decision:** `_find_array_component_bases` / `_annotate_array_component_reads`
feed their results into the *same* `pod_to_member` dict that
`_annotate_function_calls` already reads to set `FunctionCall._member_hint`
— no changes to `_annotate_function_calls` itself, and no new field on
`FunctionCall`.

**Why:** the existing mechanism already does exactly the right thing once
it has a `pod_ssa -> member_name` entry — it doesn't need to know *how*
that entry was derived (from a scalar pod's own `struct.writem`, or from a
constant/symbolic array-of-components read). Feeding the same map keeps the
"a component's output is named `member.out_arg`" logic in exactly one
place, and the array-of-components detection is purely additive: it only
ever *adds* entries that wouldn't otherwise exist, never changes how an
existing entry is consumed.

## 8. `_semantic_base`, not `_friendly_base`

**Decision:** the field name on `ArrayRead` is `_semantic_base` (originally
prototyped as `_friendly_base`).

**Why:** the codebase already had its own vocabulary for "human-readable
name standing in for a raw SSA name" — `pod.py` calls it a "semantic name"
(`"semantic names (e.g. "mux.c") instead of the default SSA-derived
names"`). "Friendly" would have been a second term for the same concept.
Matching existing vocabulary was judged more valuable than the specific
word chosen.

## 9. Scope explicitly left unhandled: repeated names across *unrelated*
   array-of-components members

**Decision:** `ctx.input_pod_to_member` and `pod_to_member` remain flat,
function-wide dicts. No additional scoping was added beyond what decisions
4 and 6 already provide.

**Why:** every example seen so far (`three_subcomponents_array_concrete.mlir`,
`ternary_concrete.mlir`) has at most one array-of-components pattern that
would reuse a given block-arg/counting-array name within a function — the
sibling-collision cases that *do* occur in practice (two `scf.for` loops
both using `%arg1`, two `scf.if` branches both defining `%18`) are already
handled by the per-scope-copy discipline (decision 4). Adding further
scoping for a case not yet observed would be speculative; noted in
`PROGRESS.md`'s "known issues" instead of built preemptively.

## 10. Unroll a loop only when its body contains a `function.call`

> **Superseded by decision 19** (`PROGRESS.md` §29): loop unrolling was
> removed entirely — naming is now resolved afterwards by `llzk_cli`.
> Kept here as historical record of why unrolling existed in the first
> place.

**Decision:** `SCFFor`/`SCFWhile` keep translating a loop as a single Core
`repeat N { ... }` block *unless* `_contains_function_call` finds a
`function.call` anywhere in the body (recursively) — only then do they emit
one literal copy per iteration instead.

**Why:** unrolling exists purely to give each iteration's subcomponent a
distinct name (decision 2's superseding case) — a loop with no call has
nothing that needs distinguishing, so unrolling it would only bloat the
output for zero benefit and reintroduce exactly the concern decision 4 of
the earlier "no-unroll" change (see `PROGRESS.md` §3) was written to avoid.
Gating on "does it actually need this" rather than unrolling unconditionally
keeps the blast radius provably limited: every loop in the two example files
that doesn't contain a call (the per-instance init loop, the bulk-copy loop,
`Num2Bits_0`'s own bit-decomposition loop) is untouched, verified by diffing
`three_subcomponents_array_concrete.mlir`'s output byte-for-byte against the
pre-change version.

## 11. `#` for an unroll-only index, never `_`

> **Superseded by decision 19**: unrolling removed, so this index form no
> longer exists — a non-constant index is always just the bare base name.

**Decision:** an index that's concrete only because the translator chose to
unroll the loop (`Num2Bits_16_325#0`) uses `#`, strictly distinct from the
`_` used when the index was already a compile-time constant in the source
IR (`last_0`, decision 1).

**Why:** these are semantically different kinds of "constant" from the
caller's perspective. `last_0` reflects something the *original circuit*
already fixed — two genuinely distinct signals the LLZK frontend chose to
lay out as array slots 0 and 1. `Num2Bits_16_325#0` reflects a choice *this
translator* made (unroll a loop) to let one name stand in for what the
source still expresses as a single parameterized loop body. Keeping them
visually distinct means the user's downstream tooling can tell "the source
already named this instance" apart from "the translator peeled this
iteration off a loop for you" without re-deriving it from context, and the
two forms remain collision-free by construction (one always has a `_digit`
tail, the other always a `#digit` tail, decision 1's bare form has neither).

## 12. No per-iteration suffix on ordinary variables when unrolling

> **Superseded by decision 19**: with unrolling removed, this decision's
> premise (a loop body ever being duplicated per iteration) no longer
> applies at all.

**Decision:** unrolling a loop's body N times reuses/reassigns every
ordinary (non-component) variable name identically in each copy — no
`_it0`/`_it1`-style suffixing, unlike the pre-`repeat` unroll this codebase
used to have (`PROGRESS.md` §3).

**Why:** the old unroll suffixed everything because it was standing in for
true SSA semantics, where the *same* name defined twice would be a
redefinition. Core's execution model already isn't SSA at this level —
`repeat N { %x = ... }` already means "reassign `%x`, N times, in sequence,"
and that's exactly what an unrolled loop needs too: an ordinary temp like
`%7_aft95 = felt.add %arg2 %6_aft95` computes a real, current value each
pass, and nothing downstream needs to distinguish *which* pass produced the
value that's live right now, only that it's current. Suffixing it would add
noise without adding information — the only thing that genuinely needs a
per-iteration identity is a component's semantic name, because that's the
one thing the user's downstream tooling keys off of.

## 13. `ctx.unroll_index` resolved at the point of use, not baked into the pre-pass

> **Superseded by decision 19**: `ctx.unroll_index` and `LoopIndexedName`
> were deleted outright — there is no more resolve-at-point-of-use step,
> since a non-constant index now always just yields the bare base name
> directly from the pre-pass.

**Decision:** the naming pre-pass (`_annotate_input_array_reads` /
`_annotate_array_component_reads`, decision 3/4) never looks at whether a
loop will actually be unrolled — it always stores `LoopIndexedName(base)`
for a non-constant index, unconditionally. Whether that resolves to
`"{base}#{i}"` or the bare `base` is decided later, by
`ArrayRead.to_core`/`FunctionCall.to_core` reading `ctx.unroll_index` — which
`SCFFor`/`SCFWhile.to_core` set independently, based on their own
`_contains_function_call` check (decision 10).

**Why:** this keeps three independent questions independent: "is this index
a source-level constant" (the pre-pass, unaffected by anything to do with
unrolling), "does this loop get unrolled" (the loop's own `to_core`,
unaffected by naming), and "what should this specific name render as right
now" (a two-line resolve at each of the two consumers). None of the three
needs to know how the others reached their answer. It also means the
pre-pass's output is correct regardless of what the loop's `to_core` later
decides — `LoopIndexedName.resolve(None)` naturally reproduces decision 2's
original bare-name behavior if a loop somehow isn't unrolled, with no
special-casing required anywhere.

## 14. Scope explicitly checked and left unhandled: split read/call pairs, nested unrolling

> **Superseded by decision 19**: moot — there is no unrolling left for a
> split read/call pair or a nested unrolled loop to go wrong in.

**Decision:** `ctx.unroll_index` is a single flat value (not a per-loop
stack, not keyed by which loop produced it). A component-array read and the
`function.call` consuming it are assumed to live in the same loop; nested
unrolled loops aren't given composite indices.

**Why:** the user asked explicitly to check for the split-read/call case
against the real examples and leave a `# TODO` if found — it wasn't:
`ternary_concrete.mlir`'s read and call are co-located in the same
`scf.while`, and `three_subcomponents_array_concrete.mlir` has no loop
containing a call at all. Building generality for a shape that doesn't
occur anywhere yet — either a split read/call pair or a nested unrolled
loop — would be speculative; both are called out in `PROGRESS.md`'s "known
issues" instead, to revisit if a future example actually needs it.

## 15. Generalized `ctx.var2const` constant folding through arithmetic and
    booleans, instead of a dedicated "tied loop" mechanism

**Decision:** to resolve a nested loop's bound that's only knowable once an
enclosing loop is unrolled (`babypbk_test_concrete.mlir`'s `%17`/`%20`
chain, `PROGRESS.md` §28), extend the *existing* `ctx.var2const`
constant-tracking substrate (`FeltBinary`/`FeltUnary`/`BoolCmp`/
`BoolBinary`/`BoolNot` now fold when their operands are known) rather than
building a parallel "is this variable free once the outer loop is
concrete" analysis pass.

**Why:** `SCFWhile`'s free-variable resolution
(`infer_n_repetitions_from_expressions`, `core_utils.py`) already checks
`ctx.var2const` for an unresolved name; `SCFFor`'s bound check already does
too. The only reason a tied nested loop's bound didn't resolve was that
arithmetic/boolean ops never *populated* `ctx.var2const` in the first
place — not that the consuming logic lacked a way to look there. Once an
enclosing loop unrolls (already-existing mechanism, unchanged) and sets the
induction variable's concrete value into `ctx.var2const` per iteration,
folding arithmetic/booleans transitively makes any downstream chain rooted
at that value resolve automatically, through ordinary re-execution of
`to_core` per iteration — no separate "will this become resolvable"
pre-pass is needed, and `core_utils.py`'s free-variable machinery needed
zero changes.

## 16. Boolean results represented as `1`/`0` in `ctx.var2const`

**Decision:** `BoolCmp`/`BoolBinary`/`BoolNot`'s new constant-folding writes
`1` or `0` into `ctx.var2const`, never `True`/`False`.

**Why:** matches the codebase's own pre-existing convention
(`arith.constant true`/`false` mapping to `1`/`0`, `PROGRESS.md` §14) and
means `SCFIf.to_core`'s `cond_const` check (`then_vals[key] if cond_const
else else_vals[key]`) composes with it directly — `ctx.var2const` is typed
`Dict[str, int]` throughout, and introducing a `bool` value into it would
be a second, inconsistent representation for the same concept.

## 17. `SCFIf` folds a result only when its *own* condition is decidable,
    never "whichever branch ran last"

**Decision:** `SCFIf.to_core` captures each branch's own folded value for
every declared result, then keeps the *taken* branch's value only if
`ctx.var2const.get(self.condition.name)` is itself known; otherwise it
explicitly pops the key rather than leaving whatever the last-translated
branch (always the else branch, or the then branch if there's no else)
happened to compute.

**Why:** found and fixed a genuine latent bug, not a hypothetical one:
`scoped_branch_registrations`' snapshot/restore-except-declared-results
mechanism means a declared result's `ctx.var2const` entry naturally ends up
holding whichever branch was translated *last*, regardless of the
condition's actual value — confirmed directly (condition forced `true`,
i.e. the then-branch is the real one, still returned the else-branch's
value). This was harmless only because nothing previously consumed an
`scf.if` result as a constant; decision 15's arithmetic-folding extension
would otherwise have made it *silently, actively* wrong the moment a nested
loop bound depended on it, rather than merely untested. Emitted Core text is
unchanged — this is purely a compile-time side-channel correction.

## 18. Lazy memoization for `SCFWhile`'s structural step-count analysis,
    with a fresh copy per call

> **Superseded by decision 19**: with unrolling removed, `_extract_step`
> runs at most once per `SCFWhile` instance regardless, so the memoization
> this decision justified has no remaining purpose — folded back into a
> plain, uncached `_extract_step`. Kept here as historical record of why
> the fresh-copy-per-call requirement mattered while unrolling still
> existed (the underlying mutation hazard it describes is real and would
> resurface if per-instance multiple calls were ever reintroduced for a
> different reason).

**Decision:** `SCFWhile._extract_step`'s construction of `var2expression`/
`condition_var` (the backward walk over `before_body`/`after_body`) is
split into a `_structural_analysis()` computed **lazily** (on first real
call, not in `__init__`) and cached; each `_extract_step` call takes a
fresh shallow `dict(...)` copy of the cached template before handing it to
`infer_n_repetitions_from_expressions`.

**Why laziness matters, not just caching:** at `__init__` time (during
parsing), an *enclosing* `scf.while`/`scf.for`'s own
`before_rename`/`after_rename`/`block_arg_rename` hasn't run yet —
`SCFWhile.parse`/`SCFFor.parse` call `update_variables` on an
already-constructed child object from the outside, mutating its
`before_body`/`after_body` SSAVar names in place, only after that child's
own `__init__` has already returned. Eagerly caching in `__init__` would
freeze `var2expression` against pre-rename names, permanently mismatched
with the post-rename names `ctx.var2const` is actually populated under once
translation starts — silently defeating free-variable resolution for any
nested `scf.while`. (`_contains_function_call`'s cache, by contrast, *is*
safe to compute eagerly in `__init__` — it's a pure `isinstance` walk,
blind to SSA names, so renaming can never change its answer.)

**Why the per-call copy matters, not just the cache itself:**
`_infer_from_comparison` (`core_utils.py`) mutates its `var2expression`
argument in place, folding a newly-resolved free variable in as a constant
leaf. Reusing the *same* cached dict object across calls (e.g. across
outer-loop iterations during unrolling) would let one iteration's resolved
value leak into the next as a stale, already-"resolved" entry that's never
re-checked against that call's own `ctx.var2const`. Confirmed by direct
repro before shipping: reusing one dict object across two calls with
different bound values (`4` then `7`) returned `4` for *both*; a fresh
`dict(...)` copy per call correctly returned `4` then `7`. This mirrors the
same "copy the accumulated map down, never mutate-through" discipline
`struct.py`'s naming pre-passes already use (decision 4) — applied here to
avoid re-running an expensive backward-walk while still keeping each call's
resolution independent.

## 19. Loop unrolling removed entirely; only its `LoopIndexedName`
    representation was simplified, not the naming pre-passes themselves

**Decision:** `scf.for`/`scf.while` no longer unroll under any
circumstance — they always translate their body as one generic iteration,
wrapped in a Core `repeat` block (a concrete count, or a `SymbolicSteps`
expression). `_contains_function_call`, `ctx.unroll_index`, and
`LoopIndexedName` are deleted outright (decisions 10-14, 18 above,
superseded). But the naming *pre-passes* that used to feed
`LoopIndexedName` — `_fold_index_constants`, `_find_array_component_bases`,
`_annotate_array_component_reads`, `_annotate_input_array_reads`,
`_annotate_function_calls`, and the `while_iter_args`/`trace_source`
block-arg aliasing — are kept, unchanged in structure; only their "index
isn't a compile-time constant" branch changed, from constructing a
`LoopIndexedName(base)` wrapper to using the bare string `base` directly.

**Why:** per an explicit product decision, subcomponent/signal naming for
anything a loop touches is now resolved afterwards by `llzk_cli`, not by
this translator — confirmed already under way via the `-ru` flag removal
(commit `5a3e46a`). This could have been read two ways: (a) narrowly, just
remove the per-iteration disambiguation unrolling existed to provide, or
(b) broadly, strip *all* semantic naming (including the `mux.c`/`mux.out`-
style scalar aliasing that predates unrolling by many sessions) since
naming is "llzk_cli's job now." (a) was confirmed correct, not (b): a
`LoopIndexedName(base).resolve(None)` call already, today, degrades to the
bare `base` string — and `ctx.unroll_index` will now *always* be `None`,
since nothing sets it once neither loop ever unrolls. Replacing the wrapper
with the literal string it already always resolved to is therefore a pure
code simplification with **zero output change**, not a naming-behavior
change requiring new test coverage for "what does naming look like now" —
confirmed by the full pytest suite and a `circomlib_examples/*.mlir` sweep
showing zero regressions (`PROGRESS.md` §29). Determining whether a
source-level array index is a compile-time constant (what the kept
pre-passes actually do) is a question about the *original circuit*, not
about whether this translator chooses to unroll a loop — the two concerns
were always separable, and decision 10 already established that the
"is this compile-time-constant" question (decisions 1-9) is independent of
the "does this loop get unrolled" question (decision 10 itself). Removing
the latter doesn't require touching the former.

**What was explicitly NOT touched, and why**: the constant-folding work
that immediately preceded this removal (`FeltBinary`/`FeltUnary`/
`BoolCmp`/`BoolBinary`/`BoolNot` folding into `ctx.var2const`, and the
`SCFIf.to_core` branch-value fix, `PROGRESS.md` §28) stays as-is. The
`SCFIf` fix corrects an independent, pre-existing correctness bug
(confirmed via direct repro, unrelated to whether any loop ever unrolls);
the constant folding is a generically useful propagation improvement,
confirmed (via the same sweep) to have already fixed a genuine, previously
silent bug in `escalarmulany_test_concrete.mlir` — neither is "unrolling
complexity" in the sense this decision's removal targets.

## 20. `signal_renaming.py`: capture quoted payloads without their
    delimiters, skip rather than assert on a mismatched prefix

**Decision:** `_CALL_ANNOTATION_RE`'s `:in-vars-info`/`:out-vars-info`
groups capture a payload's content *without* its surrounding quotes; the
decode step is exactly `json.loads(codecs.decode(raw, "unicode_escape"))`,
with no `.strip('"')`. In `process_components`, a `core_var` that doesn't
start with `"{component_name}."` is skipped, not asserted against.

**Why (decode step):** the stub's own hint comment quotes
`.strip('"')` after the `codecs.decode` call, implying the raw capture
was expected to include the surrounding quote characters (so that, after
`unicode_escape` leaves bare quote characters as literal chars rather than
unescaping them away, `.strip('"')` peels off the two now-plain leading/
trailing quotes). Capturing without the quotes in the first place — i.e.
letting the regex's own literal `"` delimiters bound the group rather than
including them inside it — means there are no leading/trailing quote
characters left to strip, and `codecs.decode` alone produces valid JSON
text. Verified directly against the real payload text extracted from
`ternary_two_calls_concrete.json` before writing any code, not just
inferred from the hint.

**Why (skip vs. assert):** `extract_component` derives `component_name`
from whichever of a call's dotted inputs/outputs happens to come first;
nothing guarantees every other `core_var` in the same call's
`in_vars_info`/`out_vars_info` shares that exact prefix (e.g. a call
mixing a `component.signal`-shaped argument with an unrelated plain-name
one). An `assert` would turn a shape this code doesn't yet have a
grounded example for into a hard crash the first time it's encountered
under real `llzk_cli` output; skipping just that one `core_var` (no
renamed entry for it, same as the "no dot at all" case `extract_component`
already handles) degrades gracefully to "don't rename what we can't
confidently attribute" without blocking every other call in the same
formula.

## 21. Pod-copy dispatch in `translate_assignment_core_with_ctx`: driven by
    `type_`, not by whether the value is already a registered `ctx.ssa2pod_var` key

**Decision:** the "Assign pod vars" branch of `translate_assignment_core_with_ctx`
(`core_utils.py`) now enters — and, when needed, lazily registers `rhs` via
`_register_pod_top_level`/`_parse_pod_fields` before proceeding — whenever
`type_` is itself a plain pod type (`type_.name.strip().startswith("!pod.type")`),
not only when `rhs.name` happens to already be a `ctx.ssa2pod_var` key.

**Why:** found via `poseidon3_test_concrete.mlir` producing a `.core` file
`llzk_cli` rejected with `seArrayCopy: ... Variable '...#1_@idx_0' not
found` — a pod-in-pod value (`@ark`'s `@idx_N` fields, each
`!pod.type<[@count, @comp: !struct.type<...>, @params: !pod.type<[]>]>`)
that this branch's own recursive `dest` derivation had minted one level up,
via a **different** invocation of this same branch, but never itself
registered as a `ctx.ssa2pod_var` key before being copied again one level
further up a deep `scf.if`/`else` cascade. The old guard
(`elif rhs.name in ctx.ssa2pod_var:`) is registration-driven: it only
recurses into a pod's fields if the source value has *already* been seen
and registered by some earlier step. That is true for a pod born directly
from `pod.new` or a struct member (registered eagerly, up front), but not
guaranteed for a pod value that is itself the *product* of one recursive
step of this very branch — registration there happens only as a
side-effect of the recursive call itself taking this same branch, which
requires its own rhs to already be registered, and so on down the chain.
One recursive call landing on an unregistered name at any depth silently
falls through every remaining branch to the generic scalar/`array.copy`
fallback at the bottom of the function — flattening one level short,
emitting a copy of a name nothing ever allocated as real storage, and
(confirmed directly) propagating the same one-level-short shortfall to
every enclosing level of the cascade, since each level's own `dest` is
never registered either.

The `!struct.type` branch immediately above this one in the same function
already gets this right, unconditionally: it recurses into a struct's own
output args purely from `type_` (via `ctx.llzk_func2core`/
`ctx.core_func2args`), never checking whether the struct value happens to
be pre-registered anywhere. This decision brings the pod branch in line
with that same principle — a value's *type* is what determines whether it
must be flattened, not whether some earlier step happened to already do
the bookkeeping for it. **This distinction is worth keeping in mind for
any future call site that dispatches on pod/struct/array shape**: prefer
deriving the recursion from `type_` (always correct, always available)
over gating it on prior registration (which can be incomplete depending on
how deeply nested control flow happens to construct a value) — the same
class of bug already surfaced twice before this fix, in unrelated files,
for unrelated reasons (`array_dimensions`/`array_felt_dimensions` not
anchored, §19 in `PROGRESS.md`; the struct-type check itself not anchored,
same section) — always for the same underlying reason: something that
should dispatch on the declared type instead trusted an incidental,
not-always-populated side channel.

**What was deliberately left alone:** the pre-existing lazy-registration
step for `lhs` a few lines below (added in §25, gated on
`ctx.input_pod_to_member.get(lhs.name)` — a member-backed semantic name)
stays as its own, narrower mechanism; it solves a different problem
(preserving a struct member's semantic destination name) and would be the
wrong place to also absorb rhs's registration, since rhs has no semantic
member identity to look up in the first place. The two lazy-registration
steps (rhs, type-driven; lhs, semantic-membership-driven) are independent
and compose without overlap — rhs's is fully general (works for a plain
SSA-derived pod name too), lhs's is not (it only fires for a known
semantic member), so they cannot be merged into one without losing lhs's
"do nothing when there's no semantic name to preserve" behavior. Nothing
in `pod.py`, `array.py`, or the "counting pod" bulk-copy mechanism in
`struct.py` needed to change — this is purely a dispatch-condition fix in
one function.

## 22. Two distinct failure classes for stale pod state: dispatch-driven
    (§21) vs. scope-lifetime (this decision) — do not conflate them

**Decision:** `pedersen_test_concrete.mlir`'s `KeyError: '@in'` crash
(`PROGRESS.md` §32) was fixed by clearing `ctx.ssa2pod_var`/`ctx.var2const`
at the start of `FunctionDef.to_core` (`function.py`) — a scope-lifetime
fix — **not** by extending §21's type-driven-dispatch fallback to
`PodRead.to_core`/`PodWrite.to_core`, even though both ops are still purely
registration-driven (`ctx.ssa2pod_var[pod_ref.name][record]`, no type
fallback at all) and it was reasonable going in to suspect the same fix
would apply.

**Why they're different, concretely:** §21's bug was "a pod value that
*should* recurse into its fields doesn't, because nothing checks `type_`
when the source isn't yet registered" — the fix (register from `type_` on
demand) is correct there because that branch is *defining* a fresh
destination for a value being assigned into; synthesizing its name from the
type it's declared as is exactly right. §32's bug was different in kind: a
pod value *was* registered, with an internally-consistent, correctly
type-derived shape — just the *wrong* one, because a stale leftover
registration from an entirely different, earlier-translated function
(reusing the same bare SSA number, since LLZK/MLIR numbering restarts per
function) was still live when this function's own code went looking for
it.

**Why extending §21's fallback to `PodRead`/`PodWrite` would be the wrong
fix for this bug, and is worth remembering for any future call site with
this shape:** `pod.read`/`pod.write` consume storage that must already
exist by the time they run — they never define a fresh name. Synthesizing
one from `type_` when `pod_ref` isn't registered would silently reference
storage nothing ever allocated, reintroducing §31's exact class of bug
(a `.core` reference to a name nothing backs) from the opposite direction,
and — worse than the original `KeyError` — would very likely do so
*silently*, without a crash, since a synthesized SSA-derived name looks
exactly as valid as a real one until something downstream reads from it.
A loud, immediate `KeyError` on stale/missing registration is strictly
preferable to a quiet, wrong one. The general rule this leaves standing:
**type-driven dispatch is the right fix for "how do I flatten/recurse a
value I'm defining"; it is not a substitute for "is the value I'm reading
from actually current" — that's a question about scope, and needs a scope
fix.**

**Why `FunctionDef.to_core`, not `PodRead`/`PodWrite`, not
`StructDef.to_core`:** confirmed via `FunctionDef`'s own `IsolatedFromAbove`
trait that a function body is LLZK's real scope boundary for SSA names —
independent of the empirical fix, this is where the clear *should* live.
It's also the single entry point shared by both a struct's `@compute` and a
bare pure function (`poly.template` wrapping a `function.def` directly,
`PROGRESS.md` §16) — anchoring in `StructDef.to_core` instead (alongside
the pre-existing `ssa_to_name`/`input_pod_to_member` clears) would have
left pure functions exposed to the identical class of collision.
`ctx.var2const` was cleared at the same site for the same reason, even
though no crash from it was observed yet — it has the identical flat,
never-cleared shape and is exposed to the same collision for constant
folding (a stale cross-function entry silently producing a wrong folded
loop-repetition count, say), so leaving it unfixed here would just be
deferring the same bug to whenever a file happens to exercise it.

## 23. `#`-separated idx-pod naming resolved entirely at translation time,
    not via `signal_renaming.py`

**Decision:** a heterogeneous array-of-components collection (LLZK's
`!pod.type<[@idx_0: !struct.type<@Ark_0::...>, @idx_1: !struct.type<@Ark_2::...>, ...]>`
lowering of a Circom collection whose elements instantiate *different*
templates per index — `PROGRESS.md` §33) is named `"{member}#{idx}"`
directly in the emitted `.core` file, at translation time — not deferred
to `signal_renaming.py`'s existing `"{component}#{i}"` post-processing
mechanism (`PROGRESS.md` §30, this file's §19/§20).

**Why:** `signal_renaming.py`'s `#i` mechanism exists specifically for a
genuinely runtime-only index — a symbolic loop variable only recoverable
from `llzk_cli`'s own SMT-level execution trace, because the translator
itself emits one generic loop body standing in for every iteration
(§19/decision 2). `@idx_N` is categorically different: it's always a
compile-time-literal pod field name — LLZK has no syntax for a
runtime-indexed pod read (`pod.read %p[@idx_%runtime_var]` doesn't exist)
— so the index is never actually ambiguous the way a loop index is. This
puts it in the same bucket as the pre-existing compile-time-constant array
index (decision 1's `"last_0"`), resolved once, correctly, at translation
time — just using `#` instead of `_` as the separator, per explicit
product decision, confirmed valid via `CORELLZK.md`'s own identifier
grammar (`id := [_,a-z,A-Z,%,@,.] [_,a-z,A-Z,0-9,%,@,#,.]*` — `#` legal
anywhere but the first character, so `ark#5.in` is a literal, real Core
identifier, not just a JSON-level label).

A post-hoc regex over `signal_renaming.py`'s `vars_info` (turning
`ark.idx_5_out` into `ark#5.out`) was considered first and rejected on
investigation: `.out` had no name at all to rewrite in the first place
(see §24 below — it fell back to a raw SSA name, not an `idx`-shaped
string), so a pure string-pattern pass couldn't have worked even before
weighing the second concern — a blind syntactic replacement risked
colliding with a signal genuinely named `idx_5` by the user's own circuit,
a risk the user explicitly flagged going in.

## 24. Match an idx-pod read by its own RESULT type's `@comp` field, not
    the source pod-type dict against the member's declared type

**Decision:** `_annotate_idx_pod_component_reads` (`struct.py`) identifies
which struct.member a `pod.read %pod_ref[@idx_N]` belongs to by parsing
the read's own declared **result** type and checking whether it's a
"counting pod" (`@count`/`@comp`/`@params`) wrapper whose `@comp` field
equals the struct type declared for `@idx_N` on the member itself
(`_idx_read_matches_member`) — not by comparing the read's *source* pod
type (`op.pod_type`, the whole `<[@idx_0: ..., @idx_1: ..., ...]>` dict)
against the member's full declared field dict.

**Why:** the first (rejected) design assumed a `pod.read[@idx_N]`'s
source type would always match the member's own final declared shape.
Tracing the real `poseidon3_test_concrete.mlir` `@ark` body disproved
this: the member's own declared type is only ever exposed *once*,
straight-line, in a `pod.new`/`struct.writem` pair right at the very end
of `compute`, packing 8 already-computed `@comp` values. Every read that
actually needs attributing to a call — inside the `scf.while` that
computes each slot, or inside the runtime-index `scf.if`/
`scf.execute_region` dispatch ladder LLZK compiles a *runtime-selected*
heterogeneous field access down to — instead reads a "counting pod"
collection, where each `@idx_N` field is itself a `@count`/`@comp`/
`@params` bookkeeping pod (the *same* idiom already used uniformly for
scalar and homogeneous-array subcomponent tracking, `PROGRESS.md` §9),
with `@comp` holding the per-index struct type. Matching the *source*
dict against the member's declared shape matches nothing at any of these
real call sites; matching the *result* type's `@comp` field matches all
of them, uniformly, regardless of which of the three population shapes
(straight-line extraction, `scf.while`, dispatch ladder) a given read sits
inside — confirmed directly against the real file after the first design
produced zero `_member_hint` annotations.

## 25. Idx-pod `#`-naming scoped to the semantic (member-backed) path
    only, never the raw SSA fallback

**Decision:** `_register_pod_top_level`'s idx-pod special case (`pod.py`)
only fires when the pod being registered is already member-backed
(`ctx.input_pod_to_member` has an entry for it) — `is_idx_pod = member is
not None and _is_idx_pod_fields(fields)`. A raw, unregistered pod (no
known member) with idx-shaped fields keeps the pre-existing
`"{var_name}_{record}"` naming completely unchanged, even though its
fields structurally match `_is_idx_pod_fields` too.

**Why:** the `#`-naming exists to produce one stable, meaningful name for
something the user's downstream tooling keys off — a raw SSA-derived
pod's own internal field naming is purely an implementation detail
nothing downstream ever reads semantically, so touching it would be
change for no benefit. Confirmed by an existing regression test,
`test_new_init_pod_field_with_nested_struct_field_uses_pod_branch`
(`tests/test_pod_parse.py`), which specifically exercises this exact
raw-fallback path (a pod-in-pod field with a `@comp: !struct.type<...>`
sub-field, unregistered) and must keep producing `"%outer_@idx_0"`-shaped
names — an earlier version of this fix applied the `#`-substitution
unconditionally and broke this test, which is what surfaced the
distinction.

## 26. `_allocate_pod_field_storage`'s own nested-pod registration guarded
    against re-registering an already-registered name

**Decision:** `_allocate_pod_field_storage` (`pod.py`) now only calls
`_register_nested_pod_vars` for a pod-typed field when `var_name not in
ctx.ssa2pod_var` — previously unconditional.

**Why:** found as a genuine latent bug while implementing §23/§24 above,
not a hypothetical one — a new unit test
(`test_new_member_pod_nonempty_nested_field_registers_recursively`)
failed with the wrong (underscore-joined) name even though
`_register_pod_top_level` had *already* correctly registered the
dot-joined, `#`-prefixed one. Tracing showed every call site
(`PodNew.to_core`, `register_and_allocate_pod`) always registers a
pod-typed field's own nested vars via `_register_pod_top_level` /
`_register_nested_pod_vars` *before* reaching this allocation step — so
this second, independent call was always redundant, silently
re-deriving the same name via the plain (non-idx-aware) `"_"`-joined
convention every time. This was harmless before §23/§24 (both
computations happened to agree), but the moment `_register_pod_top_level`
started choosing a `top_level_join=True` (dot-joined) name for an idx-pod
field, this unconditional second call silently clobbered the correct name
back to the wrong one immediately afterward — a straightforward
write-after-write ordering bug, invisible without a test asserting the
*final* registered name rather than just checking that *some* name got
registered.

## 27. `while_iter_args` collection made recursive; `result_to_init`
    deliberately left as top-level-only

**Decision:** `_build_component_naming_maps`'s two `scf.while`-derived
maps (`struct.py`, `PROGRESS.md` §34) are no longer built by one shared
top-level-only loop. `while_iter_args` — the `(block_arg_name,
init_val_name)` pairs used to alias a loop's own block-arg name to its
registered member base — is now collected by a new recursive
`_collect_while_iter_args`, reaching a `scf.while` nested inside another
at any depth. `result_to_init` — the separate map `trace_source` walks —
stays exactly as it was: built from a top-level-only scan.

**Why the split, not making both recursive:** `while_iter_args` needs an
entry at *every* nesting level, because a loop body only ever references
its *own* block-arg name — a doubly-nested `scf.while`'s body uses that
inner loop's block-arg (e.g. `%arg4`), one hop removed from the outer
loop's own (`%arg2`), and both names need to resolve to the same member.
`result_to_init` is different in kind: it's only ever *queried* from a
top-level `struct.writem`'s own value (`trace_source(op.value.name)`),
and a nested while's own result can only ever reach that top-level value
by first being yielded into its immediately-enclosing while's own
declared result — which is itself already top-level in every case
observed (LLZK/MLIR scoping: an inner op's result name is only visible
inside the block it's declared in, so it can't be referenced directly by
a top-level op without first being threaded out via the enclosing op's
own yield/results). There is no chain `trace_source` would ever need to
follow through a nested while's *result* name directly, so making it
recursive too would be speculative generality for a case that can't
occur, not a real gap — matching this file's own established discipline
(decision 9, decision 14) of not building for a shape not yet observed.

**Why ordering matters, and is preserved:** `_collect_while_iter_args`
visits an op's own iter-arg pairs *before* recursing into its sub-bodies,
so an outer while's alias is always appended to the list before any while
nested inside it. The existing single-pass alias-resolution loop (kept
completely unchanged) depends on exactly this ordering: each entry's
`init_val_name` is resolved via `ctx.input_pod_to_member.get(...)`,
which — for a nested loop's entry — only succeeds because the
*immediately enclosing* loop's own alias was already written into
`ctx.input_pod_to_member` by an earlier iteration of the very same loop.
This composes correctly to arbitrary nesting depth for free, with no
change to the resolution loop itself — confirmed by hand-tracing the real
two-level `@mixLast$inputs` chain end to end before writing the test.

## 28. Array-of-components naming generalized to N dimensions; `#` chosen
    as the single separator for every case, superseding decision 1

**Decision:** the whole array-of-components naming mechanism — both the
homogeneous real-array, compile-time-constant-index case (decision 1,
`struct.py`'s `_annotate_array_component_reads`/
`_annotate_input_array_reads`) and the heterogeneous idx-pod case
(decision 23, `pod.py`'s `_idx_pod_child_name`) — now builds a name with
one `"#idx"` segment per array/collection dimension (`"last#0"`,
`"last#0#1"`, `"ark#5"`, `"components#0#0"`), for any number of
dimensions. This retires decision 1's `"_"` separator for the
compile-time-constant case entirely — every "array/collection index
disambiguation" mechanism in this codebase now uses the same character.

**Why unify the separator, not just add N-D support alongside `"_"`:**
confirmed explicitly with the user rather than assumed. Before this
change there were three such mechanisms with two different separators:
decision 1's compile-time-constant homogeneous case (`"_"`),
`signal_renaming.py`'s genuinely-runtime-loop case (`"#i"`, decision-19-era
design), and decision 23's heterogeneous idx-pod case (`"#N"`). The
original `"_"`/`"#"` split (decision 11, since superseded) existed to let
downstream tooling distinguish "the source circuit already fixed this
instance" from "the translator disambiguated this after the fact" — a
distinction that only made sense while loop unrolling existed to produce
the second category. Decision 19 removed unrolling entirely, which
already left decision 11's distinction without a referent; this change
completes that cleanup by removing the last vestige of the two-separator
scheme, rather than leaving `"_"` permanently stranded as an
now-unmotivated special case that the N-D generalization would otherwise
have had to preserve and thread through every affected function
unchanged. Requires updating every existing test/doc asserting a
`"last_0"`-style name (`PROGRESS.md` §35) — treated as an acceptable,
one-time cost of fixing an inconsistency rather than freezing it in place.

**Why the bulk-copy detector (`_find_array_component_bases`) needed to
become a recursive nested-loop walk, not just a wider index check:** an
N-D array-of-components member's bulk copy is written as N *nested*
`scf.for` loops (one per dimension — confirmed by direct analogy to every
other N-D population shape already traced in this codebase, e.g. decision
24's two-nested-`scf.while` heterogeneous case), not one loop with N
indices. `_walk_for_bulk_copy_nest`'s recursion carries a growing stack of
enclosing induction variables and only accepts the bulk-copy triple (array
read / `pod.read[@comp]` / array write) once the read/write index count
exactly matches the current stack depth — which structurally can only
happen at the innermost loop for a genuine N-D nest, and immediately (no
recursion needed) for the pre-existing 1-D case. No real N-D homogeneous
fixture was available to verify end-to-end this session (unlike the
heterogeneous side, verified against `multidimensional_components_concrete.mlir`)
— confirmed instead via synthetic unit tests
(`TestFindArrayComponentBases`'s 2-D cases,
`TestBuildComponentNamingMapsArraysND`) built the same way this
codebase's existing 1-D tests already are (direct `SCFFor`/`ArrayRead`/
`ArrayWrite` object construction, not parsed `.mlir` text), plus
regression-confirming `poseidon3_test_concrete.mlir`'s real `@sigmaF`
(2-D) now resolves instead of falling back to a raw SSA name on both
sides.

**Why a partially-resolved index (some dimensions constant, some not)
falls back to the bare member name, not a partial suffix:** matches
decision 2's existing reasoning for the fully-unresolved case, generalized
rather than given new logic — a partial instance identifier (e.g. knowing
only the outer index of a 2-D read) still isn't a specific instance, so
there's nothing more precise to say at translation time than the bare
base name; inventing a partial suffix would imply more precision than the
translator actually has.

## 29. Array-of-components real traversal order computed as a self-contained
    `struct.py` static pre-pass, not at `to_core` time

**Decision:** the real sequence of concrete array-index tuples a
symbolically-populated array-of-components member's population loop(s)
actually visit (`PROGRESS.md` §36, consumed by `signal_renaming.py` in
place of a flat per-call counter) is computed entirely by a new,
self-contained `struct.py` pre-pass — a static analysis over the parsed
AST, run before any real `to_core` translation happens — rather than by
instrumenting `SCFFor.to_core`/`SCFWhile.to_core` themselves to record
their own sequence as a side effect of real translation.

**Why:** confirmed explicitly with the user rather than assumed, given
both were genuinely viable. The self-contained pre-pass reuses the
existing trip-count machinery (`core_utils.py`'s `count_iterations`/
`_infer_from_comparison`, `SCFWhile`'s own condition-analysis) by feeding
it *pre-pass-derived* inputs (a local, `_fold_index_constants`-based
constant fold) instead of the real `ctx.var2const` `to_core` populates —
exactly the same "own static fold, not `ctx.var2const`" principle already
established for the closely related "is this array index a compile-time
constant" question (decision 3) and for the same underlying reason: a
loop's OWN `to_core` only sets `ctx.var2const[iv]` to its *initial* value,
for legitimate structural trip-count purposes, and only for the duration
of translating that one generic loop body — trusting it here would be
imprecise in the exact same way decision 3 already ruled out. Touching
`SCFFor.to_core`/`SCFWhile.to_core` instead — the alternative considered —
would mean modifying the single most sensitive, heavily-relied-upon code
path in the whole translator (every example's own correctness depends on
these two methods emitting exactly the right `.core` text) for a feature
that has nothing to do with what gets emitted there at all; the
self-contained pre-pass touches zero lines of either method, only adding
one new sibling method to `SCFWhile` (`_extract_index_sequence`, decision
30) that `to_core` itself never calls.

## 30. Trip-count and traversal-sequence resolution share one extracted
    helper, in both `core_utils.py` and `scf.py`

**Decision:** rather than writing a second, independent implementation of
"resolve a while condition's loop-carried variable, its initial value, its
update function, and its continuation predicate" for the new
sequence-returning path, both `core_utils.py` and `scf.py` extract their
existing count-only logic into a shared helper first
(`_resolve_comparison_recurrence` in `core_utils.py`;
`_build_while_var_expressions` in `scf.py`), then add a new sibling
function/method (`_infer_sequence_from_comparison`/
`infer_iteration_sequence_from_expressions`; `SCFWhile._extract_index_sequence`)
that calls the *same* shared helper and only differs in what it does with
the result (`count_iterations` vs. the new `iterate_values`, itself just
`count_iterations`'s own loop shape with `value` appended each pass
instead of only counted).

**Why:** the two questions ("how many iterations" and "what values are
actually visited") must never be allowed to silently disagree — if they
were computed by two independently-maintained code paths, a future change
to one (e.g. a new condition shape, a new free-variable-resolution rule)
could easily update only one path and leave the other subtly wrong, with
no test failure pointing at the mismatch unless something happens to
exercise both on the exact same input. Sharing the resolution step by
construction makes that class of bug impossible: both callers are
mechanically guaranteed to agree on the recurrence itself, differing only
in the trivial, obviously-correct final step. `to_core` and `_extract_step`
themselves are byte-for-byte unchanged by this refactor (confirmed via the
full pre-existing test suite) — only the internals were reorganized.

## 31. Two structural signals distinguish a real population write from a
    look-alike: read-modify-write, and "last in scope wins"

**Decision:** `struct.py`'s new detection of a symbolic population site
(`PROGRESS.md` §36) requires two things beyond "a non-constant-indexed
`ArrayWrite` into a registered counting-pod array": (1) the write's own
value must trace back to an `ArrayRead` of that *same* array
(`_is_population_write` — a real read-modify-write, not e.g. the array's
own initial-fill loop writing a fresh `pod.new` into every slot); and (2)
when more than one such write structurally qualifies within the *same*
loop iteration's own scope (not crossing into a further-nested loop —
`_collect_population_write_candidates`), only the textually *last* one is
kept, discarding any earlier ones.

**Why both are necessary, not just one:** found empirically, in that
order, while validating against `arbitrary_traversal_array_components_concrete.mlir`.
Without (1), the array's own initialization loop (identical shape: a
non-constant-indexed write into the registered array) is indistinguishable
from a real population write, producing a spurious full-row-major sequence
covering every slot regardless of which ones a real `@compute` call
actually reaches. Without (2), a component with more than one input
signal produces a spurious *duplicate* of each nest's own sequence: LLZK
re-emits a complete "ready to call yet?" checkpoint (its own `@count`
decrement, comparison, and — guarded behind it — the real
`function.call` + array-write) once *per input signal assignment*, not
once per component instance, because the frontend can't statically know
which signal assignment will be the last one for an arbitrarily-ordered
Circom program. Every such checkpoint is structurally a complete, valid
"population write" in isolation; only the one immediately following the
*final* signal assignment ever has its guard actually satisfied at
runtime (`@count` starts at the input count and reaches exactly 0 once).
"Textually last within the same static scope" is therefore not a
heuristic tie-break but a direct consequence of how LLZK lowers this
pattern — sound for any number of input signals, not just the 2 the
motivating example happens to have. Both signals were needed together:
neither alone would have caught what the other did, and the combination
was found by writing a fixture that happened to exercise a component with
two inputs, not by design foresight.

## 32. Index-to-loop mapping resolved by SSA identity, never by position
    or nesting depth

**Decision:** `_trace_to_enclosing_loop` (`struct.py`) resolves each of a
population write's own indices to the specific enclosing loop that
produced it by following `cast.toindex`/`cast.tofelt` chains back to a
loop's own induction variable (`scf.for`) or after-region block-arg
(`scf.while`) **name** — never by the index's position in the write's own
index list, and never by assuming it corresponds to `loop_stack` in
outer-to-inner nesting order.

**Why:** confirmed necessary, not merely defensive, by reading the real
`arbitrary_traversal_array_components_concrete.mlir` body directly before
writing any code. Its Circom source writes `components[i][j]` (array
dimension 0 = `i`, dimension 1 = `j`), but the *first* of its two
population loop nests has `i` driven by the *inner* loop and `j` by the
*outer* one — the reverse of what a positional or "outer loop = dimension
0" assumption would produce. The *second* nest (a separate, textually
later loop over the odd indices) nests the *other* way (`i` outer, `j`
inner) — confirmed resolved correctly with zero special-casing, purely
because the mapping asks "which loop produced *this specific* SSA value"
rather than "which loop is in *this* position." A positional shortcut
would have silently transposed one or both nests' own sequences with no
error or warning, since both encodings produce a structurally
well-formed, plausible-looking sequence — only comparing against the
user's own hand-derived expected traversal order would have caught it,
which is exactly how this was found during initial design, before any
code was written to encode the (wrong) positional assumption in the first
place.

## 33. Pure-function output ordering: hoist-and-topo-sort, not stable
    in-place reordering

**Decision:** when a pure function (`poly.template` wrapping a bare
`function.def`) is forward-referenced — called before its own `def` is
reached in the source file, possibly through a multi-level chain (e.g.
`sha256_2_test_concrete.mlir`'s `ssigma1_1` calls `rrot_8`, declared
later) — fix the emitted `.core` order by hoisting *every* pure-function
`def` to the front of the output, topologically sorted among themselves by
their own call graph, ahead of every other top-level item (structs etc.).
Those other items keep their existing relative order unchanged.

**Why:** the alternative — a stable topological sort over the *entire*
top-level body (Kahn's algorithm with original-index tie-breaking), moving
an item only when a real forward reference forces it — produces output
ordering closer to the source file, which only matters for a human reading
generated `.core` text. It requires materially more code (a priority-queue-
or repeated-scan-based stable sort over a mixed node set, versus a plain
DFS over a same-kind node set) for no correctness benefit: nothing in this
codebase depends on a pure function's textual position *relative to a
struct*, only on it existing (as text) before any call to it, wherever
that call sits. Confirmed with the user, who chose the simpler hoist
approach for exactly this reason.

**Consequence:** the topological sort itself only needs to reason about
pure-function-to-pure-function dependencies (via `_collect_function_calls`,
recursing into nested `scf.if`/`scf.for`/`scf.while` bodies) — struct-to-
struct and struct-to-pure-function calls are unaffected by, and don't
participate in, this sort; the pre-existing assumption that struct-to-
struct calls are already correctly ordered in the source file (§16's
`ModuleOp.to_core` comment) still holds and is untouched.

## 34. Redirected from `bool.ne`/`bool.eq` while-condition support to pure-function loop-bound specialization

**Decision:** dropped the originally-requested `bool.ne`/`bool.eq`
while-condition support entirely (leaving `core_utils.py:485`'s `assert
op in ("lt", "le")` unchanged) and implemented a structurally different
fix instead: specializing a pure function's body per distinct
compile-time-constant value its own loop-bound-relevant parameter takes
across all call sites (PROGRESS.md §38).

**Why:** the motivating example (`pointbits_loopback_concrete.mlir`'s
`sqrt_0`, using `bool.cmp ne`) doesn't survive investigation as a real
target — tracing its parameter `n` through all 4 of its call sites (also
in `eddsa_test_concrete.mlir`) shows it's always a genuine runtime witness
signal, never a compile-time constant, so no amount of predicate support
could make its loop bound statically resolvable; Core's own `repeat`
construct can't even express a genuinely data-dependent trip count
regardless (only a plain identifier or integer literal, per
`CORELLZK.md`'s grammar — no true per-iteration condition check). The
user redirected to `EscalarMulW4Table_0`, a structurally similar but
genuinely fixable case: its own loop bound also depends on a parameter,
but that parameter *is* a compile-time constant at every real call site
(confirmed across all 7 affected files) — and is furthermore a
**documented, real, currently-broken case** (`llzk_cli` already rejects
these 7 files' existing `SymbolicSteps`-driven output with `Variable
'%steps_N' is a symbolic`), unlike the `ne`/`eq` gap, which was never
confirmed to unblock any file end-to-end even if implemented.

**Consequence:** `bool.ne`/`bool.eq` while-condition support remains a
known, deliberately unaddressed gap (see PROGRESS.md's "Known
pre-existing" list) — worth revisiting only if a future example is found
where the predicate genuinely would resolve to a concrete or symbolic
trip count (unlike `sqrt_0`'s).

## 35. Specialization pre-pass runs after `_topo_sort_pure_functions`, and never modifies the existing concrete-bound resolution logic

**Decision:** the new specialization pre-pass (§38) runs strictly after
the existing `_topo_sort_pure_functions` call, and resolves call-site
arguments to constants by feeding them into the **existing, unmodified**
`core_utils.construct_function_from_expressions` evaluator — the same one
while-bound resolution already uses (`bound_func(0)`) — rather than adding
any new logic to `_resolve_comparison_recurrence`/`count_iterations`/
`SymbolicSteps`.

**Why:** topological order must reflect the *original* call graph — a
pure function's dependency on another pure function doesn't change
because the callee later gets cloned, so computing it before
specialization mutates any `FunctionCall.callee` keeps that ordering
logic simple and correct without needing to teach it about clones at all.
Reusing `construct_function_from_expressions` (rather than writing a
parallel "is this constant" evaluator) means the two truths — "what value
does this expression fold to" for a while's own bound, and for a
function's call-site argument — can never silently drift apart, the same
reasoning as decision 30's shared `_resolve_comparison_recurrence`. It
also means the fix carries zero risk to the well-tested `lt`/`le`
concrete-bound path: once a clone's parameter is folded into
`ctx.var2const` (via the new `pending_const_seed`), that existing code
just sees an ordinary already-known free variable, exactly as it already
handles one resolved via a `global.def` or an outer `felt.const` chain.

## 36. Specialization is all-or-nothing per function; unnamed clone only when every call site agrees

**Decision:** if even one call site's relevant argument fails to resolve
to a concrete int, the *entire* function is left unspecialized —
untouched, byte-for-byte identical to today's output — rather than
specializing the resolvable call sites and leaving the rest pointed at a
generic fallback. Clone naming keeps the function's original Core name
when only one distinct constant value is seen module-wide (e.g.
`escalarmulw4table_concrete.mlir`'s single `k=0`), and suffixes
`{name}__{arg_display_name}{value}` only when multiple distinct values
are seen (e.g. `EscalarMulW4Table_0__k0` .. `__k63` in
`escalarmul_test_concrete.mlir`), using `FunctionDef.in_arg_names` for a
human-readable parameter name.

**Why:** a partial specialization (some call sites redirected to a
concrete clone, others still hitting the generic, still-symbolic body)
would be strictly more complex to implement and reason about for no known
benefit — no real example has a mix of resolvable and unresolvable call
sites for the same loop-bound-parametric function; `sqrt_0`'s call sites
are uniformly unresolvable, `EscalarMulW4Table_0`'s uniformly resolvable.
The original-name-when-unique convention minimizes the diff on the
already-more-common single-variant files (4 of the 7 fixed files) while
still giving multi-variant files (the 64-window `escalarmul_test_concrete.mlir`
family) unambiguous, debuggable per-clone names instead of an opaque
positional index.

## 37. `SCFWhile.to_core` binds its own external result(s) to their initial values unconditionally, not only when steps resolves to 0

**Decision:** `scf.py`'s `SCFWhile.to_core` now emits an initial binding
of its own external result name(s) (e.g. `%22`/`%22#0`) to the loop's
initial values right after the existing per-arg initial-value assignment,
*before* the `repeat` block — for every while loop, regardless of its
resolved step count, not only when it's statically known to be 0.

**Why:** this bug (an always-undefined result variable when `repeat 0`
constant-folds and no earlier real example ever hit a genuine 0-count
loop) was surfaced entirely by §38's own end-to-end verification, not
sought out separately — a specialized `EscalarMulW4Table_0` clone with
`k=0` is the first real trip count of exactly 0 this codebase has ever
produced. Binding unconditionally, rather than gating it on `steps == 0`,
avoids adding a second, easy-to-forget code path with its own edge cases
(e.g. a `SymbolicSteps` bound that only turns out to be 0 at proof-generation
time) — Core already allows plain reassignment (confirmed by the loop
body's own existing per-iteration rebinding of its block args), so the
extra binding is harmlessly overwritten by the real per-iteration one
whenever the loop actually runs at least once. Verified via a direct
before/after `.core` diff on two unrelated files with real (nonzero,
unspecialized) while loops (`mux4_1_concrete.mlir`,
`poseidon3_test_concrete.mlir`): the only diff is these new lines, nothing
removed, reordered, or functionally changed, and both still pass a full
`llzk_cli` run.

## 38. Fixed `_parse_in_arg`'s per-argument `loc(...)` blind spot rather than deferring it

**Decision:** fixed `function.py`'s `_parse_in_arg` (used by
`FunctionDef.in_arg_names`, which §38's specialization clone-naming
depends on) to strip a per-argument trailing `loc(...)` suffix (reusing
`loc_parser.strip_trailing_loc`) before checking for a trailing `{attrs}`
dict, rather than falling back to raw SSA names for clone suffixes and
leaving the bug for later.

**Why:** without this, `in_arg_names` silently returns `{}` for
essentially every real multi-argument example (each argument individually
carries its own ` loc(...)` in real `--llzk_plaintext` output, which
`LLZKParser`'s own line-level loc-stripping only ever strips once, at the
very end of the whole `function.def` line) — a real, previously-latent
bug (the field's own docstring already said "not yet consumed by any
translation logic," meaning it had never actually been exercised against
real multi-arg output before this session). Fixing it in place was low-risk
(a single, well-scoped regex/string-handling change, mirroring
`scf.py`'s own already-working `_parse_block_args` use of the identical
utility) and directly improves this fix's own deliverable — clone names
like `EscalarMulW4Table_0__k1` instead of the far less readable
`EscalarMulW4Table_0__arg11` the raw-SSA-name fallback would otherwise
have produced.

## 39. Field-aware simulation is centralized in `construct_function_from_expressions`, not scattered per-comparison

**Decision:** rather than special-casing modular reduction inside
`_resolve_comparison_recurrence`'s new eq/ne `compare_func`, the `prime`
parameter is threaded into `construct_function_from_expressions` itself
(used to build both `update_func` and `bound_func`), which reduces the
result of every composed operation modulo it.

**Why:** the actual bug (`smtprocessor10_test_concrete.mlir`'s
`i != -1`-as-`i != prime-1`) isn't a defect in the *comparison* — `x !=
bound_value` is already correct once `x` itself is correct. The defect is
in the *simulated recurrence*: `felt.sub`'s naive Python arithmetic never
wraps, so `x` drifts off as an ever-more-negative int instead of
correctly becoming `prime - 1`. Fixing it at the recurrence's own
construction point means every predicate (not just `eq`/`ne`) and every
consumer of `construct_function_from_expressions` (bound evaluation too,
not just the update function) benefits uniformly, with no risk of one
call site being fixed and a sibling being missed. It also means the eq/ne
`compare_func` itself stays exactly as simple as `lt`/`le`'s always were
— `lambda x: x != bound_value` — with no special-casing at all.

## 40. Only genuine field arithmetic is reduced modulo the prime — bitwise/integer ops are deliberately excluded

**Decision:** `felt.py`'s prime-aware reduction applies only to
`felt.add`/`sub`/`mul`/`div`/`pow`/`neg`/`inv` (`FeltBinary`/
`FeltUnary`'s new `_FIELD_ARITHMETIC_OPS` sets). `felt.shl`/`shr`/
`bit_and`/`bit_or`/`bit_xor`/`bit_not`/`uintdiv`/`sintdiv`/`umod`/`smod`
are left completely untouched, even though they're defined on the same
felt-typed values.

**Why:** these aren't field arithmetic at all — they're integer/bitwise
operations on a felt-typed value's underlying bit pattern (e.g.
`Num2Bits`' `felt.shr %arg0, %arg1` / `felt.bit_and %1, 1` bit-extraction
loop, or a hash-function rotation like `rrot_8`'s `felt.shl`/`felt.bit_or`).
`llzk`'s own `function.allow_non_native_field_ops` attribute on functions
using them signals exactly this distinction. Reducing them modulo the
field's prime would silently corrupt results that were never meant to
wrap at the prime at all (e.g. a 32-bit rotation wrapping at a ~64-bit
goldilocks-adjacent prime instead of at 2^32) — a subtler, worse bug than
the one this fix set out to close. `felt.div` is included as genuine field
division despite `felt.uintdiv`/`felt.sintdiv` existing as separately-named
integer-division variants — that naming split is itself the signal that
bare `felt.div` is the native field operation.

## 41. `felt.div`'s floor-division *algorithm* is left unchanged; only its result is now reduced modulo the prime

**Decision:** `felt.div` still computes `x // y` (floor division), not a
"real" field division (`x * modinv(y)`) — despite `felt.inv` itself being
fixed to a genuine modular inverse in the same change. Only the *result*
of `felt.div`'s existing floor-division is now wrapped with `% prime`,
matching every other field-arithmetic op.

**Why:** whether `felt.div` already means genuine field division or a
distinct floor-division-on-felt-typed-values operation in this codebase's
own IR wasn't confirmed against a real example that exercises it as a
while-loop-bound-relevant computation — unlike `felt.inv`, whose `1 // x`
was unambiguously never anything but a wrong placeholder (a modular
inverse needs the modulus, which nothing before this fix ever supplied,
so there's no prior "intended" semantics to preserve or risk breaking).
Changing `felt.div`'s core algorithm risks silently altering some
currently-passing file's already-correct constant-fold in a way this
session's verification sweep wouldn't necessarily catch (every existing
example's folded values stay non-negative and small, so `x // y` and
`x * modinv(y)` only provably diverge on inputs no current example is
known to hit — but "known to hit" isn't "proven not to"). Reducing the
result modulo the prime is unconditionally safe (a no-op for the
non-negative, sub-prime values every current example already produces)
and closes the same wraparound gap as every other op, without touching
an algorithm whose correctness for this codebase's actual usage wasn't
independently verified. Revisit if a real example is ever found where
`felt.div`'s result needs to be a genuine field element (implying true
modular-inverse semantics) rather than an integer quotient.

## 42. Defensive iteration cap added to `count_iterations`/`iterate_values`

**Decision:** added `_MAX_SIMULATED_ITERATIONS = 1_000_000` to
`core_utils.py`, raising `RuntimeError` from both trip-count simulation
loops if exceeded, rather than only fixing the specific wraparound shape
that motivated this session's investigation.

**Why:** the `smtprocessor10`/`smtverifier10` investigation surfaced a
translator that can hang indefinitely on a non-terminating recurrence,
with no prior safeguard. Field-aware simulation (decision 39) fixes the
*known* cause, but a future predicate, op, or field-arithmetic shape this
codebase doesn't model correctly yet could reintroduce the same failure
mode. A generous, fixed cap (far above any real circuit loop) costs
nothing for every real example while turning any future non-terminating
case into a fast, diagnosable failure instead of a silent hang — cheap
insurance, not scope creep, since the alternative (no cap) is strictly
worse for a codebase whose whole job is simulating trip counts for
inputs it doesn't fully control the shape of.

## 43. Fixed the raw-dict-lookup rename bug in all four `update_variables` overrides, not just `SCFWhile`

**Decision:** the reported `babypbk_test_concrete.mlir` crash only
exercised `SCFWhile.update_variables`, but `SCFIf`, `SCFExecuteRegion`,
and `SCFFor` were fixed in the same change, having been confirmed (by
direct code reading, not inference) to share the identical raw
`if name in rename: name = rename[name]` pattern instead of routing
through `core._apply_rename`.

**Why:** this is a single mechanical pattern duplicated across four
sibling classes in the same file, all populated from the same kind of
rename dict (`_collect_result_names`, always bare base names) built by
the same surrounding logic (`SCFWhile.parse`'s `before_rename`/
`after_rename`, `SCFFor.parse`'s `body_rename`). There is no plausible
reason one class's copy of the pattern would need the fix while another's
wouldn't — `outcome.csv`'s `pedersen2_test_concrete.mlir` failure
(`%80#1_@idx_0_@in`) was independently confirmed to be the exact same bug
via a different nesting path, evidence that the pattern bug isn't
purely theoretical for the other three classes either. Fixing only the
one class actually observed failing would leave known-identical latent
bugs in place for whichever real `.mlir` file happens to nest a
component/field-suffixed reference through `scf.if`/`scf.execute_region`/
`scf.for` instead of `scf.while` next.

**Also decided:** kept `_apply_rename` itself unchanged and reused as-is
(imported into `scf.py`) rather than introducing an alternative
"pre-expand the rename dict with suffixed keys" mechanism, per explicit
investigation requested by the user. Confirmed infeasible, not just
more complex: the `_@field` tags `_apply_rename` reattaches are only
constructed later, during `to_core` (`_container_field_var`, driven by a
`TranslationContext` that doesn't exist yet when the rename dicts are
built at `parse()` time), so there's nothing to pre-enumerate at
dict-construction time. Revisit only if a future change needs to rename
something *before* `to_core` ever runs and after all component/field
suffixes are already statically known — no such case exists today.

## 44. `_trace_to_enclosing_loop`'s index-arithmetic support is deliberately scoped to a single `felt.add` offset, not general expression simulation

**Decision:** when extending `_trace_to_enclosing_loop`/`_resolve_population_nest_sequence` (`struct.py`) to handle `sigmaF`'s `nRoundsF/2 + r`-shaped population index, the fix only recognizes a `felt.add` between a loop's own raw counter and the final array index (accumulating through multiple chained adds, either operand order) — not multiplication, subtraction, or any other transform, and not a general expression evaluator.

**Why:** no real file investigated this session needs anything beyond a single additive constant offset — `poseidon.circom`'s own four `sigmaF` population sites are the only real-world motivating case, and all four are either a bare loop identity or exactly this one `+const` shape. Per explicit user direction, a genuinely general version (identify the index variable(s), then *simulate* their update expressions across iterations to emit the real sequence directly) is real future work, not this fix's job — and should reuse this codebase's *existing* general-purpose trip-count/expression simulator (`core_utils.py`'s `construct_function_from_expressions`/`infer_iteration_sequence_from_expressions`, already relied on for `repeat` bound resolution elsewhere) rather than inventing a second, parallel simulation mechanism specific to array indices. Revisit only when a real file's population index needs more than one constant additive hop.

## 45. `array_member_base`'s `scf.while` aliasing is resolved as a bidirectional fixpoint, not a single forward pass

**Decision:** `_collect_while_region_array_aliases`/`_build_component_naming_maps`'s resolution of a counting array's `scf.while` block-arg aliases (`struct.py`, §42) repeatedly propagates a known member to its paired name in *either* direction until nothing changes, rather than a single forward pass over encounter order (the shape `_collect_while_iter_args`' identical, already-working `$inputs`-pod resolution gets away with).

**Why:** a first attempt ported that exact single-pass, outer-to-inner shape and it silently under-fixed a real file (`poseidon3_new.mlir`): `sigmaF`'s real population isn't purely a nesting chain (parent `scf.while` registers first, child resolves through it) — it's four *sequential sibling* `scf.while`s, each threading the counting array through as the *next* site's own init value, with only the *last* site's own result directly registered by the post-loop bulk-copy. A single forward pass can never resolve the earlier sibling sites this way, regardless of collection order, because the one registered identity is discovered *last* in the chain, not first — whichever direction a given pair resolves in depends on where that particular `scf.while` sits relative to the others, which isn't knowable in advance the way it structurally is for `$inputs` pods (always purely nested, per that mechanism's own confirmed real-world shape). A fixpoint is the correct, general answer to "propagate a known identity through an equivalence graph regardless of which direction each edge happens to resolve in," and is cheap here (bounded by the number of distinct names, each fixpoint iteration adds at least one new key or the loop stops — real files have at most a few hundred candidate pairs). Left `_collect_while_iter_args`'s own `$inputs`-pod mechanism untouched rather than generalizing it too, since no real file has yet shown a sequential-sibling `$inputs`-pod chain — revisit only if one does.

> **Superseded by decision 46**: a *third* independent occurrence of this exact bug class (in a third, separate registry) arrived in the very next session turn, and the user judged that on its own sufficient evidence to generalize now rather than wait for a fourth. `_collect_while_iter_args`/`trace_source` were retired; `ctx.input_pod_to_member` now goes through the same fixpoint mechanism as everything else.

## 46. Unified `ctx.input_pod_to_member`, `pod_to_member`, and `array_member_base` onto one `scf.while`-aliasing mechanism, retiring Part 1's own separate one

**Decision:** when a *third* independent registry (`pod_to_member`, driving scalar-subcomponent `.out` naming — `pEx.out` in `@Poseidon_70`) turned out to have the identical missing-`scf.while`-alias bug already fixed twice for `array_member_base` (§41, §42), replaced Part 1's own narrower, single-pass `_collect_while_iter_args`/`trace_source`/`result_to_init` mechanism (used only for `ctx.input_pod_to_member`, the `$inputs`-pod case) with the same general `_collect_while_region_array_aliases` + fixpoint resolution (decision 45) — rather than writing a *third* narrow, ad-hoc alias pass for `pod_to_member` alone and leaving three independently-maintained copies of conceptually the same resolution.

**Why:** decision 45 deliberately left `$inputs` alone, reasoning "no real file has shown it needing this yet." That reasoning held for exactly one more bug report — the moment a *third*, structurally unrelated registry hit the identical gap, the pattern itself (not any specific file) became the evidence: this codebase's `scf.while`-threading of long-lived values is pervasive enough that every registry built by walking a `@compute` body needs the same aliasing, and three independent, hand-rolled copies of "resolve a value's name across `scf.while` region boundaries" is exactly the kind of drift this project's own `CLAUDE.md`/`DECISIONS.md` conventions warn against (two — now three — independently-maintained copies of the same resolution logic is how these bugs happen in the first place, per this session's own §42 fix). The general fixpoint mechanism is provably a strict superset of what `trace_source`'s single top-level chain-walk did (its own `(own_result, own_init_val)` equivalence pair already subsumes exactly that chain, plus arbitrary depth and sibling chains `trace_source` never handled), so this was verified to be a safe replacement, not just a hopeful one — confirmed via the existing `TestBuildComponentNamingMapsNestedWhileInputs` test (Part 1's own real-world nested-`$inputs` case) still passing unchanged. `_collect_while_iter_args`/`trace_source`/`result_to_init` were deleted outright (confirmed via `grep` to have no other callers) rather than left dead in the file, since a translator this actively worked on shouldn't accumulate superseded-but-unremoved code paths that could be mistaken for still-relevant.

## 47. `components_info` extended for idx-pod members without touching `signal_renaming.py`, after confirming the addition is inert there

**Decision:** `StructDef.to_core`'s member-scan loop now also registers heterogeneous idx-pod members (`ark#N` → `"@Ark_i"`, reusing `_idx_pod_child_name`) into `subcomponent_members`/`ctx.member_to_struct` — but `signal_renaming.py`'s `process_components` was deliberately left untouched, rather than also teaching it to recognize an already-fully-suffixed `component_name` (skipping its own `#{occurrence}` append for that case).

**Why:** traced `process_components` precisely for an `ark` call before deciding anything, per the user's explicit "ensure the solution is general enough and no other point is affected" instruction. Because `ark`'s `.core`-level naming is already fully resolved at emission time (§33's `_annotate_idx_pod_component_reads` pre-pass), `extract_component(metadata)` returns the complete string `"ark#0"`, and `process_components` unconditionally appends its own `#{occurrence}` on top (no `components_index_sequences` entry exists for idx-pod members) — producing `"ark#0#0"`, which can never equal a `components_info` key of `"ark#0"`. So the new entries are provably inert with respect to that function's existing `if component_iteration in components:` gate: no key collision, no accidental new match introduced, no risk to any of the homogeneous-array or scalar renaming §41-43 already fixed. This also matches the user's own report that `ark`'s *signal* naming already works correctly independent of `components_info` — confirming there was no actual gap in `process_components`'s behavior to fix, only in the metadata field itself. Revisit only if a future consumer needs `process_components` to *also* rename `ark`'s `vars_info` entries under the `"ark#N.signal"` convention (it doesn't today — the raw pass-through entries already carry the correct, fully-resolved names) — that would be a new, separate requirement, not implied by this one.

## 48. Felt inequality (`lt`/`le`/`gt`/`ge`) trip-count simulation compares values via their canonical *signed* representative, not raw field elements

**Decision:** `_resolve_comparison_recurrence`'s `compare_func` construction (`core_utils.py`, §45) now reinterprets both the loop variable's current value and the bound through `_to_signed(value, prime)` (unchanged below `prime/2`, `value - prime` at or above it) before comparing, for `lt`/`le`/`gt`/`ge` only — `eq`/`ne` are left comparing raw field-element representations directly.

**Why:** `construct_function_from_expressions` already, correctly, reduces every update step modulo `prime` (a decrementing counter going below 0 wraps to `prime-1`, matching real field arithmetic — this is deliberate and required, see the pre-existing `TestPrimeAwareSimulation`). But a bounded felt counter's inequality condition (the ordinary way a circuit compiler emits "count down to and including 0", e.g. `ge(arg, 0)`) is only ever meaningful under the standard ZK-circuit convention that a field element `v >= prime/2` represents the negative integer `v - prime` — without that reinterpretation, a wrapped value is indistinguishable from an enormous positive one, and an inequality that was supposed to terminate the moment the counter "goes negative" instead runs for up to `prime` iterations (a genuine, real-file-confirmed hang, not a theoretical concern — `report_zisk_reduced/recursivef_concrete.mlir`'s `@VerifyPoW_11`). Equality/inequality checks (`eq`/`ne`) don't need this: two field elements are equal iff their *raw* representations are, regardless of which one is called "negative" — and the existing `ne`-predicate wraparound test already relies on exactly that (its bound is itself pre-wrapped to the value being matched, not reinterpreted). Scoped this narrowly to `_resolve_comparison_recurrence`'s own `compare_func`: `bool.py`'s separately-flagged `_PRED2CORE` le/ge copy-paste note (real Core emission, a different, already-documented pre-existing issue) and `BoolCmp._PRED_FNS`/`to_function` (a different call path, never reached from this while-condition resolution) are deliberately left untouched — no real example currently exercises either of those needing this same reinterpretation; revisit only if one does.

## 49. A while's loop-carried variable's own recurrence must resolve free variables via `var2const` too, before `update_func` is built — and unlike the bound, has no symbolic fallback if it can't

**Decision:** `_resolve_comparison_recurrence` (`core_utils.py`) now runs `_collect_free_var_names` + `var2const` fold-in (previously only applied to `bound`, §45/§48's neighborhood) against `variable` as well, immediately before calling `construct_function_from_expressions(variable, ...)` to build `update_func`. If any of `variable`'s own free variables aren't in `var2const`, this raises `NotImplementedError` naming the variable and the unresolved names — there is no `SymbolicSteps`-style fallback for the loop-carried variable's own update the way there is for the bound.

**Why:** `poseidon3_new_optimized.mlir`'s `MixS_9::compute` has a `scf.while` whose loop-carried variable's recurrence (`%next = felt.add %arg1, %felt_const_1`) directly reuses a `felt.const` hoisted *above* the while, rather than redefining it locally inside the body the way every sibling while loop in the same file does. `scf.py`'s `SCFWhile._build_while_var_expressions` only scans the while's own `before_body`/`after_body` when building `var2expression`, so this externally-defined operand never gets an entry — and `construct_function_from_expressions` crashed with a raw `KeyError` walking the recurrence chain, deep enough in the recursion that the caller had no way to produce a useful error message. The bound side of the same condition already had this exact resolution (an unresolved bound can legitimately fall back to a `SymbolicSteps` Core-level formula, since the bound is only evaluated once, not simulated per-iteration) — but the loop-carried variable's own update function *is* simulated per-iteration by `count_iterations`/`iterate_values`, so it must be a plain Python callable returning concrete ints; there's no way to defer an unresolved piece of it to a runtime Core expression the way `SymbolicSteps` does for the bound. Raising `NotImplementedError` here rather than reusing or extending `SymbolicSteps` keeps that distinction explicit: if a future example needs a genuinely symbolic loop-carried recurrence, that's a materially different (and more invasive) feature, not an extension of this fix.
