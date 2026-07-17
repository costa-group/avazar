import Corellzk2smt.Basic
import Corellzk2smt.Config
import Corellzk2smt.FFConstraints.Basic
import Corellzk2smt.FFConstraints.Satisfiability
import Corellzk2smt.FFConstraints.Satisfiability_th

namespace Corellzk2smt.FFConstraints.FunctionalFormula

open Corellzk2smt.Config (GlobalConfig)
open Corellzk2smt.FFConstraints.Basic
open Corellzk2smt.FFConstraints.Satisfiability
open Corellzk2smt.FFConstraints.Satisfiability_th

-- ---------------------------------------------------------------------------
-- Small VarSet lemmas
-- ---------------------------------------------------------------------------

/-- Union is monotone w.r.t. `⊆`. -/
theorem union_subset_union {s1 s2 t1 t2 : VarSet} (h1 : s1 ⊆ t1) (h2 : s2 ⊆ t2) :
    s1 ∪ s2 ⊆ t1 ∪ t2 := by
  intro x hx
  rcases Std.TreeSet.mem_union_iff.mp hx with hx1 | hx2
  · exact Std.TreeSet.mem_union_of_left (h1 x hx1)
  · exact Std.TreeSet.mem_union_of_right (h2 x hx2)

/-- The empty var set is a subset of everything. -/
theorem emptyVarSet_subset {s : VarSet} : emptyVarSet ⊆ s :=
  fun _x hx => absurd hx Std.TreeSet.not_mem_emptyc

/-- If both `s` and `t` land inside `u`, so does their union. -/
theorem union_subset {s t u : VarSet} (h1 : s ⊆ u) (h2 : t ⊆ u) : s ∪ t ⊆ u :=
  fun x hx => (Std.TreeSet.mem_union_iff.mp hx).elim (h1 x) (h2 x)

-- ---------------------------------------------------------------------------
-- Functional formula predicate
-- ---------------------------------------------------------------------------

/-- `<f, inVs, ffVs, bVs>` is a functional formula when:
    - `inVs ⊆ ffVs` (inputs are a subset of all FF vars)
    - `ffVarsOfFormula f ⊆ ffVs` (`f` only reads FF vars declared in `ffVs`)
    - `bVarsOfFormula f ⊆ bVs`   (`f` only reads bool vars declared in `bVs`)
    - For **any** assignment `rho`, there exists `rho'` such that:
        (1) `rho'` agrees with `rho` on `inVs`        (inputs are fixed)
        (2) `rho'` only modifies FF vars within `ffVs` (frame for FF vars)
        (3) `rho'` only modifies bool vars within `bVs`(frame for bool vars)
        (4) `rho'` satisfies `f`

    Conditions (2)-(3) are the "frame conditions": they ensure that when we
    extend an assignment to satisfy `f`, we only touch vars that `f` cares
    about, leaving everything else intact. This is what lets us chain two
    functional formulas (composition). The second and third conditions above
    let us derive `f`'s congruence property (`evalFormula_congr`) straight
    from the declared var sets `ffVs`/`bVs`, instead of assuming it as a
    separate hypothesis at every call site. -/
def isFunctionalFormula {c : ZKConfig}
    (gconf : GlobalConfig c)
    (ms : List (FFMacro c))
    (f : FFFormula c)
    (inVs ffVs bVs : VarSet) : Prop :=
  inVs ⊆ ffVs ∧
  ffVarsOfFormula f ⊆ ffVs ∧
  bVarsOfFormula f ⊆ bVs ∧
  ∀ (rho : Assignment c),
    ∃ (rho' : Assignment c),
      agreesOnFF inVs rho rho' ∧
      (∀ n, Var.ffv n ∉ ffVs → rho'.ff n = rho.ff n) ∧
      (∀ n, Var.boolv n ∉ bVs → rho'.bool n = rho.bool n) ∧
      evalFormula gconf rho' f ms = Except.ok true



-- ---------------------------------------------------------------------------
-- Composition theorem
-- ---------------------------------------------------------------------------

/-- **Composition** (from notes.md):

    Given functional formulas `<f1, inVs1, ffVs1, bVs1>` and
    `<f2, inVs2, ffVs2, bVs2>` such that `inVs2 ⊆ ffVs1`, the conjunction
    `f1 ∧ f2` is functional with inputs `inVs1` and vars `ffVs1 ∪ ffVs2`.

    **Proof sketch**:
    Given any `rho`:
    1. Extend `rho` using `h1` to get `rho1` that satisfies `f1` and only
       touches `ffVs1 / bVs1`.
    2. `rho1` already has values for all of `inVs2` (since `inVs2 ⊆ ffVs1`).
       Extend `rho1` using `h2` to get `rho2` that satisfies `f2` and only
       touches `ffVs2 / bVs2`.
    3. `rho2` agrees with `rho` on `inVs1` (via transitivity, using the
       disjointness condition to know `rho2` doesn't change `inVs1`).
    4. `rho2` satisfies `f1` as well: the only changes `rho2` makes (vs
       `rho1`) are on `ffVs2 / bVs2`, and the disjointness conditions ensure
       those don't overlap with the vars of `f1` (= subset of `ffVs1 / bVs1`).

    **Key extra hypothesis** (implicit in the notes, required here):
    `h_disj_ff / h_disj_bool`: the "own" vars of `f2` (those in `ffVs2 / bVs2`
    but NOT in `inVs2`) don't overlap with `ffVs1 / bVs1`. In symbolic
    execution this holds because all constraint variables are generated fresh
    (via `nextVarId`). -/
theorem functionalCompose {c : ZKConfig}
    (gconf : GlobalConfig c)
    (ms : List (FFMacro c))
    (f1 f2 : FFFormula c)
    (inVs1 inVs2 ffVs1 ffVs2 bVs1 bVs2 : VarSet)
    -- f1 and f2 are separately functional
    (h1 : isFunctionalFormula gconf ms f1 inVs1 ffVs1 bVs1)
    (h2 : isFunctionalFormula gconf ms f2 inVs2 ffVs2 bVs2)
    -- The inputs to f2 come from the vars of f1 -- this is the intended data-flow
    -- story from notes.md (f2 consumes what f1 produces), kept here as documentation
    -- of that use case. It is NOT used by the proof below: `h2_ext` is universal
    -- over any starting assignment, so it happily extends `rho1` regardless of
    -- where its values on `inVs2` came from. The overlap between `ffVs1`/`ffVs2`
    -- is instead handled entirely by `h_disj_ff`.
    -- (_h_link : inVs2 ⊆ ffVs1)
    -- any var shared by ffVs1 and ffVs2 must be an input to f2
    -- (the "private" vars of f2 are disjoint from all of f1's vars)
    (h_disj_ff : ∀ n, Var.ffv n ∈ ffVs1 → Var.ffv n ∈ ffVs2 → Var.ffv n ∈ inVs2)
    -- bool vars of f1 and f2 are disjoint (always fresh in symbolic exec)
    (h_disj_bool : ∀ n, Var.boolv n ∈ bVs1 → Var.boolv n ∉ bVs2)
    : isFunctionalFormula gconf ms (.and f1 f2) inVs1 (ffVs1 ∪ ffVs2) (bVs1 ∪ bVs2) := by
  obtain ⟨h1_sub, h1_ffv_sub, h1_bv_sub, h1_ext⟩ := h1
  obtain ⟨_h2_sub, h2_ffv_sub, h2_bv_sub, h2_ext⟩ := h2
  -- f1's congruence, derived from its declared var sets rather than assumed
  have h1_congr : ∀ (a b : Assignment c),
      agreesOnFF ffVs1 a b →
      agreesOnBool bVs1 a b →
      evalFormula gconf a f1 ms = evalFormula gconf b f1 ms :=
    fun a b hff hbool =>
      evalFormula_congr gconf ms f1 a b
        (agreesOnFF_mono h1_ffv_sub hff)
        (agreesOnBool_mono h1_bv_sub hbool)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- inVs1 ⊆ ffVs1 ∪ ffVs2
    intro v hv
    exact Std.TreeSet.mem_union_of_left (h1_sub v hv)
  · -- ffVarsOfFormula (f1 ∧ f2) ⊆ ffVs1 ∪ ffVs2
    exact union_subset_union h1_ffv_sub h2_ffv_sub
  · -- bVarsOfFormula (f1 ∧ f2) ⊆ bVs1 ∪ bVs2
    exact union_subset_union h1_bv_sub h2_bv_sub
  intro rho
  -- Step 1: extend rho to satisfy f1
  obtain ⟨rho1, h1_agree, h1_ff_frame, h1_bool_frame, h1_sat⟩ := h1_ext rho
  -- Step 2: extend rho1 (which already assigns inVs2) to satisfy f2
  obtain ⟨rho2, h2_agree, h2_ff_frame, h2_bool_frame, h2_sat⟩ := h2_ext rho1
  -- rho2 is our witness
  refine ⟨rho2, ?_, ?_, ?_, ?_⟩
  --
  · -- (1) rho2 agrees with rho on inVs1
    intro n hn
    have hn_in_ffVs1 : Var.ffv n ∈ ffVs1 := h1_sub (Var.ffv n) hn
    -- rho.ff n = rho1.ff n  (rho1 satisfies inVs1-agreement from h1)
    have step1 : rho.ff n = rho1.ff n := h1_agree n hn
    -- rho1.ff n = rho2.ff n:
    --   if n ∈ ffVs2 then n ∈ inVs2 (by h_disj_ff), and h2 agrees on inVs2
    --   if n ∉ ffVs2 then rho2 = rho1 there (frame), so .symm gives the direction
    have step2 : rho1.ff n = rho2.ff n := by
      by_cases hn2 : Var.ffv n ∈ ffVs2
      · exact h2_agree n (h_disj_ff n hn_in_ffVs1 hn2)
      · exact (h2_ff_frame n hn2).symm
    exact step1.trans step2
  --
  · -- (2) Frame for FF: rho2 only changes vars in ffVs1 ∪ ffVs2
    intro n hn
    have hn1 : Var.ffv n ∉ ffVs1 := fun h => hn (Std.TreeSet.mem_union_of_left h)
    have hn2 : Var.ffv n ∉ ffVs2 := fun h => hn (Std.TreeSet.mem_union_of_right h)
    -- rho2 = rho1 outside ffVs2, and rho1 = rho outside ffVs1
    exact (h2_ff_frame n hn2).trans (h1_ff_frame n hn1)
  --
  · -- (3) Frame for Bool: rho2 only changes vars in bVs1 ∪ bVs2
    intro n hn
    have hn1 : Var.boolv n ∉ bVs1 := fun h => hn (Std.TreeSet.mem_union_of_left h)
    have hn2 : Var.boolv n ∉ bVs2 := fun h => hn (Std.TreeSet.mem_union_of_right h)
    exact (h2_bool_frame n hn2).trans (h1_bool_frame n hn1)
  --
  · -- (4) rho2 satisfies f1 ∧ f2
    -- First show rho2 agrees with rho1 on all vars of f1 (inside ffVs1/bVs1)
    have h_agree_ff1 : agreesOnFF ffVs1 rho2 rho1 := by
      intro n hn
      by_cases hn2 : Var.ffv n ∈ ffVs2
      · -- shared var: must be in inVs2, so rho2 agrees with rho1 there
        exact (h2_agree n (h_disj_ff n hn hn2)).symm
      · -- private to f1: rho2 = rho1 outside ffVs2
        exact h2_ff_frame n hn2
    have h_agree_bool1 : agreesOnBool bVs1 rho2 rho1 := by
      intro n hn
      -- bVs1 and bVs2 are disjoint, so n ∉ bVs2
      exact h2_bool_frame n (h_disj_bool n hn)
    -- By congruence, rho2 also satisfies f1
    have h_f1_rho2 : evalFormula gconf rho2 f1 ms = Except.ok true :=
      (h1_congr rho2 rho1 h_agree_ff1 h_agree_bool1).trans h1_sat
    -- Unfold evalFormula for .and and combine
    simp only [evalFormula, h_f1_rho2, h2_sat, Bool.true_and]


-- ---------------------------------------------------------------------------
-- Disjunction theorem
-- ---------------------------------------------------------------------------

/-- **Disjunction** (from notes.md):

    Given functional formulas `<f1, inVs, ffVs1, bVs1>` and `<f2, inVs, ffVs2, bVs2>`
    with the **same** input set, and a guard formula `g` such that:
      - `g` evaluates without error on any assignment (`h_g_total`)
      - `ffVarsOfFormula g ⊆ inVs` and `bVarsOfFormula g = ∅`, so `g`'s value is
        preserved by any extension that agrees on `inVs` (this is what lets us
        derive `g`'s congruence from `evalFormula_congr` instead of assuming it)
      - `f1` and `f2` both evaluate without error on any assignment (`h_f1_total`,
        `h_f2_total`) — needed because `evalFormula`'s `.and`/`.or` never
        short-circuit: both sides are always evaluated, so e.g. in the "true"
        branch below, `f2` still has to succeed (its *value* doesn't matter,
        only that it isn't an error) at a witness built for `f1`, which
        `isFunctionalFormula ms f2 ...` alone can't guarantee (see `wellFormedFormula`
        / `evalFormula_total` for a purely syntactic way to discharge this)

    then `g∧f1 ∨ ¬g∧f2` is functional with inputs `inVs` and vars `ffVs1∪ffVs2`.

    **Proof sketch**:
    Given any `rho`, evaluate `g(rho)`:
    - If `true`:  extend via h1 to get `rho'` satisfying f1.
                  Since rho' agrees with rho on inVs, g(rho') = true as well,
                  so the first disjunct `g∧f1` holds. `f2` is evaluated at `rho'`
                  too (by `h_f2_total`), but its value is irrelevant: it's ANDed
                  with `¬g = false`, so the second disjunct is `false` and the
                  overall `||` is `true` regardless.
    - If `false`: symmetric, extending via h2 to get `rho'` satisfying f2, with
                  `f1`'s value at `rho'` (via `h_f1_total`) irrelevant this time.

    No disjointness conditions are needed: the two branches are mutually exclusive,
    so there is no cross-branch interference to guard against. -/
theorem functionalDisjunction {c : ZKConfig}
    (gconf : GlobalConfig c)
    (ms : List (FFMacro c))
    (f1 f2 g : FFFormula c)
    (inVs ffVs1 ffVs2 bVs1 bVs2 : VarSet)
    -- f1 and f2 are separately functional, with the same input set
    (h1 : isFunctionalFormula gconf ms f1 inVs ffVs1 bVs1)
    (h2 : isFunctionalFormula gconf ms f2 inVs ffVs2 bVs2)
    -- g evaluates to a definite boolean on every assignment (no errors)
    (h_g_total : isTotal gconf g ms)
    -- g only reads FF vars from inVs, and no bool vars at all
    (h_g_ffvars : ffVarsOfFormula g ⊆ inVs)
    (h_g_bvars : bVarsOfFormula g = emptyVarSet)
    -- f1/f2 evaluate without error on any assignment, not just at their own
    -- witnesses -- see the docstring above for why this can't be dropped
    (h_f1_total : isTotal gconf f1 ms)
    (h_f2_total : isTotal gconf f2 ms)
    : isFunctionalFormula gconf ms (.or (.and g f1) (.and (.not g) f2))
                          inVs (ffVs1 ∪ ffVs2) (bVs1 ∪ bVs2) := by
  -- g's congruence, derived from its declared var sets rather than assumed
  have h_g_congr : ∀ (a b : Assignment c), agreesOnFF inVs a b →
      evalFormula gconf a g ms = evalFormula gconf b g ms :=
    fun a b hff =>
      evalFormula_congr gconf ms g a b
        (agreesOnFF_mono h_g_ffvars hff)
        (h_g_bvars ▸ fun n hn => absurd hn Std.TreeSet.not_mem_emptyc)
  obtain ⟨h1_sub, h1_ffv_sub, h1_bv_sub, h1_ext⟩ := h1
  obtain ⟨h2_sub, h2_ffv_sub, h2_bv_sub, h2_ext⟩ := h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- inVs ⊆ ffVs1 ∪ ffVs2
    intro v hv
    exact Std.TreeSet.mem_union_of_left (h1_sub v hv)
  · -- ffVarsOfFormula of the whole disjunction ⊆ ffVs1 ∪ ffVs2
    have hg_ffv : ffVarsOfFormula g ⊆ ffVs1 ∪ ffVs2 :=
      fun x hx => Std.TreeSet.mem_union_of_left (h1_sub x (h_g_ffvars x hx))
    have hf1_ffv : ffVarsOfFormula f1 ⊆ ffVs1 ∪ ffVs2 :=
      fun x hx => Std.TreeSet.mem_union_of_left (h1_ffv_sub x hx)
    have hf2_ffv : ffVarsOfFormula f2 ⊆ ffVs1 ∪ ffVs2 :=
      fun x hx => Std.TreeSet.mem_union_of_right (h2_ffv_sub x hx)
    exact union_subset (union_subset hg_ffv hf1_ffv) (union_subset hg_ffv hf2_ffv)
  · -- bVarsOfFormula of the whole disjunction ⊆ bVs1 ∪ bVs2
    have hg_bv : bVarsOfFormula g ⊆ bVs1 ∪ bVs2 := h_g_bvars ▸ emptyVarSet_subset
    have hf1_bv : bVarsOfFormula f1 ⊆ bVs1 ∪ bVs2 :=
      fun x hx => Std.TreeSet.mem_union_of_left (h1_bv_sub x hx)
    have hf2_bv : bVarsOfFormula f2 ⊆ bVs1 ∪ bVs2 :=
      fun x hx => Std.TreeSet.mem_union_of_right (h2_bv_sub x hx)
    exact union_subset (union_subset hg_bv hf1_bv) (union_subset hg_bv hf2_bv)
  intro rho
  obtain ⟨vg, hvg⟩ := h_g_total rho
  cases vg with
  | true =>
      -- Extend rho to satisfy f1; g is preserved (via congruence) since the
      -- extension agrees with rho on inVs
      obtain ⟨rho', h1_agree, h1_ff_frame, h1_bool_frame, h1_sat⟩ := h1_ext rho
      have hg_rho' : evalFormula gconf rho' g ms = Except.ok true := by
        rw [← h_g_congr rho rho' h1_agree]
        exact hvg
      -- f2 must not error at rho', but its actual value is irrelevant
      obtain ⟨vf2, hf2_rho'⟩ := h_f2_total rho'
      refine ⟨rho', h1_agree, ?_, ?_, ?_⟩
      · intro n hn
        exact h1_ff_frame n (fun h => hn (Std.TreeSet.mem_union_of_left h))
      · intro n hn
        exact h1_bool_frame n (fun h => hn (Std.TreeSet.mem_union_of_left h))
      · simp [evalFormula, hg_rho', h1_sat, hf2_rho']
  | false =>
      -- Symmetric: extend rho to satisfy f2, f1 just needs to not error
      obtain ⟨rho', h2_agree, h2_ff_frame, h2_bool_frame, h2_sat⟩ := h2_ext rho
      have hg_rho' : evalFormula gconf rho' g ms = Except.ok false := by
        rw [← h_g_congr rho rho' h2_agree]
        exact hvg
      obtain ⟨vf1, hf1_rho'⟩ := h_f1_total rho'
      refine ⟨rho', h2_agree, ?_, ?_, ?_⟩
      · intro n hn
        exact h2_ff_frame n (fun h => hn (Std.TreeSet.mem_union_of_right h))
      · intro n hn
        exact h2_bool_frame n (fun h => hn (Std.TreeSet.mem_union_of_right h))
      · simp [evalFormula, hg_rho', hf1_rho', h2_sat]

end Corellzk2smt.FFConstraints.FunctionalFormula
