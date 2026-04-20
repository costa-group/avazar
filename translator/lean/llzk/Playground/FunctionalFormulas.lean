import Llzk.Basic
import Llzk.FFConstraints.Basic
import Llzk.FFConstraints.Satisfiability
import Std.Data.TreeSet.Lemmas

open Llzk.Language.Core.Syntax.AST
open Llzk.FFConstraints.Basic


structure IOFormula (c : ZKConfig) where
  inFFVars : FFVarSet := emptyFFVarSet
  auxFFVars : FFVarSet := emptyFFVarSet
  inBoolVars : BoolVarSet := emptyBoolVarSet
  auxBoolVars : BoolVarSet := emptyBoolVarSet
  f : FFFormula c := FFFormula.false

  hff : inFFVars ∩ auxFFVars = ∅
  hb  : inBoolVars ∩ auxBoolVars = ∅
  all_ff_vars : inFFVars ∪ auxFFVars = ffvars f
  all_bool_vars : inBoolVars ∪ auxBoolVars = boolvars f

  -- hfunct stands for a functional formula:
  --   for any σ (which is used as a valuation for inFFVars), we can obtain an assignment
  --   σ' that satisfies f such that σ(x) = σ'(x) for all x in inFFVars and inBoolVars.
  --   stronger version: σ' leaves all variables outside of inFFVars and inBoolVars unchanged,
  --   i.e., σ'(x) = σ(x) for all x not in inFFVars ∪ inBoolVars.
  -- FIXME: see what to do with macros "ms"
  hfunct :  ∀ (σ : Llzk.FFConstraints.Satisfiability.Assignment c) (ms : List (FFMacro c)),
            -- Llzk.FFConstraints.Satisfiability.evalFormula σ f ms = Except.ok true ->
              ∃ (σ' : Llzk.FFConstraints.Satisfiability.Assignment c),
                (∀ x: FFVar, x ∉ auxFFVars → σ.ff x.id = σ'.ff x.id) ∧
                (∀ x: BoolVar, x ∉ auxBoolVars → σ.bool x.id = σ'.bool x.id) ∧
                Llzk.FFConstraints.Satisfiability.evalFormula σ' f ms = Except.ok true
 -- 'hfunct' basically implies that every IOFormula is satisfiable. For every value of the input
 -- variables it is always possible to find correct values to the aux variables.

-- If ∀ x ∈ S, P(x) holds and S' ⊆ S, then ∀ x ∈ S', P(x) holds. For FFVarSet
theorem subset_ff_property {c : ZKConfig} (P : FFVar → Prop) (S S' : FFVarSet) :
  (∀ x ∈ S, P x) →
  S' ⊆ S →
  (∀ x ∈ S', P x) := by
intro h_all_S h_subset x h_x_in_S'
-- apply subset property
simp [Subset] at h_subset
have h_x_in_S : x ∈ S := h_subset x h_x_in_S'
have h_all_S_x := h_all_S x h_x_in_S
exact h_all_S_x

-- If ∀ x ∈ S, P(x) holds and S' ⊆ S, then ∀ x ∈ S', P(x) holds. For BoolVarSet
theorem subset_bool_property {c : ZKConfig} (P : BoolVar → Prop) (S S' : BoolVarSet) :
  (∀ x ∈ S, P x) →
  S' ⊆ S →
  (∀ x ∈ S', P x) := by
intro h_all_S h_subset x h_x_in_S'
-- apply subset property
simp [Subset] at h_subset
have h_x_in_S : x ∈ S := h_subset x h_x_in_S'
have h_all_S_x := h_all_S x h_x_in_S
exact h_all_S_x


mutual
theorem assignment_satisf_vars_formula {c : ZKConfig} (f : FFFormula c)
(σ σ' : Llzk.FFConstraints.Satisfiability.Assignment c) (ms : List (FFMacro c)) :
  (∀ x ∈ ffvars f, σ.ff x.id = σ'.ff x.id) →
  (∀ x ∈ boolvars f, σ.bool x.id = σ'.bool x.id) →
  Llzk.FFConstraints.Satisfiability.evalFormula σ f ms =
  Llzk.FFConstraints.Satisfiability.evalFormula σ' f ms :=
by
  -- by induction on the structure of f.f, requiring a mutual induction with the evaluation
  -- of terms and boolean formulas.
  sorry

theorem assignment_satisf_vars_term {c : ZKConfig} (t : FFTerm c)
(σ σ' : Llzk.FFConstraints.Satisfiability.Assignment c) (ms : List (FFMacro c)) :
  (∀ x ∈ ffvarsTerm t, σ.ff x.id = σ'.ff x.id) →
  (∀ x ∈ boolvarsTerm t, σ.bool x.id = σ'.bool x.id) →
  Llzk.FFConstraints.Satisfiability.evalTerm σ t ms =
  Llzk.FFConstraints.Satisfiability.evalTerm σ' t ms :=
by
  intros h_ffvars h_boolvars
  -- case distinction on the structure of t,
  cases t with
  | val v =>
      simp [Llzk.FFConstraints.Satisfiability.evalTerm]
  | var v =>
      simp [Llzk.FFConstraints.Satisfiability.evalTerm]
      have h_v_in_ffvars : v ∈ @ffvarsTerm c (FFTerm.var v) := by
        simp [ffvarsTerm]
      specialize h_ffvars v h_v_in_ffvars
      rw [h_ffvars]
  | add a b =>
      simp [Llzk.FFConstraints.Satisfiability.evalTerm]
      have ffvars_add : ffvarsTerm (a.add b) = (ffvarsTerm a).union (ffvarsTerm b) := by
        simp [ffvarsTerm]
      have h_subset_ffvars := @subset_ff_property c
        (fun x => σ.ff x.id = σ'.ff x.id)
        (ffvarsTerm a ∪ ffvarsTerm b) (ffvarsTerm a) (h_ffvars)
      have h_subset_ffvars_term_a : ffvarsTerm a ⊆ ffvarsTerm a ∪ ffvarsTerm b := by
        sorry
      simp at h_subset_ffvars
      have assign_term_a := h_subset_ffvars h_subset_ffvars_term_a
      have ih := assignment_satisf_vars_term a σ σ' ms assign_term_a

      sorry
  | sub a b =>
      simp [Llzk.FFConstraints.Satisfiability.evalTerm]
      sorry
  | mul a b =>
      simp [Llzk.FFConstraints.Satisfiability.evalTerm]
      sorry
  | neg a =>
      simp [Llzk.FFConstraints.Satisfiability.evalTerm]
      have assignment_a := assignment_satisf_vars_term a σ σ' ms h_ffvars h_boolvars
      exact assignment_a
  | ite cond t e =>
      simp [Llzk.FFConstraints.Satisfiability.evalTerm]
      sorry

end

#check Std.TreeSet.contains_union
#check Std.TreeSet.isEmpty_inter_iff
--#check Std.TreeSet.uni


-- This should be part of the Std library
theorem elem_in_union_treeset {α : Type} [BEq α] [Ord α] (s1 s2 : Std.TreeSet α) (x : α) :
  x ∈ s1 ∪ s2 ↔ x ∈ s1 ∨ x ∈ s2 := by
rw [Std.TreeSet.mem_iff_contains]
sorry


-- This should be part of the Std library
theorem isEmpty_equal_empty_treeset {α : Type} [BEq α] [Ord α] (s : Std.TreeSet α) :
  s.isEmpty ↔ s = ∅ := by
simp [Std.TreeSet.isEmpty, Std.TreeSet.empty]

-- This should be part of the Std library
theorem inter_comm {α : Type} [BEq α] [Ord α] (s1 s2 : Std.TreeSet α) :
  s1 ∩ s2 = s2 ∩ s1 := by
sorry


theorem treeset_not_in_aux' {α : Type} [BEq α] [Ord α]
    [Std.TransCmp (compare (α := α))] (S A B C : Std.TreeSet α) :
  S = A ∪ B ->
  C ∩ A = ∅ ->
  B ∩ C = ∅ ->
  ∀ x ∈ S, x ∉ C := by
intro hS hCA hBC x hx
rw [hS] at hx
rw [elem_in_union_treeset] at hx
cases hx with
| inl hxA =>
  rw [← isEmpty_equal_empty_treeset] at hCA
  rw [inter_comm] at hCA
  rw [Std.TreeSet.isEmpty_inter_iff] at hCA
  specialize hCA x hxA
  exact hCA
| inr hxB =>
  rw [← isEmpty_equal_empty_treeset] at hBC
  rw [Std.TreeSet.isEmpty_inter_iff] at hBC
  specialize hBC x hxB
  exact hBC


/-
P1;P2 and the formulas are f1 and f2


If we have two IOFormulas f1 and f2 such that

 f2.auxFFVars ∩ f1.inFFVars = ∅
 f2.auxBoolVars ∩ f1.inBooVars = ∅

Theorem T:
Any assignment ρ that satisfies f1.f can be extended to an assignment ρ'
that satisfies f2.f by assigning "arbitrary" values to the variables in
f2.auxFFVars and f2.auxBoolVars.
-/
theorem formula_combination {c : ZKConfig} (f1 f2 : IOFormula c) (ms : List (FFMacro c)) :
  f2.auxFFVars ∩ f1.inFFVars = ∅ →
  f2.auxBoolVars ∩ f1.inBoolVars = ∅ →
  f1.auxFFVars ∩ f2.auxFFVars = ∅ →
  f1.auxBoolVars ∩ f2.auxBoolVars = ∅ →
  ∀ σ, Llzk.FFConstraints.Satisfiability.evalFormula σ f1.f ms = Except.ok true →
          ∃ σ', (∀ x: FFVar, x ∉ f2.auxFFVars → σ.ff x.id = σ'.ff x.id) ∧
                (∀ x: BoolVar, x ∉ f2.auxBoolVars → σ.bool x.id = σ'.bool x.id) ∧
                Llzk.FFConstraints.Satisfiability.evalFormula σ' f2.f ms = Except.ok true ∧
                Llzk.FFConstraints.Satisfiability.evalFormula σ' f1.f ms = Except.ok true
  := by
  intro h_auxFF_disjoint1 h_auxBool_disjoint1 h_auxFF_disjoint2 h_auxBool_disjoint2 σ h_eval_f1
  have h_f2_func := f2.hfunct σ ms
  obtain ⟨σ', h_ff2, h_bool2, h_eval2⟩ := h_f2_func
  have h_ffvars_f1 : ∀ x ∈ ffvars f1.f, σ.ff x.id = σ'.ff x.id := by
    intro x h_x_in_ffvars_f1
    have h_x_not_in := treeset_not_in_aux' (ffvars f1.f) (f1.inFFVars) (f1.auxFFVars)
         (f2.auxFFVars) (f1.all_ff_vars.symm) (h_auxFF_disjoint1) (h_auxFF_disjoint2) x h_x_in_ffvars_f1
    specialize h_ff2 x h_x_not_in
    exact h_ff2
  have h_boolvars_f1 : ∀ x ∈ boolvars f1.f, σ.bool x.id = σ'.bool x.id := by
    intro x h_x_in_boolvars_f1
    have h_x_not_in := treeset_not_in_aux' (boolvars f1.f) (f1.inBoolVars) (f1.auxBoolVars)
         (f2.auxBoolVars) (f1.all_bool_vars.symm) (h_auxBool_disjoint1) (h_auxBool_disjoint2) x h_x_in_boolvars_f1
    specialize h_bool2 x h_x_not_in
    exact h_bool2
  have eq_eval_f1 := assignment_satisf_vars_formula f1.f σ σ' ms h_ffvars_f1 h_boolvars_f1
  rw [h_eval_f1] at eq_eval_f1
  exact ⟨σ', h_ff2, h_bool2, h_eval2, eq_eval_f1.symm⟩

/-
Other interesting properties about aux variables in IOFormulas (same for bool vars). These should
follow from the fact that aux variables are "freshly" generated and do not overlap with anything else:

  f1.auxFFVars ∩ f2.auxFFVars = ∅
  f1.inFFVars ∩ f1.auxFFVars = ∅
  f2.inFFVars ∩ f2.auxFFVars = ∅
  f2.inFFVars can contain variables in f1.inFFVars, f1.auxFFVars, or variables that are not in f1 at all.

Proof sketch of Theorem T:
  Let ρ be an assignment that satisfies f1.f. By definition it assigns values to the variables in
  f1.inFFVars ⊎ f1.auxFFVars.

  Case distinction on whether f2.inFFVars is a subset of f1.inFFVars ⊎ f1.auxFFVars or not.

  * If f2.inFFVars ⊆ f1.inFFVars ⊎ f1.auxFFVars, then we can directly extend ρ to ρ' by hf, and
    it will satisfy f2.f.

  * If f2.inFFVars ⊄ f1.inFFVars ⊎ f1.auxFFVars, then f2.inFFVars must contain some variables S that are not
    in f1.inFFVars ⊎ f1.auxFFVars (i.e., S = f2.inFFVars \ (f1.inFFVars ⊎ f1.auxFFVars)). We can extend ρ
    with arbitrary values for the variables in S, obtaining ρ''. ρ'' satisfies f1.f and by hf of f2, we can
    extend it to ρ' that satisfies f2.f.


IDEA: when working with assignments, we can find it interesting to keep them minimal, i.e., only assign values
to the variables that are needed for the next formula. We can always restrict the assignments to subsets of
relevant variables: ρ|_S

-/
