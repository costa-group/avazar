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


theorem assignment_satisf_vars {c : ZKConfig} (f : IOFormula c)
(σ σ' : Llzk.FFConstraints.Satisfiability.Assignment c) (ms : List (FFMacro c)) :
  (∀ x ∈ ffvars f.f, σ.ff x.id = σ'.ff x.id) →
  (∀ x ∈ boolvars f.f, σ.bool x.id = σ'.bool x.id) →
  Llzk.FFConstraints.Satisfiability.evalFormula σ f.f ms =
  Llzk.FFConstraints.Satisfiability.evalFormula σ' f.f ms :=
by
  -- by induction on the structure of f.f, requiring a mutual induction with the evaluation
  -- of terms and boolean formulas.
  sorry


#check Std.TreeSet.contains_union

theorem ffvar_not_in_auxff' {c : ZKConfig} (S A B C: FFVarSet) :
  S = A ∪ B ->
  C ∩ A = ∅ ->
  B ∩ C = ∅ ->
  ∀ x ∈ S, x ∉ C := by
sorry
/-
intro hS hCA hBC x hx
rw [hS] at hx
simp only [Std.TreeSet.instMembership, Std.TreeSet.contains_union, Bool.or_eq_true] at hx
rw [Std.TreeSet.contains_union] at hx
cases hx with
| inl hxA =>
  have : x ∈ C ∩ A := Std.TreeSet.mem_inter.mpr ⟨hxC, hxA⟩
  rw [hCA] at this
  exact Std.TreeSet.not_mem_empty x this
| inr hxB =>
  have : x ∈ B ∩ C := Std.TreeSet.mem_inter.mpr ⟨hxB, hxC⟩
  rw [hBC] at this
  exact Std.TreeSet.not_mem_empty x this
-/



theorem boolvar_not_in_auxff' {c : ZKConfig} (S A B C: BoolVarSet) :
  S = A ∪ B ->
  C ∩ A = ∅ ->
  B ∩ C = ∅ ->
  ∀ x ∈ S, x ∉ C := by
  sorry

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
    have h_x_not_in := @ffvar_not_in_auxff' c (ffvars f1.f) (f1.inFFVars) (f1.auxFFVars)
         (f2.auxFFVars) (f1.all_ff_vars.symm) (h_auxFF_disjoint1) (h_auxFF_disjoint2) x h_x_in_ffvars_f1
    specialize h_ff2 x h_x_not_in
    exact h_ff2
  have h_boolvars_f1 : ∀ x ∈ boolvars f1.f, σ.bool x.id = σ'.bool x.id := by
    intro x h_x_in_boolvars_f1
    have h_x_not_in := @boolvar_not_in_auxff' c (boolvars f1.f) (f1.inBoolVars) (f1.auxBoolVars)
         (f2.auxBoolVars) (f1.all_bool_vars.symm) (h_auxBool_disjoint1) (h_auxBool_disjoint2) x h_x_in_boolvars_f1
    specialize h_bool2 x h_x_not_in
    exact h_bool2
  have eq_eval_f1 := assignment_satisf_vars f1 σ σ' ms h_ffvars_f1 h_boolvars_f1
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
