import Llzk.Basic
import Llzk.FFConstraints.Basic
import Llzk.FFConstraints.Satisfiability

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

  -- hf stands for a functional formula:
  --   for any σ (which is used as a valuation for inFFVars), we can obtain assignment
  --   σ' that satisfies f such that σ(x) = σ'(x) for all x in inFFVars and inBoolVars.
  hfunct :  ∀ (σ : Llzk.FFConstraints.Satisfiability.Assignment c) (ms : List (FFMacro c)),
            -- Llzk.FFConstraints.Satisfiability.evalFormula σ f ms = Except.ok true ->
              ∃ (σ' : Llzk.FFConstraints.Satisfiability.Assignment c),
                (∀ x ∈ inFFVars, σ.ff x.id = σ'.ff x.id) ∧
                (∀ x ∈ inBoolVars, σ.bool x.id = σ'.bool x.id) ∧
                Llzk.FFConstraints.Satisfiability.evalFormula σ' f ms = Except.ok true
 -- 'hfunct' basically says that every IOFormula is satisfiable. For every value of the input variables
 -- it is always possible to find correct values to the aux variables.

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
  (f2.auxFFVars ∩ f1.inFFVars = ∅) →
  (f2.auxBoolVars ∩ f1.inBoolVars = ∅) →
  (f1.auxFFVars ∩ f2.auxFFVars = ∅) →
  (f1.inFFVars ∩ f1.auxFFVars = ∅) →
  (f2.inFFVars ∩ f2.auxFFVars = ∅) →
  (∀ σ, Llzk.FFConstraints.Satisfiability.evalFormula σ f1.f ms = Except.ok true →
          ∃ σ', (∀ x ∈ f1.inFFVars, σ.ff x.id = σ'.ff x.id) ∧
                (∀ x ∈ f1.inBoolVars, σ.bool x.id = σ'.bool x.id) ∧
                (∀ x ∈ f1.auxFFVars, σ.ff x.id = σ'.ff x.id) ∧
                (∀ x ∈ f1.auxBoolVars, σ.bool x.id = σ'.bool x.id) ∧
                Llzk.FFConstraints.Satisfiability.evalFormula σ' f2.f ms = Except.ok true)
  := by
    sorry
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
