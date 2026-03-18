import Llzk.Basic
import Llzk.FFConstraints.Basic
import Llzk.FFConstraints.Satisfiability

open Llzk.Language.Core.Syntax.AST
open Llzk.FFConstraints.Basic


structure IOFormula (c : ZKConfig) where
  inFFVars : FFVarSet := emptyFFVarSet
  auxFFVars : FFVarSet := emptyFFVarSet
  auxBoolVars : BoolVarSet := emptyBoolVarSet
  f : FFFormula c := FFFormula.false
  h : inFFVars ∩ auxFFVars = ∅
  -- hf stands for a functional formula
  --  for any ρ (which is used as a valuation for inFFVars), we can obtain assignment ρ' that
  --  satisfies f such that ρ(x) = ρ'(x) for all x in inFFVars.
  --  This is a technical condition that is needed for the proofs later.
  deriving Inhabited



/-

P1;P2 and the formulas are f1 and f2


If we have two IOFormulas f1 and f2 such that

 f2.auxFFVars ∩ f1.inFFVars = ∅
 f2.auxBoolVars ∩ f1.inBooVars = ∅

Any assignment ρ that satisfies f1.f can be extended to an assignment ρ'
that satisfies f2.f by assigning "arbitrary" values to the variables in
f2.auxFFVars and f2.auxBoolVars.



-/
