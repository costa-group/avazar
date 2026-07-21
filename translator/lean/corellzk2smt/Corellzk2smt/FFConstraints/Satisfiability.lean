import Corellzk2smt.Basic
import Corellzk2smt.FFConstraints.Basic
import Corellzk2smt.Config
import Corellzk2smt.Language.Core.Semantics.Basic

/-
This module defines executable semantics and satisfiability predicates for finite-field
constraint formulas and systems.
-/
namespace Corellzk2smt.FFConstraints.Satisfiability

open Corellzk2smt.Config (GlobalConfig)
open Corellzk2smt.FFConstraints.Basic
open Corellzk2smt.Language.Core.Semantics.Basic (evalLe)

/- An assignment maps variables to values. There are two types of
   variables, finite field variables and boolean variables, so we have
   two maps -/
structure Assignment (c : ZKConfig) where
  ff : FFVar → FF c
  bool : BoolVar → Bool
  deriving Inhabited

/- Renaming of variables for macro calls
   Version with tail recursion and accumulators (ffMap, boolMap) -/
def newAssignment' {c : ZKConfig}
   (assign : Assignment c)
   (args : List (MacroCallParam c)) (params : List Var)
   (ffMap : FFVar → FF c)
   (boolMap : BoolVar → Bool) : Except String (Assignment c) :=
  match params, args with
  | [], [] => Except.ok { ff := ffMap, bool := boolMap }
  -- parameter is a FFVar, argument is also a FFVar
  | (Var.ffv p) :: params', (MacroCallParam.var (Var.ffv a)) :: args' =>
    let ffMap' : FFVar → FF c := fun id => if id == p then assign.ff a else ffMap id
    newAssignment' assign args' params' ffMap' boolMap
  -- parameter is a FFVar, argument is also a FF value
  | (Var.ffv p) :: params', (MacroCallParam.const (Const.ffc t)) :: args' =>
    let ffMap' : FFVar → FF c := fun id => if id == p then t else ffMap id
    newAssignment' assign args' params' ffMap' boolMap
  -- parameter is a BoolVar, argument is also a BoolVar
  | (Var.boolv p) :: params', (MacroCallParam.var (Var.boolv a)) :: args' =>
    let boolMap' : BoolVar → Bool := fun id => if id == p then assign.bool a else boolMap id
    newAssignment' assign args' params' ffMap boolMap'
  -- parameter is a BoolVar, argument is also a Bool value
  | (Var.boolv p) :: params', (MacroCallParam.const (Const.boolc t)) :: args' =>
    let boolMap' : BoolVar → Bool := fun id => if id == p then t else boolMap id
    newAssignment' assign args' params' ffMap boolMap'
  --valther combination is an error
  | _, _ => Except.error "Mismatched variable lists"

def newAssignment {c : ZKConfig}
   (assign : Assignment c)
   (args : List (MacroCallParam c)) (params : List Var) : Except String (Assignment c) :=
  let ffMap : FFVar → FF c := fun _id => 0
  let boolMap : BoolVar → Bool := fun _id => false
  newAssignment' assign args params ffMap boolMap


mutual
/- Evaluate a term to FF value -/
def evalTerm {c : ZKConfig} (gconf : GlobalConfig c)
  (assign : Assignment c) (t : FFTerm c) (ms : List (FFMacro c))
  : Except String (FF c) :=
  match t with
  | .val v => Except.ok v
  | .var v => Except.ok (assign.ff v)
  | .add a b =>
     match evalTerm gconf assign a ms with
      | Except.error e => Except.error e
      | Except.ok va =>
        match evalTerm gconf assign b ms with
        | Except.error e => Except.error e
        | Except.ok vb => Except.ok (va + vb)
  | .sub a b =>
      match evalTerm gconf assign a ms with
        | Except.error e => Except.error e
        | Except.ok va =>
          match evalTerm gconf assign b ms with
          | Except.error e => Except.error e
          | Except.ok vb => Except.ok (va - vb)
  | .mul a b =>
      match evalTerm gconf assign a ms with
        | Except.error e => Except.error e
        | Except.ok va =>
          match evalTerm gconf assign b ms with
          | Except.error e => Except.error e
          | Except.ok vb => Except.ok (va * vb)
  | .neg a => match evalTerm gconf assign a ms with
            | Except.error e => Except.error e
            | Except.ok va => Except.ok (-va)
  | .ite c t e =>
      match evalFormula gconf assign c ms with
      | Except.error e => Except.error e
      | Except.ok vc =>
        if vc then evalTerm gconf assign t ms else evalTerm gconf assign e ms

termination_by (ms.length, sizeOfTerm t)
decreasing_by
  all_goals
    apply Prod.Lex.right
    simp only [sizeOfTerm]
    grind


/- Evaluate a formula to a boolean value -/
def evalFormula {c : ZKConfig} (gconf : GlobalConfig c)
  (assign : Assignment c) (f : FFFormula c) (ms : List (FFMacro c))
  : Except String Bool :=
  match f with
  | .true     => Except.ok true
  | .false    => Except.ok false
  | .range t l u =>
      match evalTerm gconf assign t ms with
      | Except.error e => Except.error e
      | Except.ok v => Except.ok (evalLe l v == 1 && evalLe v u == 1)
  | .bool v   => Except.ok (assign.bool v)
  | .eq a b =>
      match evalTerm gconf assign a ms with
      | Except.error e => Except.error e
      | Except.ok va =>
        match evalTerm gconf assign b ms with
        | Except.error e => Except.error e
        | Except.ok vb => Except.ok (va == vb)
  | .and a b =>
      match evalFormula gconf assign a ms with
      | Except.error e => Except.error e
      | Except.ok va =>
        match evalFormula gconf assign b ms with
        | Except.error e => Except.error e
        | Except.ok vb => Except.ok (va && vb)
  | .or a b =>
      match evalFormula gconf assign a ms with
      | Except.error e => Except.error e
      | Except.ok va =>
        match evalFormula gconf assign b ms with
        | Except.error e => Except.error e
        | Except.ok vb => Except.ok (va || vb)
  | .not a =>
      match evalFormula gconf assign a ms with
      | Except.error e => Except.error e
      | Except.ok va => Except.ok (!va)
  | .ite c t e =>
      match evalFormula gconf assign c ms with
      | Except.error e => Except.error e
      | Except.ok vc =>
        if vc then evalFormula gconf assign t ms else evalFormula gconf assign e ms
  | .imply a b =>
      match evalFormula gconf assign a ms with
      | Except.error e => Except.error e
      | Except.ok va =>
        match evalFormula gconf assign b ms with
        | Except.error e => Except.error e
        | Except.ok vb => Except.ok (!va || vb)
  | .iff a b =>
      match evalFormula gconf assign a ms with
      | Except.error e => Except.error e
      | Except.ok va =>
        match evalFormula gconf assign b ms with
        | Except.error e => Except.error e
        | Except.ok vb => Except.ok (va == vb)
  | .call name args =>
     match _h_fetchm: fetchMacro gconf ms name with
     | Except.error e => Except.error e
     | Except.ok (m,ms') =>
          match newAssignment assign args m.params with
          | Except.error e => Except.error e
          | Except.ok newAssign => evalFormula gconf newAssign m.body ms'
  | .anno f _ => evalFormula gconf assign f ms

termination_by (ms.length, sizeOfFormula f)

decreasing_by
  any_goals
    apply Prod.Lex.right
    simp only [sizeOfFormula]
    grind
  · apply Prod.Lex.left
    apply fetchMacroLT gconf ms ms' name m _h_fetchm

end

/- Satisfiability of a formula:

   EXIST an assignment σ such that evalFormula return true
-/
def isSatFormula {c : ZKConfig} (gconf : GlobalConfig c) (f : FFFormula c)
    (ms : List (FFMacro c)) : Prop :=
  ∃ (σ : Assignment c), evalFormula gconf σ f ms = Except.ok true


/- Totality of a formula:

   For EVERY assignment σ, evalFormula does not error (returns some Bool).
-/
def isTotal {c : ZKConfig} (gconf : GlobalConfig c) (f : FFFormula c)
    (ms : List (FFMacro c)) : Prop :=
  ∀ (σ : Assignment c), ∃ (v : Bool), evalFormula gconf σ f ms = Except.ok v


/- Satisfiability of a system:

  EXIST an assignment σ such that the main formula is true?
-/
def isSatSys {c : ZKConfig} (gconf : GlobalConfig c)
    (sys : FFConstraintSystem c) : Except String Prop := do
  let (f,_) ← mainFormula gconf sys
  return isSatFormula gconf f sys.macros


end Corellzk2smt.FFConstraints.Satisfiability
