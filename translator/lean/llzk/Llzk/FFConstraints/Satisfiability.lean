import Llzk.Basic
import Llzk.FFConstraints.Basic

namespace Llzk.FFConstraints.Satisfiability


open Llzk.FFConstraints.Basic
open Llzk.Language.Core.Syntax.AST

/- An assignment maps variables to values. There are two types of
   variables, finite field variables and boolean variables, so we have
   two maps -/
structure Assignment (c : ZKConfig) where
  ff : ℕ → FF c
  bool : ℕ → Bool
  deriving Inhabited

/- Renaming of variables for macro calls -/
def newAssignment' {c : ZKConfig}
   (assign : Assignment c)
   (args : List (MacroCallParam c)) (params : List Var)
   (ffMap : ℕ → FF c)
   (boolMap : ℕ → Bool) : Except String (Assignment c) :=
  match params, args with
  | [], [] => Except.ok { ff := ffMap, bool := boolMap }
  -- parameter is a FFVar, argument is also a FFVar
  | (.inl p) :: params', (.var (.inl a)) :: args' =>
    let ffMap' : ℕ → FF c := fun id => if id == p.id then assign.ff a.id else ffMap id
    newAssignment' assign args' params' ffMap' boolMap
  -- parameter is a FFVar, argument is also a FF value
  | (.inl p) :: params', (.ff t) :: args' =>
    let ffMap' : ℕ → FF c := fun id => if id == p.id then t else ffMap id
    newAssignment' assign args' params' ffMap' boolMap
  -- parameter is a BoolVar, argument is also a BoolVar
  | (.inr p) :: params', (.var (.inr a)) :: args' =>
    let boolMap' : ℕ → Bool := fun id => if id == p.id then assign.bool a.id else boolMap id
    newAssignment' assign args' params' ffMap boolMap'
  -- parameter is a BoolVar, argument is also a Bool value
  | (.inr p) :: params', (.bool t) :: args' =>
    let boolMap' : ℕ → Bool := fun id => if id == p.id then t else boolMap id
    newAssignment' assign args' params' ffMap boolMap'
  -- any other combination is an error
  | _, _ => Except.error "Mismatched variable lists"

def newAssignment {c : ZKConfig}
   (assign : Assignment c)
   (args : List (MacroCallParam c)) (params : List Var) : Except String (Assignment c) :=
  let ffMap : ℕ → FF c := fun _id => 0
  let boolMap : ℕ → Bool := fun _id => false
  newAssignment' assign args params ffMap boolMap

/- Evaluate a term to FF value -/
def evalTerm {c : ZKConfig} (assign : Assignment c) (t : FFTerm c) : FF c :=
  match t with
  | .const v => v
  | .var v => assign.ff v.id
  | .add a b => (evalTerm assign a) + (evalTerm assign b)
  | .sub a b => (evalTerm assign a) - (evalTerm assign b)
  | .mul a b => (evalTerm assign a) * (evalTerm assign b)
  | .neg a => -(evalTerm assign a)

/- Evaluate a formula to a boolean value -/
def evalFormula {c : ZKConfig}
   (assign : Assignment c) (f : FFFormula c) (ms : List (FFMacro c)) : Except String Bool := do
  match f with
  | .true     => return true
  | .false    => return false
  | .bool v   => return assign.bool v.id
  | .eq a b => return evalTerm assign a == evalTerm assign b
  | .and a b  => return (← evalFormula assign a ms) && (← evalFormula assign b ms)
  | .or a b   => return (← evalFormula assign a ms) || (← evalFormula assign b ms)
  | .not a    => return !(← evalFormula assign a ms)
  | .ite c t e => if (← evalFormula assign c ms) then evalFormula assign t ms
                  else evalFormula assign e ms
  | .imply a b => return !(← evalFormula assign a ms) || (← evalFormula assign b ms)
  | .iff a b   => return (← evalFormula assign a ms) == (← evalFormula assign b ms)
  | .call name args =>
     match _h_fetchm: fetchMacro ms name with
     | Except.error e => Except.error e
     | Except.ok (m,ms') =>
       let newAssign ← newAssignment assign args m.params
       evalFormula newAssign m.body ms'
termination_by (ms.length, sizeOfFormula f)
decreasing_by
  any_goals
    apply Prod.Lex.right
    simp only [sizeOfFormula]
    grind
  -- the call to a macro
  apply Prod.Lex.left
  apply fetchMacroLT ms ms' name m _h_fetchm


/- Satisfiability of a formula:

   EXIST an assignment σ such that evalFormula return true
-/
def isSatFormula {c : ZKConfig} (f : FFFormula c) (ms : List (FFMacro c)) : Prop :=
  ∃ (σ : Assignment c), evalFormula σ f ms = Except.ok true


/- Satisfiability of a system:

  EXIST an assignment σ such that the main formula is true?
-/
def isSatSys {c : ZKConfig} (sys : FFConstraintSystem c) : Except String Prop := do
  let (f,_) ← mainFormula sys
  return isSatFormula f sys.macros


end Llzk.FFConstraints.Satisfiability
