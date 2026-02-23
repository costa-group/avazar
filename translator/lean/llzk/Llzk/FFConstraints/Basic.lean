import Llzk.Basic
import Llzk.Language.Core.Syntax.AST

/- This module defines the syntax of constraint systems over finite fields
   and boolean variables -/

namespace Llzk.FFConstraints.Basic

open Llzk.Language.Core.Syntax.AST

/- Metadata for FF variables -/
structure FFVarMetaData where
  orig_name : String
  src_info : SrcInfo
  deriving Repr, BEq, Inhabited

structure BoolVarMetaData where
  orig_name : String
  src_info : SrcInfo
  deriving Repr, BEq, Inhabited

/- A finite field variable -/
structure FFVar where
  id : ℕ
  meta_data: FFVarMetaData
  deriving Repr, Inhabited

/- A boolean variable -/
structure BoolVar where
  id : ℕ
  meta_data: BoolVarMetaData
  deriving Repr, Inhabited

/- A variable, which can be either a finite field variable or a boolean variable -/
abbrev Var := FFVar ⊕ BoolVar

/-  Equality (BEq) of FFVar -/
instance : BEq FFVar where
  beq a b := a.id == b.id && a.meta_data.orig_name == b.meta_data.orig_name

/-  Equality (BEq) of BoolVar -/
instance : BEq BoolVar where
  beq a b := a.id == b.id && a.meta_data.orig_name == b.meta_data.orig_name

/-  Hashing (Hashable) of FFVar. Needed if we use this in a HashMap or HashSet -/
instance : Hashable FFVar where
  hash a := mixHash (hash a.id) (hash a.meta_data.orig_name)

/-  Hashing (Hashable) of BoolVar. Needed if we use this in a HashMap or HashSet -/
instance : Hashable BoolVar where
  hash a := mixHash (hash a.id) (hash a.meta_data.orig_name)

/-  Ordering (Ord) of FFVar. Needed if we use ordered sets -/
instance : Ord FFVar where
  compare a b :=
    match compare a.meta_data.orig_name b.meta_data.orig_name with
    | .eq => compare a.id b.id -- Names equal? Check IDs
    | ord => ord               -- Names different? Return that order

/-  Ordering (Ord) of BoolVar. Needed if we use ordered sets -/
instance : Ord BoolVar where
  compare a b :=
    match compare a.meta_data.orig_name b.meta_data.orig_name with
    | .eq => compare a.id b.id -- Names equal? Check IDs
    | ord => ord               -- Names different? Return that order


/- Term is a polynomial expression over finite fields -/
inductive FFTerm (c : ZKConfig) where
  | const : FF c →  FFTerm c
  | var   : FFVar → FFTerm c
  | add   : FFTerm c → FFTerm c → FFTerm c
  | sub   : FFTerm c → FFTerm c → FFTerm c
  | mul   : FFTerm c → FFTerm c → FFTerm c
  deriving Repr, BEq, Inhabited

/- A formula is a boolean formula with P(x)=0 as atoms.  -/
inductive FFFormula (c : ZKConfig) where
  | true   : FFFormula c
  | false  : FFFormula c
  | bool   : BoolVar → FFFormula c        -- A boolean variable
  | eqZero : FFTerm c → FFFormula c       -- P(x) = 0
  | and    : FFFormula c → FFFormula c → FFFormula c -- and
  | or     : FFFormula c → FFFormula c → FFFormula c -- or
  | not    : FFFormula c → FFFormula c -- negation
  | ite    : FFFormula c → FFFormula c → FFFormula c → FFFormula c  -- if-then-else
  | imply  : FFFormula c → FFFormula c → FFFormula c  -- implication
  | iff    : FFFormula c → FFFormula c → FFFormula c  -- if and only if
  | call   : String → List Var → FFFormula c  -- macro call
  deriving Repr, BEq, Inhabited

/- Trivial definition for size of formula, to be used for proving termination.
   Tried to use the default sizeOf but failed to unfold at some point.
   Revisit this later. -/
def sizeOfFormula {c : ZKConfig} : FFFormula c → Nat
  | .true | .false => 1
  | .bool _ => 1
  | .eqZero _ => 1
  | .and a b | .or a b | .imply a b | .iff a b => 1 + sizeOfFormula a + sizeOfFormula b
  | .not a => 1 + sizeOfFormula a
  | .ite c t e => 1 + sizeOfFormula c + sizeOfFormula t + sizeOfFormula e
  | .call _ _ => 1

/- A macro is a named formula with parameters -/
structure FFMacro (c : ZKConfig) where
  name : String
  params : List Var
  body : FFFormula c
  deriving Repr, BEq, Inhabited

/- A constraint system consists of a list of macros and the name of the main macro -/
structure FFConstraintSystem (c : ZKConfig) where
  macros : List (FFMacro c)
  main : String
  deriving Repr, BEq, Inhabited

/-- Fetch a macro by name from a list of macros. Throws an error if
    the macro is not found. -/
def fetchMacro {c : ZKConfig}
    (ms : List (FFMacro c)) (name : String) : Except String (FFMacro c × List (FFMacro c)) :=
  match ms with
  | [] => Except.error s!"Macro {name} not found"
  | m :: rest =>
      if m.name == name then Except.ok (m, rest)
      else fetchMacro rest name

/- fetchMacro returns a smaller list of macros -/
theorem fetchMacroLT {c : ZKConfig} (ms ms' : List (FFMacro c)) (name : String) (m : FFMacro c) :
  fetchMacro ms name = Except.ok (m, ms') → ms'.length < ms.length := by
  cases ms with
  | nil => simp [fetchMacro]
  | cons head tail =>
      simp only [fetchMacro]
      by_cases h : head.name = name
      · simp only [h, BEq.rfl, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq, List.length_cons,
        Order.lt_add_one_iff, and_imp] at *
        intro h1 h2
        rw [h2]
      · simp only [h, not_false_eq_true, beq_iff_eq, ↓reduceIte, List.length_cons,
        Order.lt_add_one_iff] at *
        intro h1
        have h2 := fetchMacroLT tail ms' name m h1
        grind

/- The main formula of a constraint system is a call to the main macro -/
def mainFormula {c : ZKConfig}
  (sys : FFConstraintSystem c) : Except String (FFFormula c × List Var) := do
  let (m,_) ← fetchMacro sys.macros sys.main
  return (FFFormula.call m.name m.params, m.params)

end Llzk.FFConstraints.Basic
