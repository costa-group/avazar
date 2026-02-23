import Llzk.Basic
import Llzk.Language.Core.Syntax.AST

/- This module provides a syntax for SMT formulas over finite fields, their satisfiability,
   and functions to print them in SMT-LIB2 format.
-/
namespace Llzk.SymEx.FFConstraints

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

/- A variable in the finite field constraint system -/
structure FFVar where
  id : ℕ
  meta_data: FFVarMetaData
  deriving Repr, Inhabited

structure BoolVar where
  id : ℕ
  meta_data: BoolVarMetaData
  deriving Repr, Inhabited


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

abbrev Var := FFVar ⊕ BoolVar

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

/- Trivial definition for size of formula, to be used for proving termination -/
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

/- A constraint system consists of a list of macros and a main formula -/
structure FFConstraintSystem (c : ZKConfig) where
  macros : List (FFMacro c)
  main : String
  deriving Repr, BEq, Inhabited


/-- Fetch a macro by name from a constraint system. Throws an error if the macro is not found. -/
def fetchMacro {c : ZKConfig}
    (ms : List (FFMacro c)) (name : String) : Except String (FFMacro c × List (FFMacro c)) :=
  match ms with
  | [] => Except.error s!"Macro {name} not found"
  | m :: rest =>
      if m.name == name then Except.ok (m, rest)
      else fetchMacro rest name

/- fetchMacro returns a smaller list -/
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


/- An assignment maps variables to FF values -/
structure Assignment (c : ZKConfig) where
  ff : ℕ → FF c
  bool : ℕ → Bool
  deriving Inhabited

/- Renaming of variables for macro calls -/
def newAssignment' {c : ZKConfig}
   (assign : Assignment c)
   (orginNames newNames : List Var)
   (ffMap : ℕ → FF c)
   (boolMap : ℕ → Bool) : Except String (Assignment c) :=
  match orginNames, newNames with
  | [], [] => Except.ok { ff := ffMap, bool := boolMap }
  | (.inl org) :: orgs, (.inl new) :: news =>
    let ffMap' : ℕ → FF c := fun id => if id == new.id then assign.ff org.id else ffMap id
    newAssignment' assign orgs news ffMap' boolMap
  | (.inr org) :: orgs, (.inr new) :: news =>
    let boolMap' : ℕ → Bool := fun id => if id == new.id then assign.bool org.id else boolMap id
    newAssignment' assign orgs news ffMap boolMap'
  -- This case should not happen if the input lists are well-formed. Later will throw an exception.
  | _, _ => Except.error "Mismatched variable lists"

def newAssignment {c : ZKConfig}
   (assign : Assignment c)
   (orginNames newNames : List Var) : Except String (Assignment c) :=
  let ffMap : ℕ → FF c := fun _id => 0
  let boolMap : ℕ → Bool := fun _id => false
  newAssignment' assign orginNames newNames ffMap boolMap

/- Evaluate Terms to FF values -/
def eval_term {c : ZKConfig} (assign : Assignment c) (t : FFTerm c) : FF c :=
  match t with
  | .const v => v
  | .var v => assign.ff v.id
  | .add a b => (eval_term assign a) + (eval_term assign b)
  | .sub a b => (eval_term assign a) - (eval_term assign b)
  | .mul a b => (eval_term assign a) * (eval_term assign b)

/- Evaluate Formulas to Propositions (Prop) -/
def eval_formula {c : ZKConfig}
   (assign : Assignment c) (f : FFFormula c) (ms : List (FFMacro c)) : Except String Bool := do
  match f with
  | .true     => return true
  | .false    => return false
  | .bool v   => return assign.bool v.id
  | .eqZero t => return eval_term assign t = 0
  | .and a b  => return (← eval_formula assign a ms) && (← eval_formula assign b ms)
  | .or a b   => return (← eval_formula assign a ms) || (← eval_formula assign b ms)
  | .not a    => return !(← eval_formula assign a ms)
  | .ite c t e => if (← eval_formula assign c ms) then eval_formula assign t ms
                  else eval_formula assign e ms
  | .imply a b => return !(← eval_formula assign a ms) || (← eval_formula assign b ms)
  | .iff a b   => return (← eval_formula assign a ms) == (← eval_formula assign b ms)
  | .call name args =>
     match _h_fetchm: fetchMacro ms name with
     | Except.error e => Except.error e
     | Except.ok (m,ms') =>
       let newAssign ← newAssignment assign args m.params
       eval_formula newAssign m.body ms'
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

   Does there EXIST an assignment σ such that evalFormula is true?
-/
def is_sat_formula {c : ZKConfig} (f : FFFormula c) (ms : List (FFMacro c)) : Prop :=
  ∃ (σ : Assignment c), eval_formula σ f ms = Except.ok true


/- Satisfiability of a system:

   Does there EXIST an assignment σ such that the main formula is true?
-/
def is_sat_sys {c : ZKConfig} (sys : FFConstraintSystem c) : Except String Prop := do
  let (m,ms') ← fetchMacro sys.macros sys.main
  let p := is_sat_formula m.body ms'
  return p

/- The next functions are used to collect all variables that are used in a formula.
   Note that variables with the same id and name, but with different metadata are
   considered equal. This should not happen in practice
-/

abbrev FFVarSet := Std.TreeSet FFVar compare
abbrev emptyFFVarSet : FFVarSet := Std.TreeSet.empty

abbrev BoolVarSet := Std.TreeSet BoolVar compare
abbrev emptyBoolVarSet : BoolVarSet := Std.TreeSet.empty

/- Collect variables from a Term into the accumulator set -/
partial def collectVarsTerm {c : ZKConfig} (acc : FFVarSet) (t : FFTerm c) : FFVarSet :=
  match t with
  | .const _   => acc
  | .var v     => acc.insert v
  | .add a b   =>
      let acc' := collectVarsTerm acc a
      collectVarsTerm acc' b
  | .sub a b   =>
      let acc' := collectVarsTerm acc a
      collectVarsTerm acc' b
  | .mul a b   =>
      let acc' := collectVarsTerm acc a
      collectVarsTerm acc' b

/- Collect variables from a Formula into the accumulator set -/
partial def collectVarsFormula {c : ZKConfig}
  (acc : FFVarSet × BoolVarSet) (f : FFFormula c) : FFVarSet × BoolVarSet :=
  match f with
  | .true     => acc
  | .false    => acc
  | .eqZero t => (collectVarsTerm acc.1 t, acc.2)
  | .bool v   => (acc.1, acc.2.insert v)
  | .and a b  =>
      let acc' := collectVarsFormula acc a
      collectVarsFormula acc' b
  | .or a b   =>
      let acc' := collectVarsFormula acc a
      collectVarsFormula acc' b
  | .not a    => collectVarsFormula acc a
  | .ite c t e =>
      let acc' := collectVarsFormula acc c
      let acc'' := collectVarsFormula acc' t
      collectVarsFormula acc'' e
  | .imply a b =>
      let acc' := collectVarsFormula acc a
      collectVarsFormula acc' b
  | .iff a b   =>
      let acc' := collectVarsFormula acc a
      collectVarsFormula acc' b
  | .call _ args =>
      args.foldl (fun acc var =>
        match var with
        | .inl ffVar => (acc.1.insert ffVar, acc.2)
        | .inr boolVar => (acc.1, acc.2.insert boolVar)
      ) acc

/- Returns a list of all unique variables in the formula -/
def collectVars {c : ZKConfig} (f : FFFormula c) : List FFVar × List BoolVar :=
  let emptyFFSet : FFVarSet := emptyFFVarSet
  let emptyBoolSet : BoolVarSet := emptyBoolVarSet
  let finalSet := collectVarsFormula (emptyFFSet, emptyBoolSet) f
  -- Convert the set back to a List for your SMT printer
  (finalSet.1.toList, finalSet.2.toList)

/- Printing formulas in SMT2 format

   It follows the SMT-LIB2 format for finite fields as described in:
   https://arxiv.org/abs/2407.21169
-/

/- Generates spaces for indentation -/
def getIndent (level : Nat) : String :=
  String.ofList (List.replicate (level * 2) ' ')

/- Generates a unique string identifier for a variable based on its original name and ID -/
def varIDFF (v : FFVar) : String :=
  s!"{v.meta_data.orig_name}_{v.id}_L{v.meta_data.src_info.row}_C{v.meta_data.src_info.col}"

/- Generates a unique string identifier for a variable based on its original name and ID -/
def varIDBool (v : BoolVar) : String :=
  s!"{v.meta_data.orig_name}_{v.id}_L{v.meta_data.src_info.row}_C{v.meta_data.src_info.col}"

/-- Customizable variable printer (e.g., "v_0", "v_1") -/
def printVarFF (stream : IO.FS.Stream) (v : FFVar) : IO Unit := do
--  stream.putStr s!"v_{v.id}"
  stream.putStr s!"{varIDFF v}"

/-- Customizable variable printer (e.g., "v_0", "v_1") -/
def printVarBool (stream : IO.FS.Stream) (v : BoolVar) : IO Unit := do
--  stream.putStr s!"v_{v.id}"
  stream.putStr s!"{varIDBool v}"

/-- Prints a term as an S-expression: (+ a b) -/
def printTerm {c : ZKConfig}
  (stream : IO.FS.Stream) (t : FFTerm c) : IO Unit := do
  match t with
  | .const val =>
      stream.putStr s!"{val.val}"
  | .var v =>
      printVarFF stream v
  | .add a b =>
      stream.putStr "(ff.add "
      printTerm stream a
      stream.putStr " "
      printTerm stream b
      stream.putStr ")"
  | .sub a b =>
      stream.putStr "(ff.sub "
      printTerm stream a
      stream.putStr " "
      printTerm stream b
      stream.putStr ")"
  | .mul a b =>
      stream.putStr "(ff.mul "
      printTerm stream a
      stream.putStr " "
      printTerm stream b
      stream.putStr ")"

/- Prints the boolean formula structure -/
def printFormula {c : ZKConfig}
  (stream : IO.FS.Stream) (f : FFFormula c) (level : Nat) : IO Unit := do
  let sp := getIndent level
  match f with
  | .true  => stream.putStrLn s!"{sp}true"
  | .false => stream.putStrLn s!"{sp}false"
  | .bool v =>
      stream.putStr s!"{sp}{varIDBool v}"
  | .eqZero t =>
      stream.putStr s!"{sp}(= "
      printTerm stream t
      stream.putStrLn " 0)"
  | .and a b =>
      stream.putStrLn s!"{sp}(and "
      printFormula stream a (level + 1)
      printFormula stream b (level + 1)
      stream.putStrLn s!"{sp})"
  | .or a b =>
      stream.putStrLn s!"{sp}(or "
      printFormula stream a (level + 1)
      printFormula stream b (level + 1)
      stream.putStrLn s!"{sp})"
  | .ite c t e =>
      stream.putStrLn s!"{sp}(ite "
      printFormula stream c (level + 1)
      printFormula stream t (level + 1)
      printFormula stream e (level + 1)
      stream.putStrLn s!"{sp})"
  | .imply a b =>
      stream.putStrLn s!"{sp}(=>"
      printFormula stream a (level + 1)
      printFormula stream b (level + 1)
      stream.putStrLn s!"{sp})"
  | .iff a b =>
      stream.putStrLn s!"{sp}(= "
      printFormula stream a (level + 1)
      printFormula stream b (level + 1)
      stream.putStrLn s!"{sp})"
  | .not a =>
      stream.putStrLn s!"{sp}(not "
      printFormula stream a (level + 1)
      stream.putStrLn s!"{sp})"
  | .call name args =>
      stream.putStr s!"{sp}({name} "
      let argStrs := args.map (fun var =>
        match var with
        | .inl ffVar => varIDFF ffVar
        | .inr boolVar => varIDBool boolVar
      )
      stream.putStr (String.intercalate " " argStrs)
      stream.putStrLn ")"


def printMacro {c : ZKConfig}
  (stream : IO.FS.Stream) (m : FFMacro c) : IO Unit := do
  stream.putStr s!"(define-fun {m.name} ("
  let paramStrs := m.params.map (fun var =>
    match var with
    | .inl ffVar => s!"({varIDFF ffVar} FFp)"
    | .inr boolVar => s!"({varIDBool boolVar} Bool)"
  )
  stream.putStr (String.intercalate " " paramStrs)
  stream.putStrLn ") Bool"
  printFormula stream m.body 1

def printMacros {c : ZKConfig}
  (stream : IO.FS.Stream) (ms : List (FFMacro c)) : IO Unit := do
  match ms with
  | [] => return ()
  | m :: rest =>
      printMacro stream m
      stream.putStrLn ""
      stream.putStrLn ""
      printMacros stream rest

def printConstraintSystem {c : ZKConfig}
  (stream : IO.FS.Stream) (sys : FFConstraintSystem c) : IO Unit := do
  match fetchMacro sys.macros sys.main with
  | Except.error e => stream.putStrLn s!"Error: {e}"
  | Except.ok (m, _) =>
  stream.putStrLn "(set-logic QF_FF)"
  stream.putStrLn ""
  -- The Finite Field sort declaration
  stream.putStrLn s!"(define-sort FFp () (_ FiniteField {c.p}))"
  -- Variable Declarations
  for v in m.params do
    stream.putStr "(declare-const "
    match v with
    | .inl ffVar =>
        printVarFF stream ffVar
        stream.putStrLn " FFp)"
    | .inr boolVar =>
        printVarBool stream boolVar
        stream.putStrLn " Bool)"
  -- Macros
  printMacros stream sys.macros.reverse -- we assume main is first
  -- Main formula
  let f : FFFormula c := FFFormula.call m.name m.params
  stream.putStrLn "(assert "
  printFormula stream f 1
  stream.putStrLn ")"
  stream.flush


end Llzk.SymEx.FFConstraints
