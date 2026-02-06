import Llzk.Basic
import Llzk.Language.Core.Syntax

/- This module provides a syntax for SMT formulas over finite fields, their satisfiability,
   and functions to print them in SMT-LIB2 format.
-/
namespace Llzk.SymEx.FFConstraints

open Llzk.Language.Core

/- Metadata for FF variables -/
structure FFVarMetaData where
  orig_name : String
  cmd_meta_data : CmdMetaData
  deriving Repr, BEq, Inhabited

/- A variable in the finite field constraint system -/
structure FFVar where
  id : ℕ
  meta_data: FFVarMetaData
  deriving Repr, Inhabited

/-  Equality (BEq) of FFVar -/
instance : BEq FFVar where
  beq a b := a.id == b.id && a.meta_data.orig_name == b.meta_data.orig_name

/-  Hashing (Hashable) of FFVar. Needed if we use this in a HashMap or HashSet -/
instance : Hashable FFVar where
  hash a := mixHash (hash a.id) (hash a.meta_data.orig_name)

/-  Ordering (Ord) of FFVar. Needed if we use ordered sets -/
instance : Ord FFVar where
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
  | eqZero : FFTerm c → FFFormula c       -- P(x) = 0
  | and    : FFFormula c → FFFormula c → FFFormula c
  | or     : FFFormula c → FFFormula c → FFFormula c
  | not    : FFFormula c → FFFormula c
  | true   : FFFormula c
  | false  : FFFormula c
  deriving Repr, BEq, Inhabited

/- An assignment maps variables to FF values -/
abbrev Assignment (c : ZKConfig) := ℕ → FF c


/- Evaluate Terms to FF values -/
def eval_term {c : ZKConfig} (assign : Assignment c) (t : FFTerm c) : FF c :=
  match t with
  | .const v => v
  | .var v => assign v.id
  | .add a b => (eval_term assign a) + (eval_term assign b)
  | .sub a b => (eval_term assign a) - (eval_term assign b)
  | .mul a b => (eval_term assign a) * (eval_term assign b)

/- Evaluate Formulas to Propositions (Prop) -/
def eval_formula {c : ZKConfig} (assign : Assignment c) (f : FFFormula c) : Prop :=
  match f with
  | .eqZero t => eval_term assign t = 0
  | .and a b  => (eval_formula assign a) ∧ (eval_formula assign b)
  | .or a b   => (eval_formula assign a) ∨ (eval_formula assign b)
  | .not a    => ¬(eval_formula assign a)
  | .true     => True
  | .false    => False

/- Satisfiability: does there EXIST an assignment σ such that evalFormula is true? -/
def is_sat {c : ZKConfig} (f : FFFormula c) : Prop :=
  ∃ (σ : Assignment c), eval_formula σ f



/- The next functions are used to collect all variables that are used in a formula.
   Note that variables with the same id and name, but with different metadata are
   considered equal. This should not happen in practice
-/

abbrev FFVarSet := Std.TreeSet FFVar compare
abbrev emptyFFVarSet : FFVarSet := Std.TreeSet.empty


/- Collect variables from a Term into the accumulator set -/
partial def collect_vars_term {c : ZKConfig} (acc : FFVarSet) (t : FFTerm c) : FFVarSet :=
  match t with
  | .const _   => acc
  | .var v     => acc.insert v
  | .add a b   =>
      let acc' := collect_vars_term acc a
      collect_vars_term acc' b
  | .sub a b   =>
      let acc' := collect_vars_term acc a
      collect_vars_term acc' b
  | .mul a b   =>
      let acc' := collect_vars_term acc a
      collect_vars_term acc' b

/- Collect variables from a Formula into the accumulator set -/
partial def collect_vars_formula {c : ZKConfig} (acc : FFVarSet) (f : FFFormula c) : FFVarSet :=
  match f with
  | .eqZero t => collect_vars_term acc t
  | .and a b  =>
      let acc' := collect_vars_formula acc a
      collect_vars_formula acc' b
  | .or a b   =>
      let acc' := collect_vars_formula acc a
      collect_vars_formula acc' b
  | .not a    => collect_vars_formula acc a
  | .true     => acc
  | .false    => acc

/- Returns a list of all unique variables in the formula -/
def collect_vars {c : ZKConfig} (f : FFFormula c) : List FFVar :=
  let emptySet : FFVarSet := emptyFFVarSet
  let finalSet := collect_vars_formula emptySet f
  -- Convert the set back to a List for your SMT printer
  finalSet.toList

/- Printing formulas in SMT2 format

   It follows the SMT-LIB2 format for finite fields as described in:
   https://arxiv.org/abs/2407.21169
-/

/- Generates spaces for indentation -/
def get_indent (level : Nat) : String :=
  String.ofList (List.replicate (level * 2) ' ')

/- Generates a unique string identifier for a variable based on its original name and ID -/
def var_id (v : FFVar) : String :=
  s!"{v.meta_data.orig_name}_{v.id}_L{v.meta_data.cmd_meta_data.src_info.line}"

/-- Customizable variable printer (e.g., "v_0", "v_1") -/
def print_var (stream : IO.FS.Stream) (v : FFVar) : IO Unit := do
--  stream.putStr s!"v_{v.id}"
  stream.putStr s!"{var_id v}"

/-- Prints a term as an S-expression: (+ a b) -/
partial def print_term {c : ZKConfig}
  (stream : IO.FS.Stream) (t : FFTerm c) : IO Unit := do
  match t with
  | .const val =>
      stream.putStr s!"{val.val}"
  | .var v =>
      print_var stream v
  | .add a b =>
      stream.putStr "(ff.add "
      print_term stream a
      stream.putStr " "
      print_term stream b
      stream.putStr ")"
  | .sub a b =>
      stream.putStr "(ff.sub "
      print_term stream a
      stream.putStr " "
      print_term stream b
      stream.putStr ")"
  | .mul a b =>
      stream.putStr "(ff.mul "
      print_term stream a
      stream.putStr " "
      print_term stream b
      stream.putStr ")"

/- Prints the boolean formula structure -/
partial def print_formula_body {c : ZKConfig}
  (stream : IO.FS.Stream) (f : FFFormula c) (level : Nat) : IO Unit := do
  let sp := get_indent level
  match f with
  | .eqZero t =>
      stream.putStr s!"{sp}(= "
      print_term stream t
      stream.putStrLn " 0)"
  | .and a b =>
      stream.putStrLn s!"{sp}(and "
      print_formula_body stream a (level + 1)
      print_formula_body stream b (level + 1)
      stream.putStrLn s!"{sp})"
  | .or a b =>
      stream.putStrLn s!"{sp}(or "
      print_formula_body stream a (level + 1)
      print_formula_body stream b (level + 1)
      stream.putStrLn s!"{sp})"
  | .not a =>
      stream.putStrLn s!"{sp}(not "
      print_formula_body stream a (level + 1)
      stream.putStrLn s!"{sp})"
  | .true  => stream.putStrLn s!"{sp}true"
  | .false => stream.putStrLn s!"{sp}false"

/- Prints the full SMT2 representation of the formula, including variable declarations
   and the assertion. Note that it receives the list of variables to declare as input,
   which can be obtained using `collect_vars`.
-/
def print_smt2 {c : ZKConfig}
    (vars : List FFVar)
    (f : FFFormula c)
    (stream : IO.FS.Stream) : IO Unit := do
  -- Header
  stream.putStrLn "(set-logic QF_FF)"
  stream.putStrLn ""
  -- The Finite Field sort declaration
  stream.putStrLn s!"(define-sort FFp () (_ FiniteField {c.p}))"
  -- Variable Declarations
  for v in vars do
    stream.putStr "(declare-const "
    print_var stream v
    stream.putStrLn " FFp)"
  -- Assertion
  stream.putStrLn "(assert "
  print_formula_body stream f 1
  stream.putStrLn ")"
  stream.flush


end Llzk.SymEx.FFConstraints
