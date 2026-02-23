import Llzk.Basic
import Llzk.Language.Core.Syntax.AST
import Llzk.FFConstraints.Basic

/- Printing a constraints system in SMT2 format

   For the finite field part, it follows the SMT-LIB2 format
   described in: https://arxiv.org/abs/2407.21169
-/

namespace Llzk.FFConstraints.SMT

open Llzk.Language.Core.Syntax.AST
open Llzk.FFConstraints.Basic


/- Generates spaces for indentation -/
def getIndent (level : Nat) : String :=
  String.ofList (List.replicate (level * 2) ' ')

/- Generates a unique string identifier for a variable based on its original name and ID -/
def ffVarID (v : FFVar) : String :=
  s!"{v.meta_data.orig_name}_{v.id}_L{v.meta_data.src_info.row}_C{v.meta_data.src_info.col}"

/- Generates a unique string identifier for a variable based on its original name and ID -/
def boolVarID (v : BoolVar) : String :=
  s!"{v.meta_data.orig_name}_{v.id}_L{v.meta_data.src_info.row}_C{v.meta_data.src_info.col}"

/-- Customizable variable printer (e.g., "v_0", "v_1") -/
def printVarFF (stream : IO.FS.Stream) (v : FFVar) : IO Unit := do
--  stream.putStr s!"v_{v.id}"
  stream.putStr s!"{ffVarID v}"

/-- Customizable variable printer (e.g., "v_0", "v_1") -/
def printVarBool (stream : IO.FS.Stream) (v : BoolVar) : IO Unit := do
--  stream.putStr s!"v_{v.id}"
  stream.putStr s!"{boolVarID v}"

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
      stream.putStr s!"{sp}{boolVarID v}"
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
        | .inl ffVar => ffVarID ffVar
        | .inr boolVar => boolVarID boolVar
      )
      stream.putStr (String.intercalate " " argStrs)
      stream.putStrLn ")"


def printMacro {c : ZKConfig}
  (stream : IO.FS.Stream) (m : FFMacro c) : IO Unit := do
  stream.putStr s!"(define-fun {m.name} ("
  let paramStrs := m.params.map (fun var =>
    match var with
    | .inl ffVar => s!"({ffVarID ffVar} FFp)"
    | .inr boolVar => s!"({boolVarID boolVar} Bool)"
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
  match mainFormula sys with
  | Except.error e => stream.putStrLn s!"Error: {e}"
  | Except.ok (f, vars) =>
  stream.putStrLn "(set-logic QF_FF)"
  stream.putStrLn ""
  -- The Finite Field sort declaration
  stream.putStrLn s!"(define-sort FFp () (_ FiniteField {c.p}))"
  -- Variable Declarations
  for v in vars do
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
  stream.putStrLn "(assert "
  printFormula stream f 1
  stream.putStrLn ")"
  stream.flush


end Llzk.FFConstraints.SMT
