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
  s!"{v}"

/- Generates a unique string identifier for a variable based on its original name and ID -/
def boolVarID (v : BoolVar) : String :=
  s!"{v}"

/-- Customizable variable printer (e.g., "v_0", "v_1") -/
def printVarFF (stream : IO.FS.Stream) (v : FFVar) : IO Unit := do
--  stream.putStr s!"v_{v.id}"
  stream.putStr s!"{ffVarID v}"

/-- Customizable variable printer (e.g., "v_0", "v_1") -/
def printVarBool (stream : IO.FS.Stream) (v : BoolVar) : IO Unit := do
--  stream.putStr s!"v_{v.id}"
  stream.putStr s!"{boolVarID v}"

mutual
/-- Prints a term as an S-expression: (+ a b) -/
def printTerm {c : ZKConfig}
  (stream : IO.FS.Stream) (t : FFTerm c) : IO Unit := do
  match t with
  | .val val =>
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
  | .neg a =>
      stream.putStr "(ff.neg "
      printTerm stream a
      stream.putStr ")"
  | .ite c t e =>
      stream.putStr "(ite "
      printFormula stream c 0 false
      stream.putStr " "
      printTerm stream t
      stream.putStr " "
      printTerm stream e
      stream.putStr ")"

/- Prints the boolean formula structure -/
def printFormula {c : ZKConfig}
  (stream : IO.FS.Stream) (f : FFFormula c) (level : Nat) (indent: Bool): IO Unit := do
  let sp := if indent then getIndent level else " "
  let nl := if indent then "\n" else ""
  match f with
  | .true  => stream.putStr s!"{sp}true{nl}"
  | .false => stream.putStr s!"{sp}false{nl}"
  | .range t l u =>
      let int_of_l : Int := if l.val < c.midpoint then l.val else l.val - c.p
      let int_of_u : Int := if u.val < c.midpoint then u.val else u.val - c.p
      if (int_of_l >= 0 && int_of_u < 0 ) then
        panic s!"Error: range [{int_of_l}, {int_of_u}] crosses the midpoint of the field."
      else if (int_of_l <= 0 && int_of_u < 0) || (int_of_l >= 0 && int_of_u >= 0) then
        stream.putStr s!"{sp}(ff.range "
        printTerm stream t
        stream.putStr " "
        stream.putStr s!"{int_of_l}"
        stream.putStr " "
        stream.putStr s!"{int_of_u}"
        stream.putStr s!"){nl}"
  | .bool v =>
      stream.putStr s!"{sp}{boolVarID v}"
  | .eq a b =>
      stream.putStr s!"{sp}(= "
      printTerm stream a
      stream.putStr " "
      printTerm stream b
      stream.putStr s!"){nl}"
  | .lt a b =>
      stream.putStr s!"{sp}(ff.lt "
      printTerm stream a
      stream.putStr " "
      printTerm stream b
      stream.putStr s!"){nl}"
  | .gt a b =>
      stream.putStr s!"{sp}(ff.gt "
      printTerm stream a
      stream.putStr " "
      printTerm stream b
      stream.putStr s!"){nl}"
  | .le a b =>
      stream.putStr s!"{sp}(ff.le "
      printTerm stream a
      stream.putStr " "
      printTerm stream b
      stream.putStr s!"){nl}"
  | .ge a b =>
      stream.putStr s!"{sp}(ff.ge "
      printTerm stream a
      stream.putStr " "
      printTerm stream b
      stream.putStr s!"){nl}"
  | .and a b =>
      -- we remove trivial cases to simplify the output
      if a == (@FFFormula.true c) then
        printFormula stream b level indent
      else if b == (@FFFormula.true c) then
        printFormula stream a level indent
      else
        stream.putStr s!"{sp}(and {nl}"
        printFormula stream a (level + 1) indent
        printFormula stream b (level + 1) indent
        stream.putStr s!"{sp}){nl}"
  | .or a b =>
      -- we remove trivial cases to simplify the output
      if a == (@FFFormula.false c) then
        printFormula stream b level indent
      else if b == (@FFFormula.false c) then
        printFormula stream a level indent
      else
        stream.putStr s!"{sp}(or {nl}"
        printFormula stream a (level + 1) indent
        printFormula stream b (level + 1) indent
        stream.putStr s!"{sp}){nl}"
  | .ite c t e =>
      stream.putStr s!"{sp}(ite {nl}"
      printFormula stream c (level + 1) indent
      printFormula stream t (level + 1) indent
      printFormula stream e (level + 1) indent
      stream.putStr s!"{sp}){nl}"
  | .imply a b =>
      stream.putStr s!"{sp}(=> {nl}"
      printFormula stream a (level + 1) indent
      printFormula stream b (level + 1) indent
      stream.putStr s!"{sp}){nl}"
  | .iff a b =>
      stream.putStr s!"{sp}(= {nl}"
      printFormula stream a (level + 1) indent
      printFormula stream b (level + 1) indent
      stream.putStr s!"{sp}){nl}"
  | .not a =>
      stream.putStr s!"{sp}(not {nl}"
      printFormula stream a (level + 1) indent
      stream.putStr s!"{sp}){nl}"
  | .call name args =>
      stream.putStr s!"{sp}({name} "
      let argStrs := args.map (fun a =>
        match a with
        | .var (.inl ffVar) => ffVarID ffVar
        | .var (.inr boolVar) => boolVarID boolVar
        | .ff t => s!"{t.val}"
        | .bool b => s!"{b}"
      )
      stream.putStr (String.intercalate " " argStrs)
      stream.putStr s!"){nl}"

end

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
  printFormula stream m.body 1 true
  stream.putStrLn ")"

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
  stream.putStrLn s!"; (define-sort FFp () (_ FiniteField {c.p}))"
  --
  stream.putStrLn s!"(define-sort FFp () Int)"
  stream.putStrLn s!"(declare-fun ff.add (FFp FFp) FFp)"
  stream.putStrLn s!"(declare-fun ff.mul (FFp FFp) FFp)"
  stream.putStrLn s!"(declare-fun ff.sub (FFp FFp) FFp)"
  stream.putStrLn s!"(declare-fun ff.neg (FFp) FFp)"
  stream.putStrLn s!"(declare-fun ff.range (FFp FFp FFp) Bool)"
  stream.putStrLn s!"(declare-fun ff.lt (FFp FFp) Bool)"
  stream.putStrLn s!"(declare-fun ff.gt (FFp FFp) Bool)"
  stream.putStrLn s!"(declare-fun ff.le (FFp FFp) Bool)"
  stream.putStrLn s!"(declare-fun ff.ge (FFp FFp) Bool)"
  stream.putStrLn s!""
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
  stream.putStrLn ""
  -- Macros
  printMacros stream sys.macros.reverse -- we assume main is first
  -- Main formula
  stream.putStrLn "(assert "
  printFormula stream f 1 true
  stream.putStrLn ")"
  stream.flush

def printParam_asJSON
  (stream : IO.FS.Stream) (var : Var) : IO Unit := do
  match var with
  | .inl ffVar =>
      stream.putStr s!"\{ \"name\": \"{ffVarID ffVar}\", \"type\": \"ff\" }"
  | .inr boolVar =>
      stream.putStr s!"\{ \"name\": \"{boolVarID boolVar}\", \"type\": \"bool\" }"

def printParams_asJSON
  (stream : IO.FS.Stream) (params : List Var) : IO Unit := do
  match params with
  | [] => return ()
  | var :: rest =>
      printParam_asJSON stream var
      if rest != [] then
        stream.putStr ", "
      printParams_asJSON stream rest

def printVarInfo_asJSON {c : ZKConfig}
  (stream : IO.FS.Stream) (var : MacroVarInfo c) : IO Unit := do
  match var with
  | .ffVar ffVar => stream.putStr s!"\"{ffVarID ffVar}\""
  | .const val => stream.putStr s!"{val.val}"
  | .array arr =>
      stream.putStr "["
      let varStrs := arr.map (fun v =>
        match v with
        | .inl ffVar => s!"\"{ffVarID ffVar}\""
        | .inr val => s!"{val.val}"
      )
      stream.putStr (String.intercalate ", " varStrs)
      stream.putStr "]"

def printVarsInfo_asJSON {c : ZKConfig}
  (stream : IO.FS.Stream) (vs : MacroVarsInfo c) : IO Unit := do
  match vs with
  | [] => return ()
  | (id,v) :: rest =>
      stream.putStr s!"\"{id}\": "
      printVarInfo_asJSON stream v
      if rest != [] then
        stream.putStr ", "
      printVarsInfo_asJSON stream rest


def printMacro_asJSON {c : ZKConfig}
  (stream : IO.FS.Stream) (m : FFMacro c) : IO Unit := do
  stream.putStrLn s!"    \"{m.name}\": \{"
  stream.putStr "        \"params\": ["
  printParams_asJSON stream m.params
  stream.putStrLn "],"
  stream.putStr "        \"vars_info\": {"
  printVarsInfo_asJSON stream m.vars_info
  stream.putStrLn "},"
  stream.putStr "        \"formula\": \""
  printFormula stream m.body 0 false
  stream.putStrLn " \""
  stream.putStr "     }"


def printMacros_asJSON {c : ZKConfig}
  (stream : IO.FS.Stream) (ms : List (FFMacro c)) : IO Unit := do
  match ms with
  | [] => return ()
  | m :: rest =>
      printMacro_asJSON stream m
      if rest != [] then stream.putStrLn ","
      printMacros_asJSON stream rest

def printConstraintSystem_asJSON {c : ZKConfig}
  (stream : IO.FS.Stream) (sys : FFConstraintSystem c) : IO Unit := do
  match mainFormula sys with
  | Except.error e => stream.putStrLn s!"Error: {e}"
  | Except.ok (f, vars) =>
  stream.putStrLn "{"
  stream.putStrLn s!"  \"prime\": {c.p},"
  -- Macros
  stream.putStrLn s!"  \"macros\": \{"
  printMacros_asJSON stream sys.macros.reverse -- we assume main is first
  stream.putStrLn ""
  stream.putStrLn s!"  },"
  -- Main formula
  stream.putStrLn s!"  \"main\": \{"
  stream.putStr s!"    \"vars\": ["
  printParams_asJSON stream vars
  stream.putStrLn s!"],"
  stream.putStr s!"    \"formula\": \""
  printFormula stream f 0 false
  stream.putStr s!" \""
  stream.putStrLn " }"
  stream.putStrLn "}"
  stream.flush


end Llzk.FFConstraints.SMT
