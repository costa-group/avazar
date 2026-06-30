import Corellzk2smt.Basic
import Corellzk2smt.Config
--import Corellzk2smt.Language.Core.Syntax.AST
import Corellzk2smt.FFConstraints.Basic

/- Printing a constraints system in SMT2 format

   For the finite field part, it follows the SMT-LIB2 format
   described in: https://arxiv.org/abs/2407.21169
-/

namespace Llzk.FFConstraints.SMT

--open Corellzk2smt.Language.Core.Syntax.AST
open Corellzk2smt.FFConstraints.Basic


/- Generates spaces for indentation -/
def getIndent {c : ZKConfig} (_ : GlobalConfig c) (level : Nat) : String :=
  String.ofList (List.replicate (level * 2) ' ')

/- Generates a unique string identifier for a variable based on ID -/
def varID {c : ZKConfig} (_ : GlobalConfig c) (v : Var) : String :=
  match v with
  | .ffv v' => s!"{v'}"
  | .boolv v' => s!"{v'}"

def const_repr {c : ZKConfig} (_ : GlobalConfig c) (c : Const c) : String :=
  match c with
  | .ffc v => s!"{v.val}"
  | .boolc b => s!"{b}"

/- Customizable variable printer (e.g., "v_0", "v_1") -/
def printVar {c : ZKConfig} (gconf : GlobalConfig c) (stream : IO.FS.Stream)
    (v : Var) : IO Unit := do
--  stream.putStr s!"v_{v.id}"
  stream.putStr s!"v_{varID gconf v}"

mutual
/-- Prints a term as an S-expression: (+ a b) -/
def printTerm {c : ZKConfig} (gconf : GlobalConfig c)
  (stream : IO.FS.Stream) (t : FFTerm c) : IO Unit := do
  match t with
  | .val val =>
      stream.putStr s!"{val.val}"
  | .var v =>
      printVar gconf stream (Var.ffv v)
  | .add a b =>
      stream.putStr "(ff.add "
      printTerm gconf stream a
      stream.putStr " "
      printTerm gconf stream b
      stream.putStr ")"
  | .sub a b =>
      stream.putStr "(ff.sub "
      printTerm gconf stream a
      stream.putStr " "
      printTerm gconf stream b
      stream.putStr ")"
  | .mul a b =>
      stream.putStr "(ff.mul "
      printTerm gconf stream a
      stream.putStr " "
      printTerm gconf stream b
      stream.putStr ")"
  | .neg a =>
      stream.putStr "(ff.neg "
      printTerm gconf stream a
      stream.putStr ")"
  | .ite c t e =>
      stream.putStr "(ite "
      printFormula gconf stream c 0 false
      stream.putStr " "
      printTerm gconf stream t
      stream.putStr " "
      printTerm gconf stream e
      stream.putStr ")"

/- Prints the boolean formula structure -/
def printFormula {c : ZKConfig} (gconf : GlobalConfig c)
  (stream : IO.FS.Stream) (f : FFFormula c) (level : Nat) (indent: Bool): IO Unit := do
  let sp := if indent then getIndent gconf level else " "
  let nl := if indent then "\n" else ""
  match f with
  | .true  => stream.putStr s!"{sp}true{nl}"
  | .false => stream.putStr s!"{sp}false{nl}"
  | .range t l u =>
      stream.putStr s!"{sp}(ff.range "
      printTerm gconf stream t
      stream.putStr " "
      stream.putStr s!"{l.val}"
      stream.putStr " "
      stream.putStr s!"{u.val}"
      stream.putStr s!"){nl}"
  | .bool v =>
      stream.putStr s!"{sp}{varID gconf (Var.boolv v)}"
  | .eq a b =>
      stream.putStr s!"{sp}(= "
      printTerm gconf stream a
      stream.putStr " "
      printTerm gconf stream b
      stream.putStr s!"){nl}"
  /-
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
  -/
  | .and a b =>
      -- we remove trivial cases to simplify the output
      if a == (@FFFormula.true c) then
        printFormula gconf stream b level indent
      else if b == (@FFFormula.true c) then
        printFormula gconf stream a level indent
      else
        stream.putStr s!"{sp}(and {nl}"
        printFormula gconf stream a (level + 1) indent
        printFormula gconf stream b (level + 1) indent
        stream.putStr s!"{sp}){nl}"
  | .or a b =>
      -- we remove trivial cases to simplify the output
      if a == (@FFFormula.false c) then
        printFormula gconf stream b level indent
      else if b == (@FFFormula.false c) then
        printFormula gconf stream a level indent
      else
        stream.putStr s!"{sp}(or {nl}"
        printFormula gconf stream a (level + 1) indent
        printFormula gconf stream b (level + 1) indent
        stream.putStr s!"{sp}){nl}"
  | .ite c t e =>
      stream.putStr s!"{sp}(ite {nl}"
      printFormula gconf stream c (level + 1) indent
      printFormula gconf stream t (level + 1) indent
      printFormula gconf stream e (level + 1) indent
      stream.putStr s!"{sp}){nl}"
  | .imply a b =>
      stream.putStr s!"{sp}(=> {nl}"
      printFormula gconf stream a (level + 1) indent
      printFormula gconf stream b (level + 1) indent
      stream.putStr s!"{sp}){nl}"
  | .iff a b =>
      stream.putStr s!"{sp}(= {nl}"
      printFormula gconf stream a (level + 1) indent
      printFormula gconf stream b (level + 1) indent
      stream.putStr s!"{sp}){nl}"
  | .not a =>
      stream.putStr s!"{sp}(not {nl}"
      printFormula gconf stream a (level + 1) indent
      stream.putStr s!"{sp}){nl}"
  | .call name args =>
      stream.putStr s!"{sp}({name} "
      let argStrs := args.map (fun a =>
        match a with
        | .var v => varID gconf v
        | .const t => s!"{const_repr gconf t}"
      )
      stream.putStr (String.intercalate " " argStrs)
      stream.putStr s!"){nl}"

end

/- Prints one macro as a SMT defined function -/
def printMacro {c : ZKConfig} (gconf : GlobalConfig c)
  (stream : IO.FS.Stream) (m : FFMacro c) : IO Unit := do
  stream.putStr s!"(define-fun {m.name} ("
  let paramStrs := m.params.map (fun var =>
    match var with
    | .ffv _ => s!"({varID gconf var} FFp)"
    | .boolv _ => s!"({varID gconf var} Bool)"
  )
  stream.putStr (String.intercalate " " paramStrs)
  stream.putStrLn ") Bool"
  printFormula gconf stream m.body 1 true
  stream.putStrLn ")"

/- Prints all macros as SMT defined functions -/
def printMacros {c : ZKConfig} (gconf : GlobalConfig c)
  (stream : IO.FS.Stream) (ms : List (FFMacro c)) : IO Unit := do
  match ms with
  | [] => return ()
  | m :: rest =>
      printMacro gconf stream m
      stream.putStrLn ""
      stream.putStrLn ""
      printMacros gconf stream rest

/- Prints the entire constraint system as SMT formulas -/
def printConstraintSystem {c : ZKConfig} (gconf : GlobalConfig c)
  (stream : IO.FS.Stream) (sys : FFConstraintSystem c) : IO Unit := do
  match mainFormula gconf sys with
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
    | .ffv _ =>
        printVar gconf stream v
        stream.putStrLn " FFp)"
    | .boolv _ =>
        printVar gconf stream v
        stream.putStrLn " Bool)"
  stream.putStrLn ""
  -- Macros
  printMacros gconf stream sys.macros.reverse -- we assume main is first
  -- Main formula
  stream.putStrLn "(assert "
  printFormula gconf stream f 1 true
  stream.putStrLn ")"
  stream.flush

/- Prints a parameter as JSON (both name and type) -/
def printParam_asJSON {c : ZKConfig} (gconf : GlobalConfig c)
  (stream : IO.FS.Stream) (var : Var) : IO Unit := do
  match var with
  | .ffv _ =>
      stream.putStr s!"\{ \"name\": \"{varID gconf var}\", \"type\": \"ff\" }"
  | .boolv _ =>
      stream.putStr s!"\{ \"name\": \"{varID gconf var}\", \"type\": \"bool\" }"

/- Prints a list of parameters as JSON (both names and types) -/
def printParams_asJSON {c : ZKConfig} (gconf : GlobalConfig c)
  (stream : IO.FS.Stream) (params : List Var) : IO Unit := do
  match params with
  | [] => return ()
  | var :: rest =>
      printParam_asJSON gconf stream var
      if rest != [] then
        stream.putStr ", "
      printParams_asJSON gconf stream rest

/- Prints the macro exit variable information as JSON -/
def printVarInfo_asJSON {c : ZKConfig} (gconf : GlobalConfig c)
  (stream : IO.FS.Stream) (var : MacroExitVarInfo c) : IO Unit := do
  match var with
  | .ffVar ffVar => stream.putStr s!"\"{varID gconf (Var.ffv ffVar)}\""
  | .const val => stream.putStr s!"{val.val}"
  | .array arr =>
      stream.putStr "["
      let varStrs := arr.map (fun v =>
        match v with
        | .inl ffVar => s!"\"{varID gconf (Var.ffv ffVar)}\""
        | .inr val => s!"{val.val}"
      )
      stream.putStr (String.intercalate ", " varStrs)
      stream.putStr "]"

/-- Prints a list of macro exit variable information as JSON -/
def printVarsInfo_asJSON {c : ZKConfig} (gconf : GlobalConfig c)
  (stream : IO.FS.Stream) (vs : MacroExitVarsInfo c) : IO Unit := do
  match vs with
  | [] => return ()
  | (id,v) :: rest =>
      stream.putStr s!"\"{id}\": "
      printVarInfo_asJSON gconf stream v
      if rest != [] then
        stream.putStr ", "
      printVarsInfo_asJSON gconf stream rest

/-- Prints a macro as JSON -/
def printMacro_asJSON {c : ZKConfig} (gconf : GlobalConfig c)
  (stream : IO.FS.Stream) (m : FFMacro c) : IO Unit := do
  stream.putStrLn s!"    \"{m.name}\": \{"
  stream.putStr "        \"params\": ["
  printParams_asJSON gconf stream m.params
  stream.putStrLn "],"
  stream.putStr "        \"vars_info\": {"
  printVarsInfo_asJSON gconf stream m.vars_info
  stream.putStrLn "},"
  stream.putStr "        \"formula\": \""
  printFormula gconf stream m.body 0 false
  stream.putStrLn " \""
  stream.putStr "     }"

/-- Prints a list of macros as JSON -/
def printMacros_asJSON {c : ZKConfig} (gconf : GlobalConfig c)
  (stream : IO.FS.Stream) (ms : List (FFMacro c)) : IO Unit := do
  match ms with
  | [] => return ()
  | m :: rest =>
      printMacro_asJSON gconf stream m
      if rest != [] then stream.putStrLn ","
      printMacros_asJSON gconf stream rest

/-- Prints a constraint system as JSON -/
def printConstraintSystem_asJSON {c : ZKConfig} (gconf : GlobalConfig c)
  (stream : IO.FS.Stream) (sys : FFConstraintSystem c) : IO Unit := do
  match mainFormula gconf sys with
  | Except.error e => stream.putStrLn s!"Error: {e}"
  | Except.ok (f, vars) =>
  stream.putStrLn "{"
  stream.putStrLn s!"  \"prime\": {c.p},"
  -- Macros
  stream.putStrLn s!"  \"macros\": \{"
  (printMacros_asJSON gconf stream (sys.macros.reverse)) -- we assume main is first
  stream.putStrLn ""
  stream.putStrLn s!"  },"
  -- Main formula
  stream.putStrLn s!"  \"main\": \{"
  stream.putStr s!"    \"vars\": ["
  printParams_asJSON gconf stream vars
  stream.putStrLn s!"],"
  stream.putStr s!"    \"formula\": \""
  printFormula gconf stream f 0 false
  stream.putStr s!" \""
  stream.putStrLn " }"
  stream.putStrLn "}"
  stream.flush


end Llzk.FFConstraints.SMT
