import Llzk.Basic
import Llzk.Language.Core.Syntax.AST
import Llzk.Language.Core.Syntax.Printer
import Llzk.FFConstraints.Basic
import Llzk.Language.Core.Semantics.Basic
import Std.Data.TreeMap.Basic

namespace Llzk.SymExec.Basic

open Llzk.Language.Core.Syntax.AST
open Llzk.FFConstraints.Basic
open Llzk.Language.Core.Semantics.Basic

/- This is a structure that will be passed around in the symbolic interpreter. We can
   encapsulate various things here. Separating it from the symbolic state makes things
   simpler.

   We can change the configuration without affecting the symbolic state, and we can
   also add more things to the configuration later without substantial changes
   to the code
-/
structure SymExecConfig (c : ZKConfig) where
  nextId : Nat := 0
  deriving Inhabited

/- A symbolic variable can either be a concrete value of a finite
   field or a field constraint variable -/
inductive SymFFVar (c : ZKConfig) where
  | var : FFVar → SymFFVar c
  | const : FF c → SymFFVar c
  deriving Repr, BEq, Inhabited

/- A symbolic array is an array of symbolic finite field variables -/
abbrev SymFFArray (c : ZKConfig) := Array (SymFFVar c)

/- A symbolic value can either be a SymFFVar or a SymFFArray -/
inductive SymValue (c : ZKConfig) where
  | ffVar : SymFFVar c → SymValue c
  | ffArray : SymFFArray c → SymValue c
  deriving Repr, BEq, Inhabited

/- Environment: A mapping from program variables to Value -/
abbrev SymEnv (c : ZKConfig) := Std.TreeMap VarID (SymValue c)

def emptySymEnv {c : ZKConfig} : SymEnv c := Std.TreeMap.empty



/- Retrieve a value from a symbolic environment. It fails if the variable
   is not in the environment -/
def getVar {c : ZKConfig} (env : SymEnv c) (id : VarID) : Except String (SymValue c) :=
  match env.get? id with
  | some v => Except.ok v
  | none   => Except.error s!"Variable '{id}' not found"

/- Set the value of a variable in a symbolic environment. It updates
   the value if it exists already. It never fails -/
def setVar {c : ZKConfig} (env : SymEnv c) (id : VarID) (v : SymValue c) : SymEnv c :=
  env.insert id v


/- A specification for a sequence of commands. It is a formula describing the
   relationship between the input and output symbolic environments.

   This is be extended later with more information to facilitate proofs.
    -/
structure CmdsSpec (c : ZKConfig) where
  inSymEnv : SymEnv c := emptySymEnv
  outSymEnv : SymEnv c := emptySymEnv
  f : FFFormula c := FFFormula.false
  nextId : Nat := 0
  newFFVars : FFVarSet := emptyFFVarSet
  newBoolVars : BoolVarSet := emptyBoolVarSet
  deriving Inhabited

structure ExprSpec (c : ZKConfig) where
  inSymEnv : SymEnv c := emptySymEnv
  f : FFFormula c := FFFormula.false
  -- resVar is not really used now. Maybe it will
  -- be useful for the proofs later.
  resVar : FFVar := default
  nextId : Nat := 0
  newFFVars : FFVarSet := emptyFFVarSet
  newBoolVars : BoolVarSet := emptyBoolVarSet
  deriving Inhabited

structure CondSpec (c : ZKConfig) where
  inSymEnv : SymEnv c := emptySymEnv
  f : FFFormula c := FFFormula.false
  nextId : Nat := 0
  newFFVars : FFVarSet := emptyFFVarSet
  newBoolVars : BoolVarSet := emptyBoolVarSet
  deriving Inhabited

structure IfSpec (c : ZKConfig) where
  inSymEnv : SymEnv c := emptySymEnv
  outSymEnv : SymEnv c := emptySymEnv
  tbF : FFFormula c := FFFormula.false
  ebF : FFFormula c := FFFormula.false
  nextId : Nat := 0
  newFFVars : FFVarSet := emptyFFVarSet
  newBoolVars : BoolVarSet := emptyBoolVarSet
  deriving Inhabited

structure FuncSpec (c : ZKConfig) where
  name : String := ""
  inSymEnv : SymEnv c := emptySymEnv
  outSymEnv : SymEnv c := emptySymEnv
  f : FFMacro c := default
  nextId : Nat := 0
  -- Concrete information about the parameters and return values
  params : List Param
  rets : List Param
  -- Variables that correspond to params
  numAuxFFVars : Nat := 0
  numAuxBoolVars : Nat := 0
  deriving Inhabited

structure RetVarsSpec (c : ZKConfig) where
  outSymEnv : SymEnv c := emptySymEnv
  nextId : Nat := 0
  newFFVars : FFVarSet := emptyFFVarSet
  actRetsVars : List (MacroCallParam c) := []
  deriving Inhabited


end Llzk.SymExec.Basic
