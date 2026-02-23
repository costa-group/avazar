import Llzk.Basic
import Llzk.Language.Core.Syntax.AST
import Llzk.FFConstraints.Basic
import Std.Data.TreeMap.Basic

namespace Llzk.SymExec.Basic

open Llzk.Language.Core.Syntax.AST
open Llzk.FFConstraints.Basic

/- This is a structure that will be passed around in the symbolic interpreter. We can
   encapsulate various things here. Separating it from the symbolic state makes things
   simpler.

   We can change the configuration without affecting the symbolic state, and we can
   also add more things to the configuration later without substantial changes
   to the code
-/
structure SymExecConfig (c : ZKConfig) where
  lastUsedId : Nat := 0
  deriving Inhabited

/- A symbolic variable can either be a concrete value of a finite
   field or a field constraint variable -/
inductive SymFFVar (c : ZKConfig) where
  | var : FFVar → SymFFVar c
  | const : FF c → SymFFVar c
  deriving Repr, Inhabited

/- A symbolic array is an array of symbolic finite field variables -/
abbrev SymFFArray (c : ZKConfig) := Array (SymFFVar c)

/- A symbolic value can either be a SymFFVar or a SymFFArray -/
inductive SymValue (c : ZKConfig) where
  | ffVar : SymFFVar c → SymValue c
  | ffArray : SymFFArray c → SymValue c
  deriving Repr, Inhabited

/- Environment: A mapping from program variables to Value -/
abbrev SymEnv (c : ZKConfig) := Std.TreeMap VarID (SymValue c)


def emptySymEnv {c : ZKConfig} : SymEnv c := Std.TreeMap.empty

/- A specification for a sequence of commands. It is a formula describing the
   relationship between the input and output symbolic environments.

   This is be extended later with more information to facilitate proofs.
    -/
structure CmdsSpec (c : ZKConfig) where
  inSymEnv : SymEnv c := emptySymEnv
  outSymEnv : SymEnv c := emptySymEnv
  f : FFFormula c := FFFormula.false
  deriving Inhabited


def emptyCmdsSpec {c : ZKConfig} : CmdsSpec c := {}


def symExecSkip {c : ZKConfig} (cfg : SymExecConfig c) (md: CmdMD) (symEnv : SymEnv c) : CmdsSpec c :=
  {}

def symExecAssignment {c : ZKConfig} (cfg : SymExecConfig c) (md: CmdMD) (symEnv : SymEnv c) (id : String) (e : Expr c) : CmdsSpec c :=
  {}

def symExecNewArray {c : ZKConfig} (cfg : SymExecConfig c) (md: CmdMD) (symEnv : SymEnv c) (id : String) (size : SimpleExpr c) : CmdsSpec c :=
  {}

def symExecArrayRead {c : ZKConfig} (cfg : SymExecConfig c) (md: CmdMD) (symEnv : SymEnv c) (out : String) (a : String) (idx : SimpleExpr c) : CmdsSpec c :=
  {}

def symExecArrayWrite {c : ZKConfig} (cfg : SymExecConfig c) (md: CmdMD) (symEnv : SymEnv c) (a : String) (idx : SimpleExpr c) (value : SimpleExpr c) : CmdsSpec c :=
  {}

def symExecArrayCopy {c : ZKConfig} (cfg : SymExecConfig c) (md: CmdMD) (symEnv : SymEnv c) (out : String) (a : String) : CmdsSpec c :=
  {}

end Llzk.SymExec.Basic
