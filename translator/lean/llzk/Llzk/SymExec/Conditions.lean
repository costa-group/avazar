import Llzk.Language.Core.Syntax.AST
import Llzk.Language.Core.Syntax.Printer
import Llzk.FFConstraints.Basic
import Llzk.SymExec.Basic
import Llzk.SymExec.Common

namespace Llzk.SymExec.SymInstr

open Llzk.Language.Core.Syntax.AST
open Llzk.FFConstraints.Basic
open Llzk.Language.Core.Semantics.Basic
open Llzk.SymExec.Basic



/- Try to evaluate a condition to a boolean value. This is used to discard
   infeasible branches in if-statements.
-/
def evalCond {c : ZKConfig}
  (_cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c)
  (cond : Cond c)
  : Except String Bool := do
  match cond with
  | .eq s1 s2 =>
    let v1 ← simpleExprToFF senv s1
    let v2 ← simpleExprToFF senv s2
    return v1 == v2

/- Symbolic execution of conditions -/
def sEvalCond {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (cond : Cond c)
  : Except String (CondSpec c) := do
  match cond with
  | .eq s1 s2 =>
    let v1 ← simpleExprToTerm senv s1
    let v2 ← simpleExprToTerm senv s2
    return {
      inSymEnv := senv,
      f := .eq v1 v2,
      nextId := cfg.nextId,
      newFFVars := emptyFFVarSet,
      newBoolVars := emptyBoolVarSet
    }


end Llzk.SymExec.SymInstr
