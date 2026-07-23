import Corellzk2smt.SymExec.Correctness.Lemmas

/-!
Correctness statement for `seEvalAssignment` (`SymExec/Assignment.lean`) against its concrete
counterpart `evalAssign` (`Language/Core/Semantics/Basic.lean`). `seEvalAssignment` is currently a
permanent `"TBD"` stub, so this is left as an honest `sorry` -- see `SimpleCmdCorrectness.lean`,
which composes this together with `ArrayCmdsCorrectness.lean`'s theorems into `H_simple_holds`.
-/

namespace Corellzk2smt.SymExec.Correctness.AssignmentCorrectness

open Corellzk2smt.Config
open Corellzk2smt.Language.Core.Syntax.AST
open Corellzk2smt.Language.Core.Semantics.Basic
open Corellzk2smt.SymExec.Basic
open Corellzk2smt.SymExec.BigStep
open Corellzk2smt.FFConstraints.Basic
open Corellzk2smt.SymExec.Correctness.Lemmas

/-- `seEvalAssignment` correctly translates `evalAssign`. Genuinely open: `seEvalAssignment` is
    currently a permanent `"TBD"` stub, under which this would be vacuously provable (the success
    hypothesis inside `TranslatesCorrectly` can never fire) -- but that proves the wrong thing, so
    it's left as an honest `sorry` instead. Once `seEvalAssignment` is actually implemented, this
    is the one place that needs a real proof. -/
theorem seEvalAssignment_correct {c : ZKConfig} (gconf : GlobalConfig c)
    (specs : List (FuncSpec c)) (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD)
    (id : VarID) (e : Expr c) :
    TranslatesCorrectly gconf sconf specs ctx
      (fun env => evalAssign md gconf env id e)
      (fun symEnv => seEvalAssignment md gconf sconf symEnv specs id e) := by
  sorry

end Corellzk2smt.SymExec.Correctness.AssignmentCorrectness
