import Corellzk2smt.SymExec.Correctness.Lemmas

/-!
Correctness statements for the four array operations in `SymExec/ArrayCmds.lean`
(`seNewArray`/`seReadArray`/`seWriteArray`/`seCopyArray`) against their concrete counterparts in
`Language/Core/Semantics/Basic.lean`. All four symbolic operations are currently permanent `"TBD"`
stubs, so these are left as honest `sorry`s -- see `SimpleCmdCorrectness.lean`, which composes
these together with `AssignmentCorrectness.lean`'s theorem into `H_simple_holds`.
-/

namespace Corellzk2smt.SymExec.Correctness.ArrayCmdsCorrectness

open Corellzk2smt.Config
open Corellzk2smt.Language.Core.Syntax.AST
open Corellzk2smt.Language.Core.Semantics.Basic
open Corellzk2smt.SymExec.Basic
open Corellzk2smt.SymExec.BigStep
open Corellzk2smt.SymExec.Correctness.Lemmas

/-- `seNewArray` correctly translates `evalNewArray`. Genuinely open, same reason as
    `seEvalAssignment_correct` (`AssignmentCorrectness.lean`): `seNewArray` is currently a
    permanent `"TBD"` stub. -/
theorem seNewArray_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (md : CmdMD) (id : VarID) (size : SimpleExpr c) :
    TranslatesCorrectly gconf sconf specs
      (fun env => evalNewArray md gconf env id size)
      (fun symEnv => seNewArray md gconf sconf symEnv specs id size) := by
  sorry

/-- `seReadArray` correctly translates `evalReadArray`. Genuinely open, same reason as
    `seEvalAssignment_correct`. -/
theorem seReadArray_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (md : CmdMD) (out a : VarID) (index : SimpleExpr c) :
    TranslatesCorrectly gconf sconf specs
      (fun env => evalReadArray md gconf env out a index)
      (fun symEnv => seReadArray md gconf sconf symEnv specs out a index) := by
  sorry

/-- `seWriteArray` correctly translates `evalWriteArray`. Genuinely open, same reason as
    `seEvalAssignment_correct`. -/
theorem seWriteArray_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (md : CmdMD) (a : VarID) (index value : SimpleExpr c) :
    TranslatesCorrectly gconf sconf specs
      (fun env => evalWriteArray md gconf env a index value)
      (fun symEnv => seWriteArray md gconf sconf symEnv specs a index value) := by
  sorry

/-- `seCopyArray` correctly translates `evalCopyArray`. Genuinely open, same reason as
    `seEvalAssignment_correct`. -/
theorem seCopyArray_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (md : CmdMD) (out a : VarID) :
    TranslatesCorrectly gconf sconf specs
      (fun env => evalCopyArray md gconf env out a)
      (fun symEnv => seCopyArray md gconf sconf symEnv specs out a) := by
  sorry

end Corellzk2smt.SymExec.Correctness.ArrayCmdsCorrectness
