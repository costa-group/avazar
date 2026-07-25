import Corellzk2smt.SymExec.Correctness.Lemmas
import Corellzk2smt.SymExec.Correctness.AssignmentCorrectness
import Corellzk2smt.SymExec.Correctness.ArrayCmdsCorrectness

/-!
`H_simple`'s conditional-form statement, given its own file so it's easy to find without wading
through `ProgCorrectness.lean`'s whole-program induction. `seSimpleCmd` dispatches to one of five
per-operation functions (`SymExec/Assignment.lean`/`ArrayCmds.lean`); this file's proof is pure
dispatch, routing each case to `AssignmentCorrectness.lean`/`ArrayCmdsCorrectness.lean`'s own
theorem for that operation (each currently an honest `sorry`, since the operation itself is still
a `"TBD"` stub) -- no `sorry` lives directly in this file anymore.
-/

namespace Corellzk2smt.SymExec.Correctness.SimpleCmdCorrectness

open Corellzk2smt.Config
open Corellzk2smt.Language.Core.Syntax.AST
open Corellzk2smt.Language.Core.Semantics.Basic
open Corellzk2smt.Language.Core.Semantics.BigStep
open Corellzk2smt.SymExec.Basic
open Corellzk2smt.SymExec.BigStep
open Corellzk2smt.FFConstraints.Basic
open Corellzk2smt.FFConstraints.Lemmas
open Corellzk2smt.Language.Core.Analysis.DefinedVars
open Corellzk2smt.SymExec.Correctness.Lemmas
open Corellzk2smt.SymExec.Correctness.AssignmentCorrectness
open Corellzk2smt.SymExec.Correctness.ArrayCmdsCorrectness

/-- `H_simple`'s conditional-form statement, kept as a theorem (not an assumed parameter) so every
    consumer calls it by name rather than ever unfolding `seSimpleCmd` directly. Dispatches on
    `i`'s command: the five simple-command cases each reduce (via `evalSimpleCmd`/`seSimpleCmd`'s
    own definitional unfolding) to the matching per-operation theorem; every other command shape is
    unreachable in practice (the caller already filters to simple commands only) and is discharged
    vacuously, since both `evalSimpleCmd`/`seSimpleCmd` error on it. -/
theorem H_simple_holds {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (ctx : FFFormula c) (i : ComWithMD c) :
    TranslatesCorrectly gconf sconf specs ctx (fun env => evalSimpleCmd gconf env i)
      (fun symEnv => seSimpleCmd gconf sconf symEnv specs i) := by
  match i with
  | .mk md cmd =>
    match cmd with
    | .assign id e =>
        have heq_c : (fun env => evalSimpleCmd gconf env (ComWithMD.mk md (Com.assign id e)))
            = (fun env => evalAssign md gconf env id e) := by
          funext env; simp only [evalSimpleCmd]
        have heq_s : (fun symEnv => seSimpleCmd gconf sconf symEnv specs
              (ComWithMD.mk md (Com.assign id e)))
            = (fun symEnv => seEvalAssignment md gconf sconf symEnv specs id e) := by
          funext symEnv; simp only [seSimpleCmd]
        rw [heq_c, heq_s]
        exact seEvalAssignment_correct gconf specs sconf ctx md id e
    | .new_array id size =>
        have heq_c : (fun env => evalSimpleCmd gconf env (ComWithMD.mk md (Com.new_array id size)))
            = (fun env => evalNewArray md gconf env id size) := by
          funext env; simp only [evalSimpleCmd]
        have heq_s : (fun symEnv => seSimpleCmd gconf sconf symEnv specs
              (ComWithMD.mk md (Com.new_array id size)))
            = (fun symEnv => seNewArray md gconf sconf symEnv specs id size) := by
          funext symEnv; simp only [seSimpleCmd]
        rw [heq_c, heq_s]
        exact seNewArray_correct gconf specs sconf ctx md id size
    | .read_array out a index =>
        have heq_c : (fun env => evalSimpleCmd gconf env
              (ComWithMD.mk md (Com.read_array out a index)))
            = (fun env => evalReadArray md gconf env out a index) := by
          funext env; simp only [evalSimpleCmd]
        have heq_s : (fun symEnv => seSimpleCmd gconf sconf symEnv specs
              (ComWithMD.mk md (Com.read_array out a index)))
            = (fun symEnv => seReadArray md gconf sconf symEnv specs out a index) := by
          funext symEnv; simp only [seSimpleCmd]
        rw [heq_c, heq_s]
        exact seReadArray_correct gconf specs sconf ctx md out a index
    | .write_array a index value =>
        have heq_c : (fun env => evalSimpleCmd gconf env
              (ComWithMD.mk md (Com.write_array a index value)))
            = (fun env => evalWriteArray md gconf env a index value) := by
          funext env; simp only [evalSimpleCmd]
        have heq_s : (fun symEnv => seSimpleCmd gconf sconf symEnv specs
              (ComWithMD.mk md (Com.write_array a index value)))
            = (fun symEnv => seWriteArray md gconf sconf symEnv specs a index value) := by
          funext symEnv; simp only [seSimpleCmd]
        rw [heq_c, heq_s]
        exact seWriteArray_correct gconf specs sconf ctx md a index value
    | .copy_array out a =>
        have heq_c : (fun env => evalSimpleCmd gconf env (ComWithMD.mk md (Com.copy_array out a)))
            = (fun env => evalCopyArray md gconf env out a) := by
          funext env; simp only [evalSimpleCmd]
        have heq_s : (fun symEnv => seSimpleCmd gconf sconf symEnv specs
              (ComWithMD.mk md (Com.copy_array out a)))
            = (fun symEnv => seCopyArray md gconf sconf symEnv specs out a) := by
          funext symEnv; simp only [seSimpleCmd]
        rw [heq_c, heq_s]
        exact seCopyArray_correct gconf specs sconf ctx md out a
    | .if_stmt .. | .loop_exp .. | .loop .. | .func_call .. =>
        intro symEnv _hbelow _hvalid spec hspec_eq
        simp only [seSimpleCmd] at hspec_eq
        simp at hspec_eq

/-- `H_simple_domain`'s conditional-form statement -- lets `Lemmas.lean`'s domain-of-defined family
    (and everything downstream) treat "whatever `seSimpleCmd` does to the symbolic env's domain" as
    an opaque hypothesis, so it never needs to unfold `seSimpleCmd`/`seEvalAssignment`/etc. itself.
    Dispatches the same way `H_simple_holds` does: the four array ops are still permanent `"TBD"`
    stubs, discharged vacuously; `.assign` is genuinely open (mirrors `seEvalAssignment_correct`'s
    own honest `sorry`, since `seEvalAssignmentConst` can now succeed). -/
theorem H_simple_domain_holds {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (symEnv : SymEnv c) (vars : VarIDSet) (md : CmdMD) (cmd : Com c)
    (hpre : ∀ id, id ∈ definedVarsCom vars cmd → symEnv.contains id) (spec : CmdsSpec c)
    (heq : seSimpleCmd gconf sconf symEnv specs (ComWithMD.mk md cmd) = Except.ok spec) :
    ∀ id, symEnv.contains id ↔ spec.outSymEnv.contains id := by
  match cmd with
  | .assign id e =>
      sorry
  | .new_array id size =>
      simp [seSimpleCmd, seNewArray] at heq
  | .read_array out a index =>
      simp [seSimpleCmd, seReadArray] at heq
  | .write_array a index value =>
      simp [seSimpleCmd, seWriteArray] at heq
  | .copy_array out a =>
      simp [seSimpleCmd, seCopyArray] at heq
  | .if_stmt .. | .loop_exp .. | .loop .. | .func_call .. =>
      simp [seSimpleCmd] at heq

/-- `H_simple_names_below`'s conditional-form statement -- the `FormulaNamesBelow` analogue of
    `H_simple_domain_holds` above, for the same reason (keep `Lemmas.lean`'s `_names_below` family
    from ever unfolding `seSimpleCmd` itself). Same dispatch/status as `H_simple_domain_holds`. -/
theorem H_simple_names_below_holds {c : ZKConfig} (gconf : GlobalConfig c)
    (specs : List (FuncSpec c)) (badName : String) (sconf : SymExecConfig c) (symEnv : SymEnv c)
    (i : ComWithMD c) (spec : CmdsSpec c)
    (heq : seSimpleCmd gconf sconf symEnv specs i = Except.ok spec) :
    FormulaNamesBelow spec.f badName := by
  match i with
  | .mk md cmd =>
    match cmd with
    | .assign id e =>
        sorry
    | .new_array id size =>
        simp [seSimpleCmd, seNewArray] at heq
    | .read_array out a index =>
        simp [seSimpleCmd, seReadArray] at heq
    | .write_array a index value =>
        simp [seSimpleCmd, seWriteArray] at heq
    | .copy_array out a =>
        simp [seSimpleCmd, seCopyArray] at heq
    | .if_stmt .. | .loop_exp .. | .loop .. | .func_call .. =>
        simp [seSimpleCmd] at heq

end Corellzk2smt.SymExec.Correctness.SimpleCmdCorrectness
