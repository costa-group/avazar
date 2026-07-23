import Corellzk2smt.SymExec.PartialCorrectness.FuncCorrectness
import Corellzk2smt.Language.Core.Analysis.DefinedVars

/- Shared machinery for whole-program correctness (`seExecFuncs`/`seExecProg`,
   `SymExec/BigStep.lean`): `seFunc_f_name_eq`, `fetchFunc_skip_ne`, `evalFunCall_congr`,
   `seFuncCall_names_below`, and the two purely-structural (`WellShaped`/no-dup-names/
   `TranslatesCorrectly`-independent) inductions over `seExecFuncs.loop`'s own recursion:
   `seExecFuncs_loop_specs_suffix` (the spec accumulator only ever grows by prepending) and
   `seExecFuncs_loop_params_split` (every macro's `params : List Var` field decomposes into a
   params range / a rets range / an opaque aux list, exposing `seFunc_f_params_split_basic`'s per-
   function fact at the whole-program level). None of this is stated in terms of
   `TranslatesCorrectly` itself, so it's reused unchanged by both the (now-removed) unconditional
   formalization and the current conditional one in
   `SymExec/PartialCorrectness/ProgCorrectness.lean` -- see that file's header for
   `seExecFuncs_loop_correct`/`seExecFuncs_correct` (induct over
   `seExecFuncs`'s own `loop`, discharging `H_funcCall` for real -- not assuming it -- at each
   step) and the final top-level theorem, `seExecProg_call_correct`, built on top of this. -/

namespace Corellzk2smt.SymExec.ProgCorrectness

open Corellzk2smt.Config
open Corellzk2smt.Language.Core.Syntax.AST
open Corellzk2smt.Language.Core.Semantics.Basic
open Corellzk2smt.Language.Core.Semantics.BigStep
open Corellzk2smt.Language.Core.Analysis.WellShaped
open Corellzk2smt.Language.Core.Analysis.DefinedVars
open Corellzk2smt.SymExec.Basic
open Corellzk2smt.SymExec.BigStep
open Corellzk2smt.FFConstraints.Basic
open Corellzk2smt.FFConstraints.Satisfiability
open Corellzk2smt.FFConstraints.Satisfiability_th
open Corellzk2smt.SymExec.Lemmas
open Corellzk2smt.SymExec.PartialCorrectness.Correctness
open Corellzk2smt.SymExec.PartialCorrectness.FuncCorrectness

/-- `seFunc`'s output spec's macro name (`fspec.f.name`) is exactly the translated function's own
    name -- mirrors `seFunc_eq_shape`'s exact proof shape (same unfolding sequence), just also
    reading off the `f.name` field, which `seFunc_eq_shape` doesn't. -/
theorem seFunc_f_name_eq {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (name : FName) (params rets : List Param) (body : List (ComWithMD c)) (fspec : FuncSpec c)
    (h : seFunc gconf specs (Func.mk name params rets body) = Except.ok fspec) :
    fspec.f.name = name := by
  simp only [seFunc] at h
  cases hdup : hasDupNames (params.map (·.name)) || hasDupNames (rets.map (·.name)) with
  | true => simp [hdup] at h
  | false =>
    simp only [hdup] at h
    cases hmp : mintFreshParams (c := c) 0 params
        ((definedVarsOfFunc (Func.mk name params rets body)).foldl
          (fun env id => setVar env id (SymValue.simple (SimpleSymVal.const 0))) emptySymEnv)
      with
    | error e => simp [hmp] at h
    | ok result =>
        obtain ⟨nv1, paramVars, inSymEnv⟩ := result
        simp only [hmp] at h
        cases hbs : seCmds gconf { nextVarId := nv1 } inSymEnv specs body with
        | error e => simp [hbs] at h
        | ok bodySpec =>
            simp only [hbs] at h
            cases hmr : mintFreshRetsWithEq (c := c) bodySpec.nextVarId bodySpec.outSymEnv rets
              with
            | error e => simp [hmr] at h
            | ok result2 =>
                obtain ⟨nv2, retVars, retBinds, retEqFormula⟩ := result2
                simp only [hmr] at h
                injection h with h
                subst h
                rfl

/-- `seExecFuncs.loop` only ever *prepends* newly-built specs onto its accumulator, never removing
    or reordering anything already there -- a purely structural fact about the recursion, needing
    no `WellShaped`/no-dup-names hypotheses at all. Used to relate a macro's own construction-time
    callee list (whatever `specs` was when the loop processed it) back to the *final* result: it's
    always a suffix of it, with the same functions in between untouched. -/
theorem seExecFuncs_loop_specs_suffix {c : ZKConfig} (gconf : GlobalConfig c) :
    ∀ (funcs : List (FuncWithMD c)) (specs newSpecs : List (FuncSpec c)),
      seExecFuncs.loop gconf funcs specs = Except.ok newSpecs →
      ∃ built : List (FuncSpec c), newSpecs = built ++ specs ∧ built.length = funcs.length := by
  intro funcs
  induction funcs with
  | nil =>
      intro specs newSpecs h
      simp only [seExecFuncs.loop] at h
      injection h with h
      exact ⟨[], by simp [h], rfl⟩
  | cons func funcs' ih =>
      intro specs newSpecs h
      obtain ⟨md, func⟩ := func
      simp only [seExecFuncs.loop] at h
      cases hseFunc_eq : seFunc gconf specs func with
      | error e =>
          rw [hseFunc_eq] at h
          simp only [Bind.bind, Except.bind] at h
          exact absurd h (by simp)
      | ok fspec =>
          rw [hseFunc_eq] at h
          simp only [Bind.bind, Except.bind] at h
          obtain ⟨built', hbuilt'_eq, hbuilt'_len⟩ := ih (fspec :: specs) newSpecs h
          refine ⟨built' ++ [fspec], ?_, ?_⟩
          · rw [hbuilt'_eq, List.append_assoc]; rfl
          · simp [hbuilt'_len]

/-- `seFunc_f_params_split_basic`'s fact, threaded through the whole loop: every spec ever built (either
    already in `specs` when the loop starts, or newly minted along the way) has its macro's
    `params : List Var` field split into a params range, a rets range, and an opaque aux list --
    a purely structural fact (no `WellShaped`/no-dup-names/`TranslatesCorrectly` involved at all),
    so it doesn't need to be threaded alongside `seExecFuncs_loop_correct`'s own induction --
    carrying it here, independently, avoids complicating that already-verified proof. -/
theorem seExecFuncs_loop_params_split {c : ZKConfig} (gconf : GlobalConfig c) :
    ∀ (funcs : List (FuncWithMD c)) (specs newSpecs : List (FuncSpec c)),
      (∀ spec ∈ specs, ∃ (retsOffset : Nat) (auxVarsList : List Var),
        spec.f.params =
          (List.range (totalParamSize spec.params)).map (fun i => Var.ffv i) ++
          (List.range (totalParamSize spec.rets)).map (fun i => Var.ffv (retsOffset + i)) ++
          auxVarsList ∧
        (auxVarsList.filter isFFvVar).length = spec.numAuxFFVars ∧
        (auxVarsList.filter (fun v => !isFFvVar v)).length = spec.numAuxBoolVars ∧
        auxVarsList.Pairwise (fun a b => compare a b = .lt)) →
      seExecFuncs.loop gconf funcs specs = Except.ok newSpecs →
      ∀ spec ∈ newSpecs, ∃ (retsOffset : Nat) (auxVarsList : List Var),
        spec.f.params =
          (List.range (totalParamSize spec.params)).map (fun i => Var.ffv i) ++
          (List.range (totalParamSize spec.rets)).map (fun i => Var.ffv (retsOffset + i)) ++
          auxVarsList ∧
        (auxVarsList.filter isFFvVar).length = spec.numAuxFFVars ∧
        (auxVarsList.filter (fun v => !isFFvVar v)).length = spec.numAuxBoolVars ∧
        auxVarsList.Pairwise (fun a b => compare a b = .lt) := by
  intro funcs
  induction funcs with
  | nil =>
      intro specs newSpecs hbase h
      simp only [seExecFuncs.loop] at h
      injection h with h
      rw [← h]
      exact hbase
  | cons func funcs' ih =>
      intro specs newSpecs hbase h
      obtain ⟨md, name, params, rets, body⟩ := func
      simp only [seExecFuncs.loop] at h
      cases hseFunc_eq : seFunc gconf specs (Func.mk name params rets body) with
      | error e =>
          rw [hseFunc_eq] at h
          simp only [Bind.bind, Except.bind] at h
          exact absurd h (by simp)
      | ok fspec =>
          rw [hseFunc_eq] at h
          simp only [Bind.bind, Except.bind] at h
          have hfspec_split := seFunc_f_params_split_basic gconf specs name params rets body fspec
            hseFunc_eq
          obtain ⟨hname_eq, hparams_eq, hrets_eq⟩ := seFunc_eq_shape gconf specs name params rets
            body fspec hseFunc_eq
          have hbase' : ∀ spec ∈ fspec :: specs, ∃ (retsOffset : Nat) (auxVarsList : List Var),
              spec.f.params =
                (List.range (totalParamSize spec.params)).map (fun i => Var.ffv i) ++
                (List.range (totalParamSize spec.rets)).map (fun i => Var.ffv (retsOffset + i)) ++
                auxVarsList ∧
              (auxVarsList.filter isFFvVar).length = spec.numAuxFFVars ∧
              (auxVarsList.filter (fun v => !isFFvVar v)).length = spec.numAuxBoolVars ∧
              auxVarsList.Pairwise (fun a b => compare a b = .lt) := by
            intro spec hspec
            rcases List.mem_cons.mp hspec with hspec | hspec
            · rw [hspec, hparams_eq, hrets_eq]; exact hfspec_split
            · exact hbase spec hspec
          exact ih (fspec :: specs) newSpecs hbase' h

/-- `fetchFunc`'s search skips straight past a prepended function whose name doesn't match --
    the `FuncWithMD`/`Prog` mirror of `fetchFuncSpec_prepend_indep`/`fetchMacro_skip_ne`. -/
theorem fetchFunc_skip_ne {c : ZKConfig} (badFunc : FuncWithMD c) (rest : Prog c) (fname : FName)
    (hne : funcWithMDName badFunc ≠ fname) :
    fetchFunc (badFunc :: rest) fname = fetchFunc rest fname := by
  match badFunc with
  | FuncWithMD.mk md func =>
    match func with
    | Func.mk name params rets body =>
      simp only [funcWithMDName] at hne
      have hbeq : (name == fname) = false := by simpa using hne
      simp only [fetchFunc, hbeq, Bool.false_eq_true, ↓reduceIte]

/-- `evalFunCall` only ever reads `p` through the single `fetchFunc p fname` lookup at its start
    -- everything downstream depends only on the lookup's *result*, so two programs whose
    `fetchFunc` behaves identically for `fname` give identical `evalFunCall` results. -/
theorem evalFunCall_congr {c : ZKConfig} (gconf : GlobalConfig c) (p1 p2 : Prog c) (fname : FName)
    (heq : fetchFunc p1 fname = fetchFunc p2 fname)
    (hnodup1 : hasDupFuncNames p1 = false) (hnodup2 : hasDupFuncNames p2 = false)
    (argVals : List (Value c)) :
    evalFunCall gconf p1 fname argVals = evalFunCall gconf p2 fname argVals := by
  simp only [evalFunCall, hnodup1, hnodup2, Bool.false_eq_true, if_false]
  rw [heq]


/-- `seFuncCall`'s output formula never directly calls a name that isn't the call target `fname'`
    -- a standalone (non-recursive, since `seFuncCall` doesn't recurse) specialization of the
    `seCmd_names_below`-style argument for the one place a `.call` node is actually introduced. -/
theorem seFuncCall_names_below {c : ZKConfig} (gconf : GlobalConfig c) (sconf : SymExecConfig c)
    (symEnv : SymEnv c) (specs : List (FuncSpec c)) (fname' : FName) (args : List (SimpleExpr c))
    (outs : List VarID) (badName : FName) (hne : badName ≠ fname')
    (hspecs_wf : ∀ spec ∈ specs, spec.f.name = spec.name)
    (spec : CmdsSpec c)
    (hspec_eq : seFuncCall gconf sconf symEnv specs fname' args outs = Except.ok spec) :
    FormulaNamesBelow spec.f badName := by
  simp only [seFuncCall] at hspec_eq
  cases hfs : fetchFuncSpec specs fname' with
  | error e => rw [hfs] at hspec_eq; simp at hspec_eq
  | ok fspec' =>
    rw [hfs] at hspec_eq
    simp only [] at hspec_eq
    cases hargs : resolveSimpleExprsToSymValue symEnv args with
    | error e => rw [hargs] at hspec_eq; simp at hspec_eq
    | ok argVals =>
      rw [hargs] at hspec_eq
      simp only [] at hspec_eq
      cases hflat : flattenArgVals fspec'.params argVals with
      | error e => rw [hflat] at hspec_eq; simp at hspec_eq
      | ok inputParams =>
        rw [hflat] at hspec_eq
        simp only [] at hspec_eq
        cases hsv : setVars symEnv outs (mintFreshRets sconf.nextVarId fspec'.rets).2.2 with
        | error e => rw [hsv] at hspec_eq; simp at hspec_eq
        | ok outSymEnv' =>
          rw [hsv] at hspec_eq
          simp only [] at hspec_eq
          injection hspec_eq with hspec_eq
          obtain ⟨hspecname, hspecmem⟩ := fetchFuncSpec_sound specs fname' fspec' hfs
          have hfname_eq2 : fspec'.f.name = fname' := by
            rw [hspecs_wf fspec' hspecmem, hspecname]
          simp only [FormulaNamesBelow, ← hspec_eq]
          rw [hfname_eq2]
          exact hne.symm

end Corellzk2smt.SymExec.ProgCorrectness
