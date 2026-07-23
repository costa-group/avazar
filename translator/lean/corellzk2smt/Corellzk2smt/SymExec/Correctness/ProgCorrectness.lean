import Corellzk2smt.SymExec.Correctness.FuncCorrectness
import Corellzk2smt.SymExec.Correctness.SimpleCmdCorrectness
import Corellzk2smt.Language.Core.Analysis.DefinedVars
import Corellzk2smt.Language.Core.Syntax.Lemmas

/-
This file merges what used to be two files: `SymExec/ProgCorrectness.lean` ("shared machinery"
for whole-program correctness: `seFunc_f_name_eq`, `fetchFunc_skip_ne`, `evalFunCall_congr`,
`seFuncCall_names_below`, and the two purely-structural inductions over `seExecFuncs.loop`'s own
recursion -- `seExecFuncs_loop_specs_suffix` (the spec accumulator only ever grows by prepending)
and `seExecFuncs_loop_params_split` (every macro's `params : List Var` field decomposes into a
params range / a rets range / an opaque aux list, exposing `seFunc_f_params_split_basic`'s per-
function fact at the whole-program level), none of it stated in terms of `TranslatesCorrectly`)
and `SymExec/Correctness/ProgCorrectness.lean` (`seExecFuncs_loop_correct`/
`seExecFuncs_correct`, and the final top-level theorem `seExecProg_call_correct`, built on top).
They were separate because the shared machinery was meant to be reusable by both an unconditional
and a conditional (`TranslatesCorrectly`) formalization; the unconditional one was deleted once
the conditional one fully superseded it, leaving the split purely historical -- merged back into
one file/namespace now that there's only one consumer.

Partial-correctness analogue of whole-program correctness for `seExecFuncs`/`seExecProg`, built on
the conditional `seFunc_correct`/`seFuncCall_correct_via_seFunc` (earlier in this same file, was
`Correctness/FuncCorrectness.lean`).

Three genuine (not merely mechanical) changes from the old file, per the session's investigation
into what the conditional `TranslatesCorrectly` actually buys at the whole-program level:

1. `H_simple` drops out as a *parameter* entirely, replaced by `H_simple_holds`
   (`SimpleCmdCorrectness.lean`) -- kept as a theorem (not reintroduced as an assumed parameter)
   so every call site still just invokes it by name, but its proof is an honest `sorry`:
   `seSimpleCmd` is currently a permanent `"TBD"` stub,
   so it *could* be discharged vacuously (the success hypothesis inside `TranslatesCorrectly` can
   never fire), but proving it that way would be proving the wrong thing -- true only because
   nothing is implemented yet, not because simple commands actually translate correctly. Leaving
   it a `sorry` keeps that gap visible, and keeps every consumer routing through this one
   statement of `TranslatesCorrectly` for `seSimpleCmd`/`evalSimpleCmd` instead of ever unfolding
   `seSimpleCmd` directly to reach its error case.

2. [REMOVED 2026] `WellShapedCom`/`WellShapedCmds`/`WellShapedProg`/`WellShapedProgBodies` and
   every `hshaped`/`hwsp` *parameter* are gone entirely -- both the definitions themselves
   (`Language/Core/Analysis/WellShaped.lean` deleted) and every parameter threaded from them, all
   the way from `seIfStmt_correct`/`seCmd_correct`/`seCmds_correct` (`Correctness/Lemmas.lean`'s
   mutual block) up through `FuncCorrectness.lean` to this file's own
   `seExecFuncs_loop_correct`/`seExecFuncs_correct`/`seExecProg_call_correct` -- no caller anywhere
   has to prove or thread down a well-shapedness fact. The predicate had been kept around
   (parameter still real, but always trivially provable) past the point it stopped asserting
   anything, specifically because removing it from that one mutual block previously triggered a
   severe elaborator blowup (see `feedback_lean_slow_build_diagnosis`); the actual fix turned out
   to be replacing a few `by grind` calls inside that block's `decreasing_by` (proving simple facts
   like `a ≤ a + b`) with direct proof terms once the surrounding context got large enough for
   `grind`'s search to blow up -- not a fundamental obstruction to removing the parameter itself.
   Whole-program pairwise function-name uniqueness is given directly by `hasDupFuncNames` (already
   threaded into every relevant theorem, see `FuncCorrectness.lean`/`FuncCallCorrectness.lean`);
   `hasDupFuncNames_cons_disjoint` (below) recovers the one specific disjointness fact the
   induction actually consumes (`hBdisj`) from it.

3. `H_domain` and `H_shape` no longer exist as parameters anywhere in this whole chain -- both
   turned out to be false as originally stated (blanket-quantified over arbitrary, unrelated
   command lists/environments), and both are now discharged internally instead:
   - `H_shape`'s correctly-scoped, per-if-statement replacement is derived inline inside
     `seIfStmt_correct` (`Correctness/Correctness.lean`), straight from `mergeSymEnv`'s own
     success via `sameShape_of_symValMatches` (`SymExec/Lemmas.lean`).
   - `H_domain`'s replacement, `seCmds_domain_of_defined`/`seCmd_domain_of_defined`/
     `seIfStmt_domain_of_defined` (`SymExec/Lemmas.lean`), needs an extra premise (every variable
     a command could write is already in the environment's domain, phrased over
     `definedVarsCom`/`definedVarsCmds`, `Language/Core/Analysis/DefinedVars.lean`) -- so
     `seCmd_correct`/`seCmds_correct`/`seIfStmt_correct` gained a `vars : VarIDSet` parameter and
     their conclusion changed from plain `TranslatesCorrectly` to `TranslatesCorrectlyGiven ...
     guard ...` (`Correctness/Lemmas.lean`), threading that premise through their own
     recursion. `seFunc_correct` (earlier in this same file) discharges the premise itself, using
     `zeroSymEnv_contains`/`mintFreshParams_contains_mono` (also earlier in this same file) to
     show its own `inSymEnv` construction already satisfies it -- so nothing needs threading any
     further up than that, and `H_domain` is gone by the time whole-program level (this file) is
     reached.

4. `seExecFuncs_loop_correct`/`_correct` carry a *second* per-function fact (`hSpecC`) alongside
   the original generic `TranslatesCorrectly` one (`hHfc`): `hspec_retsShape`/`H_specCorrect`
   (the pair `seFunc_correct` produces) restated against the *final* `specs.map (·.f)` list, using
   the same easy "these two names differ" lift `hHfc` already used (`H_specCorrect`'s formula is
   always a bare `.call` leaf, never the function body itself). This is what lets
   `seExecProg_call_correct` (the actual top-level theorem this file builds toward -- see its own
   header) relate an arbitrary assignment's satisfaction of a macro call directly to a concrete
   `evalFunCall` execution, without going through `seFuncCall`/`evalFuncCallCmd` at all.
   `seExecProg_correct` (the old wrapper that only exposed `hHfc`) was deleted once
   `seExecProg_call_correct` made it fully redundant -- nothing called it, and everything it
   proved was either subsumed by `seExecFuncs_correct` or re-derived independently anyway.
-/

namespace Corellzk2smt.SymExec.Correctness.ProgCorrectness

open Corellzk2smt.Config
open Corellzk2smt.Language.Core.Syntax.AST
open Corellzk2smt.Language.Core.Syntax.Lemmas
open Corellzk2smt.Language.Core.Semantics.Basic
open Corellzk2smt.Language.Core.Semantics.BigStep
open Corellzk2smt.Language.Core.Analysis.DefinedVars
open Corellzk2smt.SymExec.Basic
open Corellzk2smt.SymExec.BigStep
open Corellzk2smt.FFConstraints.Basic
open Corellzk2smt.FFConstraints.Satisfiability
open Corellzk2smt.FFConstraints.Lemmas
open Corellzk2smt.SymExec.Correctness.Lemmas
open Corellzk2smt.SymExec.Correctness.FuncCorrectness
open Corellzk2smt.SymExec.Correctness.FuncCallCorrectness
open Corellzk2smt.SymExec.Correctness.SimpleCmdCorrectness

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

-- ---------------------------------------------------------------------------
-- seExecFuncs_loop_correct / seExecFuncs_correct / seExecProg_call_correct
-- ---------------------------------------------------------------------------

/-- The one disjointness fact `seExecFuncs_loop_correct`'s induction actually needs (`hBdisj` in
    the old proof): if a function-list has no duplicate names, its head's name is disjoint from
    every name in the tail. Recovers, from `hasDupFuncNames` alone, exactly what the old proof
    got from `WellShapedProg_head_after_prefix`'s `hBdisj` component. -/
theorem hasDupFuncNames_cons_disjoint {c : ZKConfig} (f : FuncWithMD c) (rest : Prog c)
    (h : hasDupFuncNames (f :: rest) = false) :
    ∀ f' ∈ rest, funcWithMDName f' ≠ funcWithMDName f := by
  simp only [hasDupFuncNames, List.map_cons, hasDupNames, Bool.or_eq_false_iff] at h
  intro f' hf' heq
  have hmem : funcWithMDName f ∈ rest.map funcWithMDName := by
    rw [← heq]; exact List.mem_map_of_mem hf'
  have hcontains : (rest.map funcWithMDName).contains (funcWithMDName f) = true := by
    rw [List.contains_iff_mem]; exact hmem
  rw [h.1] at hcontains
  exact absurd hcontains (by simp)

/-- `TranslatesCorrectly` (conditional form) only ever consumes `concrete`/`symbolic` through
    pointwise application, so equal-as-functions replacements carry a fact across -- identical
    proof to the old `SymExec.ProgCorrectness.TranslatesCorrectly_congr`, restated for the new
    `TranslatesCorrectly`. -/
theorem TranslatesCorrectly_congr {c : ZKConfig} (gconf : GlobalConfig c) (sconf : SymExecConfig c)
    (specs : List (FuncSpec c)) (concrete1 concrete2 : Env c → Except String (Env c))
    (symbolic1 symbolic2 : SymEnv c → Except String (CmdsSpec c))
    (hconcrete : ∀ env, concrete1 env = concrete2 env)
    (hsymbolic : ∀ symEnv, symbolic1 symEnv = symbolic2 symEnv)
    (h : TranslatesCorrectly gconf sconf specs concrete1 symbolic1) :
    TranslatesCorrectly gconf sconf specs concrete2 symbolic2 := by
  have hc : concrete1 = concrete2 := funext hconcrete
  have hs : symbolic1 = symbolic2 := funext hsymbolic
  rw [hc, hs] at h
  exact h

/-- Conditional-form analogue of `SymExec.Correctness.TranslatesCorrectly_prepend`: if
    `concrete`/`symbolic` translate correctly (given success) against `specs`, they still do
    against `fspec_new :: specs`, given `fspec_new`'s name is disjoint from every spec already in
    `specs` and every formula `symbolic` can ever produce never directly calls `fspec_new.f.name`.
    The proof mirrors the old one exactly, except `h`'s conditional form takes `spec`/`hsym` as
    given rather than producing them existentially, so there is no `obtain ⟨spec, hsym, ...⟩`
    step -- applying `h symEnv hvarSetBelow spec hsym` directly yields the conjuncts. -/
theorem TranslatesCorrectly_prepend {c : ZKConfig} (gconf : GlobalConfig c)
    (sconf : SymExecConfig c) (specs : List (FuncSpec c)) (fspec_new : FuncSpec c)
    (hne : ∀ spec ∈ specs, fspec_new.f.name ≠ spec.f.name)
    (concrete : Env c → Except String (Env c))
    (symbolic : SymEnv c → Except String (CmdsSpec c))
    (hnb : ∀ (symEnv : SymEnv c) (spec : CmdsSpec c), symbolic symEnv = Except.ok spec →
      FormulaNamesBelow spec.f fspec_new.f.name)
    (h : TranslatesCorrectly gconf sconf specs concrete symbolic) :
    TranslatesCorrectly gconf sconf (fspec_new :: specs) concrete symbolic := by
  intro symEnv hvarSetBelow spec hsym
  obtain ⟨hin, hnext, hspecVars1, hspecVars2, houtVars1, houtVars2, hsound, hcomplete⟩ :=
    h symEnv hvarSetBelow spec hsym
  have hnb_spec := hnb symEnv spec hsym
  have hmap : ((fspec_new :: specs).map (·.f) : List (FFMacro c)) =
      fspec_new.f :: specs.map (·.f) := List.map_cons ..
  refine ⟨hin, hnext, hspecVars1, hspecVars2, houtVars1, houtVars2, ?_, ?_⟩
  · intro env assignment hmatch env' hconcrete
    obtain ⟨assignment', hagreeFF, hagreeBool, hffout, hboolout, hformula, hmatch'⟩ :=
      hsound env assignment hmatch env' hconcrete
    refine ⟨assignment', hagreeFF, hagreeBool, hffout, hboolout, ?_, hmatch'⟩
    rw [hmap]
    exact evalFormula_prepend_indep gconf [fspec_new.f] assignment' spec.f (specs.map (·.f)) true
      (fun m hm m' hm' => by
        simp only [List.mem_singleton] at hm
        obtain ⟨spec', hspec'mem, hspec'eq⟩ := List.mem_map.mp hm'
        exact hspec'eq ▸ (hm ▸ hne spec' hspec'mem))
      hformula
  · intro env assignment hmatch assignment' hagreeFF hformula
    rw [hmap] at hformula
    exact hcomplete env assignment hmatch assignment'
      hagreeFF (evalFormula_names_below_indep gconf fspec_new.f (specs.map (·.f)) assignment'
        spec.f true hnb_spec hformula)

/-- The core induction: `seExecFuncs`'s `loop`, generalized over an explicit `donePart` -- see
    `SymExec.ProgCorrectness.seExecFuncs_loop_correct`'s header for the invariant. `H_simple` is
    no longer a parameter (see `H_simple_holds`); no well-shapedness hypothesis is needed at all
    (see this file's header, point 2), with the disjointness fact the old proof needed for this
    coming from `hasDupFuncNames` instead. -/
theorem seExecFuncs_loop_correct {c : ZKConfig} (gconf : GlobalConfig c) :
    ∀ (funcs donePart : Prog c) (specs : List (FuncSpec c)),
      hasDupFuncNames (funcs.reverse ++ donePart) = false →
      (∀ spec ∈ specs, spec.f.name = spec.name) →
      specs.map (·.name) = donePart.map funcWithMDName →
      (∀ fname'' fspec', fetchFuncSpec specs fname'' = Except.ok fspec' →
        ∀ md func p'', fetchFunc donePart fname'' = Except.ok (FuncWithMD.mk md func, p'') →
          match func with | Func.mk _ _ rets _ => fspec'.rets.length = rets.length) →
      (∀ (sconf : SymExecConfig c) (fname' : FName) (args : List (SimpleExpr c))
          (outs : List VarID) (md' : FuncMD) (func' : Func c) (p'' : Prog c),
        fetchFunc donePart fname' = Except.ok (FuncWithMD.mk md' func', p'') →
        (match func' with | Func.mk _ _ rets _ => outs.length = rets.length) →
        TranslatesCorrectly gconf sconf specs
          (fun env => evalFuncCallCmd gconf donePart fname' args outs env)
          (fun symEnv => seFuncCall gconf sconf symEnv specs fname' args outs)) →
      (∀ (fname' : FName) (md' : FuncMD) (func' : Func c) (p'' : Prog c),
        fetchFunc donePart fname' = Except.ok (FuncWithMD.mk md' func', p'') →
        ∀ fspec' : FuncSpec c, fetchFuncSpec specs fname' = Except.ok fspec' →
          (∃ (retsOffset : Nat) (auxVarsList : List Var),
            fspec'.f.params =
              (List.range (totalParamSize fspec'.params)).map (fun i => Var.ffv i) ++
              (List.range (totalParamSize fspec'.rets)).map (fun i => Var.ffv (retsOffset + i)) ++
              auxVarsList ∧
            totalParamSize fspec'.params ≤ retsOffset ∧
            (auxVarsList.filter isFFvVar).length = fspec'.numAuxFFVars ∧
            (auxVarsList.filter (fun v => !isFFvVar v)).length = fspec'.numAuxBoolVars ∧
            auxVarsList.Pairwise (fun a b => compare a b = .lt) ∧
            (∀ v ∈ auxVarsList, ∀ n, v = Var.ffv n →
              ¬(n < totalParamSize fspec'.params) ∧
              ¬(retsOffset ≤ n ∧ n < retsOffset + totalParamSize fspec'.rets))) ∧
          (∀ argVals, ValuesMatchParams argVals fspec'.params → ∀ outVals,
            evalFunCall gconf donePart fname' argVals = Except.ok outVals →
            ValuesMatchParams outVals fspec'.rets) ∧
          (∀ argVals, ValuesMatchParams argVals fspec'.params →
            (∀ retVals, evalFunCall gconf donePart fname' argVals = Except.ok retVals →
              ValuesMatchParams retVals fspec'.rets ∧
              ∃ (auxFF : List (FF c)) (auxBool : List Bool),
                auxFF.length = fspec'.numAuxFFVars ∧ auxBool.length = fspec'.numAuxBoolVars ∧
                ∀ assign, evalFormula gconf assign
                  (FFFormula.call fspec'.f.name
                    (flattenValuesParams argVals ++ flattenValuesParams retVals ++
                     auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
                     auxBool.map (fun v => MacroCallParam.const (Const.boolc v))))
                  (specs.map (·.f)) = Except.ok true) ∧
            (∀ (retVals : List (Value c)) (auxFF : List (FF c)) (auxBool : List Bool),
              ValuesMatchParams retVals fspec'.rets →
              auxFF.length = fspec'.numAuxFFVars → auxBool.length = fspec'.numAuxBoolVars →
              (∀ assign, evalFormula gconf assign
                (FFFormula.call fspec'.f.name
                  (flattenValuesParams argVals ++ flattenValuesParams retVals ++
                   auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
                   auxBool.map (fun v => MacroCallParam.const (Const.boolc v))))
                (specs.map (·.f)) = Except.ok true) →
              evalFunCall gconf donePart fname' argVals = Except.ok retVals))) →
      ∀ (newSpecs : List (FuncSpec c)),
        seExecFuncs.loop gconf funcs specs = Except.ok newSpecs →
        (∀ spec ∈ newSpecs, spec.f.name = spec.name) ∧
        newSpecs.map (·.name) = (funcs.reverse ++ donePart).map funcWithMDName ∧
        (∀ fname'' fspec', fetchFuncSpec newSpecs fname'' = Except.ok fspec' →
          ∀ md func p'', fetchFunc (funcs.reverse ++ donePart) fname'' =
              Except.ok (FuncWithMD.mk md func, p'') →
            match func with | Func.mk _ _ rets _ => fspec'.rets.length = rets.length) ∧
        (∀ (sconf : SymExecConfig c) (fname' : FName) (args : List (SimpleExpr c))
            (outs : List VarID) (md' : FuncMD) (func' : Func c) (p'' : Prog c),
          fetchFunc (funcs.reverse ++ donePart) fname' =
              Except.ok (FuncWithMD.mk md' func', p'') →
          (match func' with | Func.mk _ _ rets _ => outs.length = rets.length) →
          TranslatesCorrectly gconf sconf newSpecs
            (fun env => evalFuncCallCmd gconf (funcs.reverse ++ donePart) fname' args outs env)
            (fun symEnv => seFuncCall gconf sconf symEnv newSpecs fname' args outs)) ∧
        (∀ (fname' : FName) (md' : FuncMD) (func' : Func c) (p'' : Prog c),
          fetchFunc (funcs.reverse ++ donePart) fname' =
              Except.ok (FuncWithMD.mk md' func', p'') →
          ∀ fspec' : FuncSpec c, fetchFuncSpec newSpecs fname' = Except.ok fspec' →
            (∃ (retsOffset : Nat) (auxVarsList : List Var),
              fspec'.f.params =
                (List.range (totalParamSize fspec'.params)).map (fun i => Var.ffv i) ++
                (List.range (totalParamSize fspec'.rets)).map
                  (fun i => Var.ffv (retsOffset + i)) ++
                auxVarsList ∧
              totalParamSize fspec'.params ≤ retsOffset ∧
              (auxVarsList.filter isFFvVar).length = fspec'.numAuxFFVars ∧
              (auxVarsList.filter (fun v => !isFFvVar v)).length = fspec'.numAuxBoolVars ∧
              auxVarsList.Pairwise (fun a b => compare a b = .lt) ∧
              (∀ v ∈ auxVarsList, ∀ n, v = Var.ffv n →
                ¬(n < totalParamSize fspec'.params) ∧
                ¬(retsOffset ≤ n ∧ n < retsOffset + totalParamSize fspec'.rets))) ∧
            (∀ argVals, ValuesMatchParams argVals fspec'.params → ∀ outVals,
              evalFunCall gconf (funcs.reverse ++ donePart) fname' argVals = Except.ok outVals →
              ValuesMatchParams outVals fspec'.rets) ∧
            (∀ argVals, ValuesMatchParams argVals fspec'.params →
              (∀ retVals,
                evalFunCall gconf (funcs.reverse ++ donePart) fname' argVals = Except.ok retVals →
                ValuesMatchParams retVals fspec'.rets ∧
                ∃ (auxFF : List (FF c)) (auxBool : List Bool),
                  auxFF.length = fspec'.numAuxFFVars ∧ auxBool.length = fspec'.numAuxBoolVars ∧
                  ∀ assign, evalFormula gconf assign
                    (FFFormula.call fspec'.f.name
                      (flattenValuesParams argVals ++ flattenValuesParams retVals ++
                       auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
                       auxBool.map (fun v => MacroCallParam.const (Const.boolc v))))
                    (newSpecs.map (·.f)) = Except.ok true) ∧
              (∀ (retVals : List (Value c)) (auxFF : List (FF c)) (auxBool : List Bool),
                ValuesMatchParams retVals fspec'.rets →
                auxFF.length = fspec'.numAuxFFVars → auxBool.length = fspec'.numAuxBoolVars →
                (∀ assign, evalFormula gconf assign
                  (FFFormula.call fspec'.f.name
                    (flattenValuesParams argVals ++ flattenValuesParams retVals ++
                     auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
                     auxBool.map (fun v => MacroCallParam.const (Const.boolc v))))
                  (newSpecs.map (·.f)) = Except.ok true) →
                evalFunCall gconf (funcs.reverse ++ donePart) fname' argVals =
                  Except.ok retVals))) := by
  intro funcs
  induction funcs with
  | nil =>
      intro donePart specs _hnodup hspecs_wf hnames_corr hrets_corr hHfc hSpecC newSpecs
        hloop_eq
      simp only [List.reverse_nil, List.nil_append] at hloop_eq ⊢
      simp only [seExecFuncs.loop] at hloop_eq
      injection hloop_eq with hloop_eq
      exact ⟨hloop_eq ▸ hspecs_wf, hloop_eq ▸ hnames_corr, hloop_eq ▸ hrets_corr, hloop_eq ▸ hHfc,
        hloop_eq ▸ hSpecC⟩
  | cons func funcs' ih =>
      intro donePart specs hnodup hspecs_wf hnames_corr hrets_corr hHfc hSpecC newSpecs
        hloop_eq
      obtain ⟨md, name, params, rets, body⟩ := func
      have hlist_eq : (FuncWithMD.mk md (Func.mk name params rets body) :: funcs').reverse ++
          donePart =
          funcs'.reverse ++ (FuncWithMD.mk md (Func.mk name params rets body) :: donePart) := by
        simp [List.reverse_cons, List.append_assoc]
      rw [hlist_eq] at hnodup ⊢
      have hnodup_head : hasDupFuncNames
          (FuncWithMD.mk md (Func.mk name params rets body) :: donePart) = false :=
        hasDupFuncNames_append_right funcs'.reverse _ hnodup
      have hnodup_donePart : hasDupFuncNames donePart = false :=
        hasDupFuncNames_cons_tail _ _ hnodup_head
      simp only [seExecFuncs.loop] at hloop_eq
      cases hseFunc_eq : seFunc gconf specs (Func.mk name params rets body) with
      | error e =>
        rw [hseFunc_eq] at hloop_eq
        simp only [Bind.bind, Except.bind] at hloop_eq
        exact absurd hloop_eq (by simp)
      | ok fspec =>
        rw [hseFunc_eq] at hloop_eq
        simp only [Bind.bind, Except.bind] at hloop_eq
        have hBdisj : ∀ f ∈ donePart,
            funcWithMDName f ≠ funcWithMDName (FuncWithMD.mk md (Func.mk name params rets body)) :=
          hasDupFuncNames_cons_disjoint _ donePart hnodup_head
        have hname_eq2 : funcWithMDName (FuncWithMD.mk md (Func.mk name params rets body)) =
            name := rfl
        rw [hname_eq2] at hBdisj
        have hfname_eq : fspec.f.name = name :=
          seFunc_f_name_eq gconf specs name params rets body fspec hseFunc_eq
        obtain ⟨hname_eq, hparams_eq, hrets_eq⟩ := seFunc_eq_shape gconf specs name params rets
          body fspec hseFunc_eq
        have hspecs_wf' : ∀ spec ∈ fspec :: specs, spec.f.name = spec.name := by
          intro spec hspec
          rcases List.mem_cons.mp hspec with hspec | hspec
          · rw [hspec, hfname_eq, hname_eq]
          · exact hspecs_wf spec hspec
        have hnames_corr' : (fspec :: specs).map (·.name) =
            (FuncWithMD.mk md (Func.mk name params rets body) :: donePart).map funcWithMDName :=
          by simp only [List.map_cons, hname_eq, funcWithMDName, hnames_corr]
        have hne_specs : ∀ spec ∈ specs, fspec.f.name ≠ spec.f.name := by
          intro spec hspec heq
          have hspecname_mem : spec.name ∈ specs.map (·.name) := List.mem_map_of_mem hspec
          rw [hnames_corr] at hspecname_mem
          obtain ⟨f, hfmem, hfeq⟩ := List.mem_map.mp hspecname_mem
          have hspec_wf := hspecs_wf spec hspec
          apply hBdisj f hfmem
          rw [hfeq, ← hspec_wf, ← heq, hfname_eq]
        have hspecs_cover_here : ∀ fname'', fname'' ∈ specs.map (·.name) →
            fname'' ∈ donePart.map funcWithMDName := fun _ h => hnames_corr ▸ h
        have hrets_corr' : ∀ fname'' fspec', fetchFuncSpec (fspec :: specs) fname'' =
              Except.ok fspec' →
            ∀ md'' func p'', fetchFunc
                (FuncWithMD.mk md (Func.mk name params rets body) :: donePart) fname'' =
                Except.ok (FuncWithMD.mk md'' func, p'') →
              match func with | Func.mk _ _ rs _ => fspec'.rets.length = rs.length := by
          intro fname'' fspec' hspec'_eq md'' func p'' hfetch'
          simp only [fetchFunc] at hfetch'
          by_cases hcase : name = fname''
          · subst hcase
            simp only [BEq.rfl, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hfetch'
            obtain ⟨hfeq, _hpeq⟩ := hfetch'
            injection hfeq with _hmdeq hfunceq
            rw [← hfunceq]
            simp only []
            have hfspec_eq : fetchFuncSpec (fspec :: specs) name = Except.ok fspec := by
              simp [fetchFuncSpec, hname_eq]
            have hfspec'_fspec : fspec' = fspec := by
              have heqq := hspec'_eq.symm.trans hfspec_eq
              injection heqq
            rw [hfspec'_fspec]
            exact congrArg List.length hrets_eq
          · have hbeq : (name == fname'') = false := by simpa using hcase
            simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at hfetch'
            have hspec'_eq_old : fetchFuncSpec specs fname'' = Except.ok fspec' := by
              rwa [fetchFuncSpec_prepend_indep fspec specs fname'' (hname_eq ▸ hcase)] at hspec'_eq
            exact hrets_corr fname'' fspec' hspec'_eq_old md'' func p'' hfetch'
        -- H_funcCall for (thisFunc :: donePart) / (fspec :: specs)
        have hHfc' : ∀ (sconf : SymExecConfig c) (fname' : FName) (args : List (SimpleExpr c))
            (outs : List VarID) (md' : FuncMD) (func'' : Func c) (p'' : Prog c),
            fetchFunc (FuncWithMD.mk md (Func.mk name params rets body) :: donePart) fname' =
                Except.ok (FuncWithMD.mk md' func'', p'') →
            (match func'' with | Func.mk _ _ rs _ => outs.length = rs.length) →
            TranslatesCorrectly gconf sconf (fspec :: specs)
              (fun env => evalFuncCallCmd gconf
                (FuncWithMD.mk md (Func.mk name params rets body) :: donePart) fname' args outs
                env)
              (fun symEnv => seFuncCall gconf sconf symEnv (fspec :: specs) fname' args outs) := by
          intro sconf fname' args outs md'' func'' p'' hfetch houtlen
          simp only [fetchFunc] at hfetch
          by_cases hcase : name = fname'
          · subst hcase
            simp only [BEq.rfl, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hfetch
            obtain ⟨hfeq, hpeq⟩ := hfetch
            injection hfeq with hmdeq hfunceq
            exact seFuncCall_correct_via_seFunc gconf (FuncWithMD.mk md
                (Func.mk name params rets body) :: donePart) specs sconf name md
              (Func.mk name params rets body) donePart
              (by simp only [fetchFunc, BEq.rfl, ↓reduceIte])
              hnodup_head
              (H_simple_holds gconf specs) hHfc hspecs_cover_here hrets_corr hspecs_wf
              fspec hseFunc_eq args outs
          · have hbeq : (name == fname') = false := by simpa using hcase
            simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at hfetch
            have hspec_old := hHfc sconf fname' args outs md'' func'' p'' hfetch houtlen
            have hnb : ∀ (symEnv : SymEnv c) (spec : CmdsSpec c),
                seFuncCall gconf sconf symEnv specs fname' args outs = Except.ok spec →
                FormulaNamesBelow spec.f fspec.f.name :=
              fun symEnv spec heq =>
                seFuncCall_names_below gconf sconf symEnv specs fname' args outs fspec.f.name
                  (by rw [hfname_eq]; exact hcase) hspecs_wf spec heq
            have hlifted := TranslatesCorrectly_prepend gconf sconf specs fspec hne_specs _ _
              hnb hspec_old
            apply TranslatesCorrectly_congr gconf sconf (fspec :: specs) _ _ _ _ ?_ ?_ hlifted
            · intro env
              simp only [evalFuncCallCmd]
              cases evalSimpleExprsToValue env args with
              | error e => rfl
              | ok argVals =>
                  simp only []
                  rw [evalFunCall_congr gconf
                    (FuncWithMD.mk md (Func.mk name params rets body) :: donePart) donePart
                    fname' (fetchFunc_skip_ne (FuncWithMD.mk md (Func.mk name params rets body))
                      donePart fname' (by rw [hname_eq2]; exact hcase))
                    hnodup_head hnodup_donePart argVals]
            · intro symEnv
              exact (seFuncCall_prepend_indep gconf sconf symEnv fspec specs fname' args outs
                (by rw [hname_eq]; exact hcase)).symm
        -- H_specCorrect for (thisFunc :: donePart) / (fspec :: specs) -- mirrors `hHfc'` above,
        -- except the fact being carried is per-*function* (`fetchFuncSpec`), not per-*call-site*,
        -- and its formula is always a bare `.call fspec'.f.name` leaf, so lifting it past the
        -- newly-prepended `fspec.f` is direct (`evalFormula_prepend_indep`/
        -- `evalFormula_names_below_indep`), reusing exactly `hne_specs` -- no need for
        -- `seFunc_correct`'s own `FormulaNamesBelow fspec.f.body` fact at all.
        have hSpecC' : ∀ (fname' : FName) (md' : FuncMD) (func'' : Func c) (p'' : Prog c),
            fetchFunc (FuncWithMD.mk md (Func.mk name params rets body) :: donePart) fname' =
                Except.ok (FuncWithMD.mk md' func'', p'') →
            ∀ fspec' : FuncSpec c, fetchFuncSpec (fspec :: specs) fname' = Except.ok fspec' →
              (∃ (retsOffset : Nat) (auxVarsList : List Var),
                fspec'.f.params =
                  (List.range (totalParamSize fspec'.params)).map (fun i => Var.ffv i) ++
                  (List.range (totalParamSize fspec'.rets)).map
                    (fun i => Var.ffv (retsOffset + i)) ++
                  auxVarsList ∧
                totalParamSize fspec'.params ≤ retsOffset ∧
                (auxVarsList.filter isFFvVar).length = fspec'.numAuxFFVars ∧
                (auxVarsList.filter (fun v => !isFFvVar v)).length = fspec'.numAuxBoolVars ∧
                auxVarsList.Pairwise (fun a b => compare a b = .lt) ∧
                (∀ v ∈ auxVarsList, ∀ n, v = Var.ffv n →
                  ¬(n < totalParamSize fspec'.params) ∧
                  ¬(retsOffset ≤ n ∧ n < retsOffset + totalParamSize fspec'.rets))) ∧
              (∀ argVals, ValuesMatchParams argVals fspec'.params → ∀ outVals,
                evalFunCall gconf
                  (FuncWithMD.mk md (Func.mk name params rets body) :: donePart) fname' argVals =
                  Except.ok outVals →
                ValuesMatchParams outVals fspec'.rets) ∧
              (∀ argVals, ValuesMatchParams argVals fspec'.params →
                (∀ retVals,
                  evalFunCall gconf
                    (FuncWithMD.mk md (Func.mk name params rets body) :: donePart) fname' argVals =
                    Except.ok retVals →
                  ValuesMatchParams retVals fspec'.rets ∧
                  ∃ (auxFF : List (FF c)) (auxBool : List Bool),
                    auxFF.length = fspec'.numAuxFFVars ∧ auxBool.length = fspec'.numAuxBoolVars ∧
                    ∀ assign, evalFormula gconf assign
                      (FFFormula.call fspec'.f.name
                        (flattenValuesParams argVals ++ flattenValuesParams retVals ++
                         auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
                         auxBool.map (fun v => MacroCallParam.const (Const.boolc v))))
                      ((fspec :: specs).map (·.f)) = Except.ok true) ∧
                (∀ (retVals : List (Value c)) (auxFF : List (FF c)) (auxBool : List Bool),
                  ValuesMatchParams retVals fspec'.rets →
                  auxFF.length = fspec'.numAuxFFVars → auxBool.length = fspec'.numAuxBoolVars →
                  (∀ assign, evalFormula gconf assign
                    (FFFormula.call fspec'.f.name
                      (flattenValuesParams argVals ++ flattenValuesParams retVals ++
                       auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
                       auxBool.map (fun v => MacroCallParam.const (Const.boolc v))))
                    ((fspec :: specs).map (·.f)) = Except.ok true) →
                  evalFunCall gconf
                    (FuncWithMD.mk md (Func.mk name params rets body) :: donePart) fname' argVals =
                    Except.ok retVals)) := by
          intro fname' md'' func'' p'' hfetch fspec' hspec'_eq
          simp only [fetchFunc] at hfetch
          by_cases hcase : name = fname'
          · subst hcase
            have hfspec_eq : fetchFuncSpec (fspec :: specs) name = Except.ok fspec := by
              simp [fetchFuncSpec, hname_eq]
            have hfspec'_fspec : fspec' = fspec := by
              have heqq := hspec'_eq.symm.trans hfspec_eq
              injection heqq
            rw [hfspec'_fspec]
            have hparams_split_new :=
              seFunc_f_params_split gconf
                (FuncWithMD.mk md (Func.mk name params rets body) :: donePart) specs name md
                (Func.mk name params rets body) donePart
                (by simp only [fetchFunc, BEq.rfl, ↓reduceIte])
                (H_simple_holds gconf specs) hHfc hspecs_cover_here hrets_corr fspec
                hseFunc_eq
            obtain ⟨hspec_retsShape, _hnamesBelow, H_specCorrect⟩ :=
              seFunc_correct gconf (FuncWithMD.mk md (Func.mk name params rets body) :: donePart)
                specs name md (Func.mk name params rets body) donePart
                (by simp only [fetchFunc, BEq.rfl, ↓reduceIte])
                hnodup_head (H_simple_holds gconf specs) hHfc hspecs_cover_here hrets_corr
                hspecs_wf fspec hseFunc_eq
            refine ⟨hparams_split_new, hspec_retsShape, ?_⟩
            simpa only [List.map_cons] using H_specCorrect
          · have hbeq : (name == fname') = false := by simpa using hcase
            simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at hfetch
            have hspec'_eq_old : fetchFuncSpec specs fname' = Except.ok fspec' := by
              rwa [fetchFuncSpec_prepend_indep fspec specs fname' (hname_eq ▸ hcase)] at hspec'_eq
            obtain ⟨hparams_split_old, hspec_retsShape_old, H_specCorrect_old⟩ :=
              hSpecC fname' md'' func'' p'' hfetch fspec' hspec'_eq_old
            have hfspec'_mem : fspec' ∈ specs :=
              (fetchFuncSpec_sound specs fname' fspec' hspec'_eq_old).2
            have hne_call : fspec.f.name ≠ fspec'.f.name := hne_specs fspec' hfspec'_mem
            have hcongr : ∀ (argVals : List (Value c)),
                evalFunCall gconf
                  (FuncWithMD.mk md (Func.mk name params rets body) :: donePart) fname' argVals =
                  evalFunCall gconf donePart fname' argVals := fun argVals =>
              evalFunCall_congr gconf
                (FuncWithMD.mk md (Func.mk name params rets body) :: donePart) donePart fname'
                (fetchFunc_skip_ne (FuncWithMD.mk md (Func.mk name params rets body)) donePart
                  fname' (by rw [hname_eq2]; exact hcase))
                hnodup_head hnodup_donePart argVals
            refine ⟨hparams_split_old, ?_, ?_⟩
            · intro argVals hargVals outVals hev
              rw [hcongr argVals] at hev
              exact hspec_retsShape_old argVals hargVals outVals hev
            · intro argVals hargVals
              obtain ⟨hforward_old, hbackward_old⟩ := H_specCorrect_old argVals hargVals
              refine ⟨?_, ?_⟩
              · intro retVals hev
                rw [hcongr argVals] at hev
                obtain ⟨hshape, auxFF, auxBool, hauxFF_len, hauxBool_len, hformula⟩ :=
                  hforward_old retVals hev
                refine ⟨hshape, auxFF, auxBool, hauxFF_len, hauxBool_len, ?_⟩
                intro assign
                rw [List.map_cons]
                exact evalFormula_prepend_indep gconf [fspec.f] assign _ (specs.map (·.f)) true
                  (fun m hm m' hm' => by
                    simp only [List.mem_singleton] at hm
                    subst hm
                    obtain ⟨spec, hspec_mem, hspec_eq2⟩ := List.mem_map.mp hm'
                    rw [← hspec_eq2]
                    exact hne_specs spec hspec_mem)
                  (hformula assign)
              · intro retVals auxFF auxBool hshape hauxFF_len hauxBool_len hformula_big
                rw [hcongr argVals]
                refine hbackward_old retVals auxFF auxBool hshape hauxFF_len hauxBool_len ?_
                intro assign
                have hbig := hformula_big assign
                rw [List.map_cons] at hbig
                have hnb : FormulaNamesBelow
                    (FFFormula.call fspec'.f.name
                      (flattenValuesParams argVals ++ flattenValuesParams retVals ++
                       auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
                       auxBool.map (fun v => MacroCallParam.const (Const.boolc v))))
                    fspec.f.name := by
                  simp only [FormulaNamesBelow]
                  exact fun heq => hne_call heq.symm
                exact evalFormula_names_below_indep gconf fspec.f (specs.map (·.f)) assign _ true
                  hnb hbig
        obtain ⟨hnewSpecs_wf, hnewSpecs_names, hnewSpecs_rets, hnewSpecs_Hfc, hnewSpecs_SpecC⟩ :=
          ih (FuncWithMD.mk md (Func.mk name params rets body) :: donePart) (fspec :: specs)
            hnodup hspecs_wf' hnames_corr' hrets_corr' hHfc' hSpecC' newSpecs hloop_eq
        exact ⟨hnewSpecs_wf, hnewSpecs_names, hnewSpecs_rets, hnewSpecs_Hfc, hnewSpecs_SpecC⟩

-- ---------------------------------------------------------------------------
-- Whole-program wrappers: `seExecFuncs`/`seExecProg`
-- ---------------------------------------------------------------------------

/-- `seExecFuncs gconf p`, specialized from `seExecFuncs_loop_correct` at `funcs := p.reverse`,
    `donePart := []` -- see `SymExec.ProgCorrectness.seExecFuncs_correct`'s header; `H_simple` is
    no longer a parameter (see `H_simple_holds`), and no well-shapedness hypothesis is needed at
    all (see this file's header, point 2). `hasDupFuncNames p = false` also isn't a parameter --
    `seExecFuncs`'s own definition checks it first (`if hasDupFuncNames p then Except.error ...
    else ...`), so `hspecs_eq`'s success already forces it, recovered here by a case-split rather
    than assumed. -/
theorem seExecFuncs_correct {c : ZKConfig} (gconf : GlobalConfig c) (p : Prog c)
    (specs : List (FuncSpec c)) (hspecs_eq : seExecFuncs gconf p = Except.ok specs) :
    (∀ spec ∈ specs, spec.f.name = spec.name) ∧
    specs.map (·.name) = p.map funcWithMDName ∧
    (∀ (sconf : SymExecConfig c) (fname' : FName) (args : List (SimpleExpr c))
        (outs : List VarID) (md' : FuncMD) (func' : Func c) (p'' : Prog c),
      fetchFunc p fname' = Except.ok (FuncWithMD.mk md' func', p'') →
      (match func' with | Func.mk _ _ rs _ => outs.length = rs.length) →
      TranslatesCorrectly gconf sconf specs
        (fun env => evalFuncCallCmd gconf p fname' args outs env)
        (fun symEnv => seFuncCall gconf sconf symEnv specs fname' args outs)) ∧
    (∀ (fname' : FName) (md' : FuncMD) (func' : Func c) (p'' : Prog c),
      fetchFunc p fname' = Except.ok (FuncWithMD.mk md' func', p'') →
      ∀ fspec' : FuncSpec c, fetchFuncSpec specs fname' = Except.ok fspec' →
        (∃ (retsOffset : Nat) (auxVarsList : List Var),
          fspec'.f.params =
            (List.range (totalParamSize fspec'.params)).map (fun i => Var.ffv i) ++
            (List.range (totalParamSize fspec'.rets)).map (fun i => Var.ffv (retsOffset + i)) ++
            auxVarsList ∧
          totalParamSize fspec'.params ≤ retsOffset ∧
          (auxVarsList.filter isFFvVar).length = fspec'.numAuxFFVars ∧
          (auxVarsList.filter (fun v => !isFFvVar v)).length = fspec'.numAuxBoolVars ∧
          auxVarsList.Pairwise (fun a b => compare a b = .lt) ∧
          (∀ v ∈ auxVarsList, ∀ n, v = Var.ffv n →
            ¬(n < totalParamSize fspec'.params) ∧
            ¬(retsOffset ≤ n ∧ n < retsOffset + totalParamSize fspec'.rets))) ∧
        (∀ argVals, ValuesMatchParams argVals fspec'.params → ∀ outVals,
          evalFunCall gconf p fname' argVals = Except.ok outVals →
          ValuesMatchParams outVals fspec'.rets) ∧
        (∀ argVals, ValuesMatchParams argVals fspec'.params →
          (∀ retVals, evalFunCall gconf p fname' argVals = Except.ok retVals →
            ValuesMatchParams retVals fspec'.rets ∧
            ∃ (auxFF : List (FF c)) (auxBool : List Bool),
              auxFF.length = fspec'.numAuxFFVars ∧ auxBool.length = fspec'.numAuxBoolVars ∧
              ∀ assign, evalFormula gconf assign
                (FFFormula.call fspec'.f.name
                  (flattenValuesParams argVals ++ flattenValuesParams retVals ++
                   auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
                   auxBool.map (fun v => MacroCallParam.const (Const.boolc v))))
                (specs.map (·.f)) = Except.ok true) ∧
          (∀ (retVals : List (Value c)) (auxFF : List (FF c)) (auxBool : List Bool),
            ValuesMatchParams retVals fspec'.rets →
            auxFF.length = fspec'.numAuxFFVars → auxBool.length = fspec'.numAuxBoolVars →
            (∀ assign, evalFormula gconf assign
              (FFFormula.call fspec'.f.name
                (flattenValuesParams argVals ++ flattenValuesParams retVals ++
                 auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
                 auxBool.map (fun v => MacroCallParam.const (Const.boolc v))))
              (specs.map (·.f)) = Except.ok true) →
            evalFunCall gconf p fname' argVals = Except.ok retVals))) := by
  have hnodup : hasDupFuncNames p = false := by
    cases h : hasDupFuncNames p with
    | true => simp [seExecFuncs, h] at hspecs_eq
    | false => rfl
  have hloop_eq : seExecFuncs.loop gconf p.reverse [] = Except.ok specs := by
    simp only [seExecFuncs, hnodup, Bool.false_eq_true, if_false] at hspecs_eq
    exact hspecs_eq
  have hnodup' : hasDupFuncNames (p.reverse.reverse ++ ([] : Prog c)) = false := by
    simp only [List.reverse_reverse, List.append_nil]
    exact hnodup
  have hspecs_wf0 : ∀ spec ∈ ([] : List (FuncSpec c)), spec.f.name = spec.name :=
    fun spec hspec => absurd hspec (List.not_mem_nil)
  have hnames_corr0 : (([] : List (FuncSpec c)).map (·.name)) =
      (([] : Prog c)).map funcWithMDName := rfl
  have hrets_corr0 : ∀ fname'' fspec', fetchFuncSpec ([] : List (FuncSpec c)) fname'' =
        Except.ok fspec' →
      ∀ md func p'', fetchFunc ([] : Prog c) fname'' = Except.ok (FuncWithMD.mk md func, p'') →
        match func with | Func.mk _ _ rets _ => fspec'.rets.length = rets.length :=
    fun fname' _ hspec_eq => absurd hspec_eq (by simp [fetchFuncSpec])
  have hHfc0 : ∀ (sconf : SymExecConfig c) (fname' : FName) (args : List (SimpleExpr c))
      (outs : List VarID) (md' : FuncMD) (func' : Func c) (p'' : Prog c),
      fetchFunc ([] : Prog c) fname' = Except.ok (FuncWithMD.mk md' func', p'') →
      (match func' with | Func.mk _ _ rs _ => outs.length = rs.length) →
      TranslatesCorrectly gconf sconf ([] : List (FuncSpec c))
        (fun env => evalFuncCallCmd gconf ([] : Prog c) fname' args outs env)
        (fun symEnv => seFuncCall gconf sconf symEnv ([] : List (FuncSpec c)) fname' args outs) :=
    fun _ fname' _ _ _ _ _ hfetch _ _ _ _ => absurd hfetch (by simp [fetchFunc])
  have hSpecC0 : ∀ (fname' : FName) (md' : FuncMD) (func' : Func c) (p'' : Prog c),
      fetchFunc ([] : Prog c) fname' = Except.ok (FuncWithMD.mk md' func', p'') →
      ∀ fspec' : FuncSpec c, fetchFuncSpec ([] : List (FuncSpec c)) fname' = Except.ok fspec' →
        (∃ (retsOffset : Nat) (auxVarsList : List Var),
          fspec'.f.params =
            (List.range (totalParamSize fspec'.params)).map (fun i => Var.ffv i) ++
            (List.range (totalParamSize fspec'.rets)).map (fun i => Var.ffv (retsOffset + i)) ++
            auxVarsList ∧
          totalParamSize fspec'.params ≤ retsOffset ∧
          (auxVarsList.filter isFFvVar).length = fspec'.numAuxFFVars ∧
          (auxVarsList.filter (fun v => !isFFvVar v)).length = fspec'.numAuxBoolVars ∧
          auxVarsList.Pairwise (fun a b => compare a b = .lt) ∧
          (∀ v ∈ auxVarsList, ∀ n, v = Var.ffv n →
            ¬(n < totalParamSize fspec'.params) ∧
            ¬(retsOffset ≤ n ∧ n < retsOffset + totalParamSize fspec'.rets))) ∧
        (∀ argVals, ValuesMatchParams argVals fspec'.params → ∀ outVals,
          evalFunCall gconf ([] : Prog c) fname' argVals = Except.ok outVals →
          ValuesMatchParams outVals fspec'.rets) ∧
        (∀ argVals, ValuesMatchParams argVals fspec'.params →
          (∀ retVals, evalFunCall gconf ([] : Prog c) fname' argVals = Except.ok retVals →
            ValuesMatchParams retVals fspec'.rets ∧
            ∃ (auxFF : List (FF c)) (auxBool : List Bool),
              auxFF.length = fspec'.numAuxFFVars ∧ auxBool.length = fspec'.numAuxBoolVars ∧
              ∀ assign, evalFormula gconf assign
                (FFFormula.call fspec'.f.name
                  (flattenValuesParams argVals ++ flattenValuesParams retVals ++
                   auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
                   auxBool.map (fun v => MacroCallParam.const (Const.boolc v))))
                (([] : List (FuncSpec c)).map (·.f)) = Except.ok true) ∧
          (∀ (retVals : List (Value c)) (auxFF : List (FF c)) (auxBool : List Bool),
            ValuesMatchParams retVals fspec'.rets →
            auxFF.length = fspec'.numAuxFFVars → auxBool.length = fspec'.numAuxBoolVars →
            (∀ assign, evalFormula gconf assign
              (FFFormula.call fspec'.f.name
                (flattenValuesParams argVals ++ flattenValuesParams retVals ++
                 auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
                 auxBool.map (fun v => MacroCallParam.const (Const.boolc v))))
              (([] : List (FuncSpec c)).map (·.f)) = Except.ok true) →
            evalFunCall gconf ([] : Prog c) fname' argVals = Except.ok retVals)) :=
    fun _ fname' _ _ hfetch _ _ => absurd hfetch (by simp [fetchFunc])
  obtain ⟨hspecs_wf, hnames_corr, _hrets_corr, hHfc, hSpecC⟩ := seExecFuncs_loop_correct gconf
    p.reverse [] [] hnodup' hspecs_wf0 hnames_corr0 hrets_corr0 hHfc0 hSpecC0 specs hloop_eq
  have hp_eq : p.reverse.reverse ++ ([] : Prog c) = p := by simp
  refine ⟨hspecs_wf, ?_, ?_, ?_⟩
  · rw [hnames_corr, hp_eq]
  · intro sconf fname' args outs md' func' p'' hfetch houtlen
    have hfetch' : fetchFunc (p.reverse.reverse ++ ([] : Prog c)) fname' =
        Except.ok (FuncWithMD.mk md' func', p'') := by rw [hp_eq]; exact hfetch
    have := hHfc sconf fname' args outs md' func' p'' hfetch' houtlen
    simpa [hp_eq] using this
  · intro fname' md' func' p'' hfetch fspec' hspec'_eq
    have hfetch' : fetchFunc (p.reverse.reverse ++ ([] : Prog c)) fname' =
        Except.ok (FuncWithMD.mk md' func', p'') := by rw [hp_eq]; exact hfetch
    have := hSpecC fname' md' func' p'' hfetch' fspec' hspec'_eq
    simpa [hp_eq] using this

/-- Generic list fact: if `a ↦ b` occurs in `l` and `l`'s first components are `Nodup`, a linear
    search for `a` (via a `DecidableEq`-derived `Bool` test) finds exactly that pair -- the key
    fact making `lookupAuxFF`/`lookupAuxBool` (below) read back the right value, since
    `auxVarsList` is `Nodup` (it's `compare`-sorted, see `var_pairwise_lt_nodup`) but *not*
    contiguous, so it can't be read by direct indexing the way the param/ret ranges are. -/
theorem find?_fst_eq_some_of_nodup_mem {α β : Type} [DecidableEq α] :
    ∀ {l : List (α × β)}, (l.map Prod.fst).Nodup → ∀ {a : α} {b : β}, (a, b) ∈ l →
      l.find? (fun p => decide (p.1 = a)) = some (a, b) := by
  intro l
  induction l with
  | nil => intro _ a b hmem; simp at hmem
  | cons hd tl ih =>
      intro hnodup a b hmem
      rcases List.mem_cons.mp hmem with heq | hmem'
      · rw [← heq]; simp
      · simp only [List.map_cons, List.nodup_cons] at hnodup
        have hane : hd.1 ≠ a := by
          intro hcontra
          apply hnodup.1
          rw [hcontra]
          exact List.mem_map_of_mem hmem'
        rw [List.find?_cons_of_neg (by simpa using hane)]
        exact ih hnodup.2 hmem'

/-- Read an assignment's `.ff` value at a scattered, `Nodup` list of finite-field variable
    positions back out of a matching list of values, by linear search -- the
    assignment-construction dual of the direct indexing used for `buildAssign`'s contiguous
    param/ret ranges (`auxVarsList` isn't contiguous, so it can't be indexed directly). -/
def lookupAuxFF {c : ZKConfig} (vars : List Var) (vals : List (FF c)) (k : Nat) : FF c :=
  ((vars.zip vals).find? (fun p => decide (p.1 = Var.ffv k))).map Prod.snd |>.getD 0

/-- Bool-valued counterpart of `lookupAuxFF`. -/
def lookupAuxBool (vars : List Var) (vals : List Bool) (k : Nat) : Bool :=
  ((vars.zip vals).find? (fun p => decide (p.1 = Var.boolv k))).map Prod.snd |>.getD false

theorem lookupAuxFF_eq {c : ZKConfig} {vars : List Var} {vals : List (FF c)}
    (hlen : vars.length ≤ vals.length) (hnodup : vars.Nodup) {n : Nat} {x : FF c}
    (hmem : (Var.ffv n, x) ∈ vars.zip vals) :
    lookupAuxFF vars vals n = x := by
  unfold lookupAuxFF
  rw [find?_fst_eq_some_of_nodup_mem (by rw [List.map_fst_zip hlen]; exact hnodup) hmem]
  simp

theorem lookupAuxBool_eq {vars : List Var} {vals : List Bool}
    (hlen : vars.length ≤ vals.length) (hnodup : vars.Nodup) {n : Nat} {x : Bool}
    (hmem : (Var.boolv n, x) ∈ vars.zip vals) :
    lookupAuxBool vars vals n = x := by
  unfold lookupAuxBool
  rw [find?_fst_eq_some_of_nodup_mem (by rw [List.map_fst_zip hlen]; exact hnodup) hmem]
  simp

/-- Build an assignment whose readout at a contiguous param range `[0, paramsLen)`, a contiguous
    ret range `[retsOffset, retsOffset + retsLen)`, and a scattered `auxVarsList` (split into its
    ff/bool parts) matches given concrete/witness data exactly -- the construction
    `seExecProg_call_complete` needs to exhibit a genuine satisfying assignment from bare
    input/output/witness values. This is the dual of `reconstructValues`, which reads an
    assignment *back* into values; `buildAssign` goes the other way. -/
def buildAssign {c : ZKConfig} (paramsLen retsOffset retsLen : Nat)
    (argFF retFF : List (FF c)) (auxFFPart auxBoolPart : List Var)
    (auxFF : List (FF c)) (auxBool : List Bool) : Assignment c :=
  { ff := fun k =>
      if k < paramsLen then argFF.getD k 0
      else if retsOffset ≤ k ∧ k < retsOffset + retsLen then retFF.getD (k - retsOffset) 0
      else lookupAuxFF auxFFPart auxFF k
    bool := fun k => lookupAuxBool auxBoolPart auxBool k }

/-- Generic list fact: at any shared in-bounds index `i`, the two lists' `i`-th elements
    (read via `getD`, any fallback) are paired up by `List.zip` -- lets index-based reasoning
    (e.g. `list_map_const_ffc_eq_of_pointwise`'s per-position hypothesis) feed into
    `lookupAuxFF_eq`/`lookupAuxBool_eq`, which are stated over `zip` membership. -/
theorem mem_zip_of_getD {α β : Type} (l1 : List α) (l2 : List β) (d1 : α) (d2 : β) (i : Nat)
    (h1 : i < l1.length) (h2 : i < l2.length) :
    (l1.getD i d1, l2.getD i d2) ∈ l1.zip l2 := by
  induction l1 generalizing l2 i with
  | nil => simp at h1
  | cons a as ih =>
      cases l2 with
      | nil => simp at h2
      | cons b bs =>
          cases i with
          | zero => simp
          | succ i' =>
              simp only [List.length_cons] at h1 h2
              simp only [List.getD_cons_succ, List.zip_cons_cons, List.mem_cons]
              exact Or.inr (ih bs i' (by omega) (by omega))

/-- If every `Var` in `vars` is `.ffv`-typed and, at every in-bounds index, `assign`'s readout at
    that position's index matches `vals`'s own entry there, then constifying `vars` (as
    `MacroCallParam.var`s) against `assign` reproduces `vals` (as `.ffc` consts) exactly -- the
    per-position principle behind all three FF constify-pieces `seExecProg_call_complete` needs
    (params, rets, and the aux-ff sublist), proved once by simultaneous induction rather than
    three times. -/
theorem list_map_const_ffc_eq_of_pointwise {c : ZKConfig} (assign : Assignment c) :
    ∀ (vars : List Var) (vals : List (FF c)), vars.length = vals.length →
      (∀ v ∈ vars, ∃ n, v = Var.ffv n) →
      (∀ (i : Nat) (_hi : i < vars.length) (n : Nat), vars.getD i default = Var.ffv n →
        assign.ff n = vals.getD i 0) →
      vars.map (fun v => constifyMacroCallParam assign (MacroCallParam.var v)) =
        vals.map (fun x => MacroCallParam.const (Const.ffc x)) := by
  intro vars
  induction vars with
  | nil =>
      intro vals hlen _ _
      simp only [List.length_nil] at hlen
      simp [List.eq_nil_of_length_eq_zero hlen.symm]
  | cons v vs ih =>
      intro vals hlen hallff hassign
      cases vals with
      | nil => simp at hlen
      | cons x xs =>
          have hlen' : vs.length = xs.length := by
            simp only [List.length_cons] at hlen; omega
          obtain ⟨n, hn⟩ := hallff v (List.mem_cons_self)
          have hv0 : assign.ff n = x := by
            have h0 := hassign 0 (by simp) n (by simp [hn])
            simpa using h0
          have hrest := ih xs hlen'
            (fun v' hv' => hallff v' (List.mem_cons_of_mem v hv'))
            (fun i hi n' hn' => by
              have := hassign (i + 1) (by simp only [List.length_cons]; omega) n'
                (by simpa [List.getD_cons_succ] using hn')
              simpa [List.getD_cons_succ] using this)
          simp only [List.map_cons, hn, hrest]
          simp [constifyMacroCallParam, hv0]

/-- Bool-valued counterpart of `list_map_const_ffc_eq_of_pointwise`, for the aux-bool sublist. -/
theorem list_map_const_boolc_eq_of_pointwise {c : ZKConfig} (assign : Assignment c) :
    ∀ (vars : List Var) (vals : List Bool), vars.length = vals.length →
      (∀ v ∈ vars, ∃ n, v = Var.boolv n) →
      (∀ (i : Nat) (_hi : i < vars.length) (n : Nat), vars.getD i default = Var.boolv n →
        assign.bool n = vals.getD i false) →
      vars.map (fun v => constifyMacroCallParam assign (MacroCallParam.var v)) =
        vals.map (fun x => MacroCallParam.const (Const.boolc x)) := by
  intro vars
  induction vars with
  | nil =>
      intro vals hlen _ _
      simp only [List.length_nil] at hlen
      simp [List.eq_nil_of_length_eq_zero hlen.symm]
  | cons v vs ih =>
      intro vals hlen hallbool hassign
      cases vals with
      | nil => simp at hlen
      | cons x xs =>
          have hlen' : vs.length = xs.length := by
            simp only [List.length_cons] at hlen; omega
          obtain ⟨n, hn⟩ := hallbool v (List.mem_cons_self)
          have hv0 : assign.bool n = x := by
            have h0 := hassign 0 (by simp) n (by simp [hn])
            simpa using h0
          have hrest := ih xs hlen'
            (fun v' hv' => hallbool v' (List.mem_cons_of_mem v hv'))
            (fun i hi n' hn' => by
              have := hassign (i + 1) (by simp only [List.length_cons]; omega) n'
                (by simpa [List.getD_cons_succ] using hn')
              simpa [List.getD_cons_succ] using this)
          simp only [List.map_cons, hn, hrest]
          simp [constifyMacroCallParam, hv0]

/-- Forward ("sound") half of `seExecProg_call_correct`: if some assignment satisfies a call to
    `fspec` with its own formal parameters as arguments, that assignment's own readout at the
    param/ret positions already *is* a matching concrete execution -- the conclusion says so
    explicitly (`argVals`/`retVals` are literally `assign`'s own `reconstructValues` readout, not
    just "some values of the right shape"), since a witness existential unconnected to the given
    `assign` would say nothing about *this* assignment at all. Takes exactly the per-`fname`
    bundle `hSpecC` (`seExecFuncs_correct`) produces, so `seExecProg_call_correct` can call this
    directly without redoing the whole-program setup. -/
theorem seExecProg_call_sound {c : ZKConfig} (gconf : GlobalConfig c) (funcs : Prog c)
    (fname : FName) (fspec : FuncSpec c) (macros : List (FFMacro c))
    (retsOffset : Nat) (auxVarsList : List Var)
    (hsplit_eq : fspec.f.params =
      (List.range (totalParamSize fspec.params)).map (fun i => Var.ffv i) ++
      (List.range (totalParamSize fspec.rets)).map (fun i => Var.ffv (retsOffset + i)) ++
      auxVarsList)
    (hsorted : auxVarsList.Pairwise (fun a b => compare a b = Ordering.lt))
    (hauxFF_len : (auxVarsList.filter isFFvVar).length = fspec.numAuxFFVars)
    (hauxBool_len : (auxVarsList.filter (fun v => !isFFvVar v)).length = fspec.numAuxBoolVars)
    (H_specCorrect : ∀ (argVals : List (Value c)), ValuesMatchParams argVals fspec.params →
      (∀ (retVals : List (Value c)), evalFunCall gconf funcs fname argVals = Except.ok retVals →
        ValuesMatchParams retVals fspec.rets ∧
        ∃ (auxFF : List (FF c)) (auxBool : List Bool),
          auxFF.length = fspec.numAuxFFVars ∧ auxBool.length = fspec.numAuxBoolVars ∧
          ∀ (assign : Assignment c), evalFormula gconf assign
            (FFFormula.call fspec.f.name
              (flattenValuesParams argVals ++ flattenValuesParams retVals ++
               auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
               auxBool.map (fun v => MacroCallParam.const (Const.boolc v)))) macros
            = Except.ok true) ∧
      (∀ (retVals : List (Value c)) (auxFF : List (FF c)) (auxBool : List Bool),
        ValuesMatchParams retVals fspec.rets → auxFF.length = fspec.numAuxFFVars →
        auxBool.length = fspec.numAuxBoolVars →
        (∀ (assign : Assignment c), evalFormula gconf assign
          (FFFormula.call fspec.f.name
            (flattenValuesParams argVals ++ flattenValuesParams retVals ++
             auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
             auxBool.map (fun v => MacroCallParam.const (Const.boolc v)))) macros
          = Except.ok true) →
        evalFunCall gconf funcs fname argVals = Except.ok retVals))
    (assign : Assignment c)
    (hLHS : evalFormula gconf assign
      (FFFormula.call fspec.f.name (fspec.f.params.map (fun v => MacroCallParam.var v))) macros
      = Except.ok true) :
    ∃ (argVals retVals : List (Value c)),
      ValuesMatchParams argVals fspec.params ∧ ValuesMatchParams retVals fspec.rets ∧
      evalFunCall gconf funcs fname argVals = Except.ok retVals ∧
      argVals = reconstructValues assign.ff fspec.params 0 ∧
      retVals = reconstructValues assign.ff fspec.rets retsOffset := by
  rw [evalFormula_call_constify, List.map_map, hsplit_eq, List.map_append, List.map_append]
    at hLHS
  simp only [Function.comp_def] at hLHS
  set argVals : List (Value c) := reconstructValues assign.ff fspec.params 0 with hargVals_def
  set retVals : List (Value c) := reconstructValues assign.ff fspec.rets retsOffset
    with hretVals_def
  set auxFF : List (FF c) :=
    (auxVarsList.filter isFFvVar).map (fun v => assign.ff (varIndex v)) with hauxFF_def
  set auxBool : List Bool :=
    (auxVarsList.filter (fun v => !isFFvVar v)).map (fun v => assign.bool (varIndex v))
    with hauxBool_def
  have hpieceP : ((List.range (totalParamSize fspec.params)).map (fun i => Var.ffv i)).map
      (fun v => constifyMacroCallParam assign (MacroCallParam.var v)) =
      flattenValuesParams argVals := by
    rw [hargVals_def, flattenValuesParams_eq_map, reconstructValues_flattenToFF]
    simp only [List.map_map, Function.comp_def, constifyMacroCallParam, Nat.zero_add]
  have hpieceR : ((List.range (totalParamSize fspec.rets)).map
      (fun i => Var.ffv (retsOffset + i))).map
      (fun v => constifyMacroCallParam assign (MacroCallParam.var v)) =
      flattenValuesParams retVals := by
    rw [hretVals_def, flattenValuesParams_eq_map, reconstructValues_flattenToFF]
    simp only [List.map_map, Function.comp_def, constifyMacroCallParam]
  have hpieceA : auxVarsList.map
      (fun v => constifyMacroCallParam assign (MacroCallParam.var v)) =
      auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
      auxBool.map (fun v => MacroCallParam.const (Const.boolc v)) := by
    have hfullList := auxVarsList_ff_bool_split auxVarsList hsorted
    conv_lhs => rw [← List.take_append_drop (auxVarsList.filter isFFvVar).length auxVarsList]
    rw [hfullList.1, hfullList.2.1, List.map_append, hauxFF_def, hauxBool_def,
      List.map_map, List.map_map]
    congr 1
    · apply List.map_congr_left
      intro v hv
      obtain ⟨n, hn⟩ := hfullList.2.2.1 v hv
      simp [hn, constifyMacroCallParam, varIndex]
    · apply List.map_congr_left
      intro v hv
      obtain ⟨n, hn⟩ := hfullList.2.2.2 v hv
      simp [hn, constifyMacroCallParam, varIndex]
  rw [hpieceP, hpieceR, hpieceA] at hLHS
  simp only [← List.append_assoc] at hLHS
  have hallconst : ∀ mcp ∈ (flattenValuesParams argVals ++ flattenValuesParams retVals ++
      auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
      auxBool.map (fun v => MacroCallParam.const (Const.boolc v))),
      ∃ cv, mcp = MacroCallParam.const cv := by
    intro mcp hmcp
    rcases List.mem_append.mp hmcp with h1 | h2
    · rcases List.mem_append.mp h1 with h1a | h1b
      · rcases List.mem_append.mp h1a with h1a1 | h1a2
        · exact flattenValuesParams_all_const argVals mcp h1a1
        · exact flattenValuesParams_all_const retVals mcp h1a2
      · obtain ⟨v, _, hveq⟩ := List.mem_map.mp h1b; exact ⟨Const.ffc v, hveq.symm⟩
    · obtain ⟨v, _, hveq⟩ := List.mem_map.mp h2; exact ⟨Const.boolc v, hveq.symm⟩
  have hform_all : ∀ assign', evalFormula gconf assign'
      (FFFormula.call fspec.f.name
        (flattenValuesParams argVals ++ flattenValuesParams retVals ++
         auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
         auxBool.map (fun v => MacroCallParam.const (Const.boolc v))))
      macros = Except.ok true := by
    intro assign'
    rw [evalFormula_call_const_args_indep gconf assign' assign fspec.f.name _ macros hallconst]
    exact hLHS
  have hshape_arg : ValuesMatchParams argVals fspec.params := by
    rw [hargVals_def]; exact reconstructValues_matches assign.ff fspec.params 0
  have hshape_ret : ValuesMatchParams retVals fspec.rets := by
    rw [hretVals_def]; exact reconstructValues_matches assign.ff fspec.rets retsOffset
  have hauxFF_len' : auxFF.length = fspec.numAuxFFVars := by
    rw [hauxFF_def, List.length_map]; exact hauxFF_len
  have hauxBool_len' : auxBool.length = fspec.numAuxBoolVars := by
    rw [hauxBool_def, List.length_map]; exact hauxBool_len
  obtain ⟨_, hB⟩ := H_specCorrect argVals hshape_arg
  have hevalFC : evalFunCall gconf funcs fname argVals = Except.ok retVals :=
    hB retVals auxFF auxBool hshape_ret hauxFF_len' hauxBool_len' hform_all
  exact ⟨argVals, retVals, hshape_arg, hshape_ret, hevalFC, hargVals_def, hretVals_def⟩

/-- Backward ("complete") half of `seExecProg_call_correct`: given a concrete execution
    (`argVals`/`retVals` related by `evalFunCall`), `buildAssign` exhibits an assignment that
    satisfies a call to `fspec` with its own formal parameters as arguments -- and, again
    explicitly (not just "some assignment exists" unconnected to the given data), that
    assignment's own readout at the param/ret positions reproduces `argVals`/`retVals` exactly,
    via the new `reconstructValues_eq_of_matches` roundtrip fact. Needs the extra
    range-disjointness fact `seFunc_f_params_split` proves (`hparams_le_rets`/`hauxDisjoint`) --
    unlike `seExecProg_call_sound`, this direction *constructs* the assignment piecewise, so it
    has to know the param/ret/aux ranges genuinely don't overlap before trusting `buildAssign`'s
    if-chain to land in the right branch. -/
theorem seExecProg_call_complete {c : ZKConfig} (gconf : GlobalConfig c) (funcs : Prog c)
    (fname : FName) (fspec : FuncSpec c) (macros : List (FFMacro c))
    (retsOffset : Nat) (auxVarsList : List Var)
    (hsplit_eq : fspec.f.params =
      (List.range (totalParamSize fspec.params)).map (fun i => Var.ffv i) ++
      (List.range (totalParamSize fspec.rets)).map (fun i => Var.ffv (retsOffset + i)) ++
      auxVarsList)
    (hparams_le_rets : totalParamSize fspec.params ≤ retsOffset)
    (hsorted : auxVarsList.Pairwise (fun a b => compare a b = Ordering.lt))
    (hauxFF_len : (auxVarsList.filter isFFvVar).length = fspec.numAuxFFVars)
    (hauxBool_len : (auxVarsList.filter (fun v => !isFFvVar v)).length = fspec.numAuxBoolVars)
    (hauxDisjoint : ∀ v ∈ auxVarsList, ∀ n, v = Var.ffv n →
      ¬(n < totalParamSize fspec.params) ∧
      ¬(retsOffset ≤ n ∧ n < retsOffset + totalParamSize fspec.rets))
    (H_specCorrect : ∀ (argVals : List (Value c)), ValuesMatchParams argVals fspec.params →
      (∀ (retVals : List (Value c)), evalFunCall gconf funcs fname argVals = Except.ok retVals →
        ValuesMatchParams retVals fspec.rets ∧
        ∃ (auxFF : List (FF c)) (auxBool : List Bool),
          auxFF.length = fspec.numAuxFFVars ∧ auxBool.length = fspec.numAuxBoolVars ∧
          ∀ (assign : Assignment c), evalFormula gconf assign
            (FFFormula.call fspec.f.name
              (flattenValuesParams argVals ++ flattenValuesParams retVals ++
               auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
               auxBool.map (fun v => MacroCallParam.const (Const.boolc v)))) macros
            = Except.ok true) ∧
      (∀ (retVals : List (Value c)) (auxFF : List (FF c)) (auxBool : List Bool),
        ValuesMatchParams retVals fspec.rets → auxFF.length = fspec.numAuxFFVars →
        auxBool.length = fspec.numAuxBoolVars →
        (∀ (assign : Assignment c), evalFormula gconf assign
          (FFFormula.call fspec.f.name
            (flattenValuesParams argVals ++ flattenValuesParams retVals ++
             auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
             auxBool.map (fun v => MacroCallParam.const (Const.boolc v)))) macros
          = Except.ok true) →
        evalFunCall gconf funcs fname argVals = Except.ok retVals))
    (argVals : List (Value c)) (hargVals : ValuesMatchParams argVals fspec.params)
    (retVals : List (Value c))
    (hevalFC : evalFunCall gconf funcs fname argVals = Except.ok retVals) :
    ∃ (assign : Assignment c),
      evalFormula gconf assign
        (FFFormula.call fspec.f.name (fspec.f.params.map (fun v => MacroCallParam.var v))) macros
        = Except.ok true ∧
      argVals = reconstructValues assign.ff fspec.params 0 ∧
      retVals = reconstructValues assign.ff fspec.rets retsOffset := by
  obtain ⟨hshape_ret, auxFF, auxBool, hauxFF_len', hauxBool_len', hform_all⟩ :=
    (H_specCorrect argVals hargVals).1 retVals hevalFC
  set argFF : List (FF c) := flattenValuesToFF argVals with hargFF_def
  set retFF : List (FF c) := flattenValuesToFF retVals with hretFF_def
  set auxFFPart : List Var := auxVarsList.filter isFFvVar with hauxFFPart_def
  set auxBoolPart : List Var := auxVarsList.filter (fun v => !isFFvVar v) with hauxBoolPart_def
  set assign : Assignment c := buildAssign (totalParamSize fspec.params) retsOffset
    (totalParamSize fspec.rets) argFF retFF auxFFPart auxBoolPart auxFF auxBool with hassign_def
  refine ⟨assign, ?_⟩
  have hargFF_len : argFF.length = totalParamSize fspec.params :=
    flattenValuesToFF_length argVals fspec.params hargVals
  have hretFF_len : retFF.length = totalParamSize fspec.rets :=
    flattenValuesToFF_length retVals fspec.rets hshape_ret
  have hauxFFPart_nodup : auxFFPart.Nodup :=
    List.Sublist.nodup List.filter_sublist (var_pairwise_lt_nodup hsorted)
  have hauxBoolPart_nodup : auxBoolPart.Nodup :=
    List.Sublist.nodup List.filter_sublist (var_pairwise_lt_nodup hsorted)
  have hauxFFPart_sub : auxFFPart ⊆ auxVarsList := List.Sublist.subset List.filter_sublist
  have hfullList := auxVarsList_ff_bool_split auxVarsList hsorted
  have hpieceP : ((List.range (totalParamSize fspec.params)).map (fun i => Var.ffv i)).map
      (fun v => constifyMacroCallParam assign (MacroCallParam.var v)) =
      flattenValuesParams argVals := by
    rw [flattenValuesParams_eq_map, ← hargFF_def]
    apply list_map_const_ffc_eq_of_pointwise
    · simp [hargFF_len]
    · intro v hv
      obtain ⟨i, hi, hveq⟩ := List.mem_map.mp hv
      exact ⟨i, hveq.symm⟩
    · intro i hi n hn
      rw [range_map_getD (totalParamSize fspec.params) (fun i => Var.ffv i) i
        (by simpa using hi) default] at hn
      injection hn with hn
      subst hn
      simp only [hassign_def, buildAssign]
      rw [if_pos (by simpa using hi)]
  have hpieceR : ((List.range (totalParamSize fspec.rets)).map
      (fun i => Var.ffv (retsOffset + i))).map
      (fun v => constifyMacroCallParam assign (MacroCallParam.var v)) =
      flattenValuesParams retVals := by
    rw [flattenValuesParams_eq_map, ← hretFF_def]
    apply list_map_const_ffc_eq_of_pointwise
    · simp [hretFF_len]
    · intro v hv
      obtain ⟨i, hi, hveq⟩ := List.mem_map.mp hv
      exact ⟨retsOffset + i, hveq.symm⟩
    · intro i hi n hn
      rw [range_map_getD (totalParamSize fspec.rets) (fun i => Var.ffv (retsOffset + i)) i
        (by simpa using hi) default] at hn
      injection hn with hn
      subst hn
      have hi' : i < totalParamSize fspec.rets := by simpa using hi
      have hple := hparams_le_rets
      simp only [hassign_def, buildAssign]
      rw [if_neg (show ¬ (retsOffset + i < totalParamSize fspec.params) by omega),
        if_pos (show retsOffset ≤ retsOffset + i ∧
          retsOffset + i < retsOffset + totalParamSize fspec.rets by omega)]
      congr 1
      omega
  have hpieceAFF : auxFFPart.map (fun v => constifyMacroCallParam assign (MacroCallParam.var v)) =
      auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) := by
    apply list_map_const_ffc_eq_of_pointwise
    · rw [hauxFFPart_def, hauxFF_len]; exact hauxFF_len'.symm
    · exact hfullList.2.2.1
    · intro i hi n hn
      have hvmem : Var.ffv n ∈ auxFFPart := by
        have hmem := List.getElem_mem (l := auxFFPart) (n := i) hi
        rw [List.getElem_eq_getD (default : Var)] at hmem
        rwa [hn] at hmem
      have hdisj := hauxDisjoint (Var.ffv n) (hauxFFPart_sub hvmem) n rfl
      have hlen_eq : auxFFPart.length = auxFF.length := by
        rw [hauxFFPart_def, hauxFF_len]; exact hauxFF_len'.symm
      have hmemzip := mem_zip_of_getD auxFFPart auxFF default 0 i hi (by rw [← hlen_eq]; exact hi)
      rw [hn] at hmemzip
      have heq : assign.ff n = lookupAuxFF auxFFPart auxFF n := by
        simp only [hassign_def, buildAssign]
        rw [if_neg hdisj.1, if_neg hdisj.2]
      rw [heq]
      exact lookupAuxFF_eq (le_of_eq hlen_eq) hauxFFPart_nodup hmemzip
  have hpieceABool : auxBoolPart.map
      (fun v => constifyMacroCallParam assign (MacroCallParam.var v)) =
      auxBool.map (fun v => MacroCallParam.const (Const.boolc v)) := by
    apply list_map_const_boolc_eq_of_pointwise
    · rw [hauxBoolPart_def, hauxBool_len]; exact hauxBool_len'.symm
    · exact hfullList.2.2.2
    · intro i hi n hn
      have hlen_eq : auxBoolPart.length = auxBool.length := by
        rw [hauxBoolPart_def, hauxBool_len]; exact hauxBool_len'.symm
      have hmemzip := mem_zip_of_getD auxBoolPart auxBool default false i hi
        (by rw [← hlen_eq]; exact hi)
      rw [hn] at hmemzip
      have heq : assign.bool n = lookupAuxBool auxBoolPart auxBool n := by
        simp only [hassign_def, buildAssign]
      rw [heq]
      exact lookupAuxBool_eq (le_of_eq hlen_eq) hauxBoolPart_nodup hmemzip
  have hpieceA : auxVarsList.map
      (fun v => constifyMacroCallParam assign (MacroCallParam.var v)) =
      auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
      auxBool.map (fun v => MacroCallParam.const (Const.boolc v)) := by
    conv_lhs => rw [← List.take_append_drop (auxVarsList.filter isFFvVar).length auxVarsList]
    rw [hfullList.1, hfullList.2.1, List.map_append, ← hauxFFPart_def, ← hauxBoolPart_def,
      hpieceAFF, hpieceABool]
  have hconstify_eq :
      fspec.f.params.map (fun v => constifyMacroCallParam assign (MacroCallParam.var v)) =
        flattenValuesParams argVals ++ flattenValuesParams retVals ++
        auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
        auxBool.map (fun v => MacroCallParam.const (Const.boolc v)) := by
    rw [hsplit_eq, List.map_append, List.map_append, hpieceP, hpieceR, hpieceA]
    simp only [← List.append_assoc]
  have hargVals_eq : argVals = reconstructValues assign.ff fspec.params 0 := by
    symm
    apply reconstructValues_eq_of_matches assign.ff argVals fspec.params 0 hargVals
    intro i hi
    simp only [Nat.zero_add, hassign_def, buildAssign]
    rw [if_pos hi, ← hargFF_def]
  have hretVals_eq : retVals = reconstructValues assign.ff fspec.rets retsOffset := by
    symm
    apply reconstructValues_eq_of_matches assign.ff retVals fspec.rets retsOffset hshape_ret
    intro i hi
    simp only [hassign_def, buildAssign]
    rw [if_neg (show ¬ (retsOffset + i < totalParamSize fspec.params) by omega),
      if_pos (show retsOffset ≤ retsOffset + i ∧
        retsOffset + i < retsOffset + totalParamSize fspec.rets by omega),
      ← hretFF_def]
    congr 1
    omega
  refine ⟨?_, hargVals_eq, hretVals_eq⟩
  rw [evalFormula_call_constify, List.map_map]
  simp only [Function.comp_def]
  rw [hconstify_eq]
  exact hform_all assign

end Corellzk2smt.SymExec.Correctness.ProgCorrectness
