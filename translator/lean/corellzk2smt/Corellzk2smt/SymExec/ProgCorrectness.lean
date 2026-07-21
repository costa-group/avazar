import Corellzk2smt.SymExec.FuncCorrectness
import Corellzk2smt.Language.Core.Analysis.DefinedVars

/- Whole-program correctness: `seExecFuncs`/`seExecProg` (`SymExec/BigStep.lean`). Builds on
   `seFunc_correct`/`seFuncCall_correct_via_seFunc` (`FuncCorrectness.lean`) by inducting over
   `seExecFuncs`'s own `loop`, discharging `H_funcCall` for real (not assuming it) at each step --
   using `TranslatesCorrectly_prepend` (`Correctness.lean`) to lift the previous step's `H_funcCall`
   fact across the newly-added spec, and `WellShapedProg`/`WellShapedProg_head_after_prefix`
   (`Language/Core/Analysis/WellShaped.lean`) to discharge the well-shapedness/name-disjointness
   preconditions that lift needs. `H_simple`/`H_domain`/`H_shape` remain permanently-assumed
   hypotheses throughout (quantified over every `specs` value that arises along the induction),
   exactly as `seFunc_correct` itself already needs -- `seSimpleCmd` is still a stub, and
   `H_domain`/`H_shape` are about `seCmds`'s own internal behavior, not about `specs`'s history. -/

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
open Corellzk2smt.SymExec.Correctness
open Corellzk2smt.SymExec.FuncCorrectness

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

/-- `TranslatesCorrectly` only ever consumes `concrete`/`symbolic` through pointwise application,
    so equal-as-functions replacements carry a `TranslatesCorrectly` fact across. -/
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

/-- The core induction: `seExecFuncs`'s `loop`, generalized over an explicit `donePart` standing
    for the functions already folded into `specs` (so `funcs.reverse ++ donePart` is always the
    relevant whole-program context for `fetchFunc`/`WellShapedProg` purposes -- `loop` processes
    `funcs` back-to-front, so at any point the functions already handled, in *original* order,
    are `funcs.reverse`'s complement within the full list, i.e. exactly `donePart`), together with
    the invariant that `specs`'s names exactly track `donePart`'s (both grow by prepending the
    same name at the same time). -/
theorem seExecFuncs_loop_correct {c : ZKConfig} (gconf : GlobalConfig c)
    (H_simple : ∀ (specs : List (FuncSpec c)) (sconf : SymExecConfig c) (i : ComWithMD c),
      TranslatesCorrectly gconf sconf specs (fun env => evalSimpleCmd gconf env i)
        (fun symEnv => seSimpleCmd gconf sconf symEnv specs i))
    (H_domain : ∀ (specs : List (FuncSpec c)) (sconf' : SymExecConfig c) (symEnv' : SymEnv c)
        (cmds : List (ComWithMD c)) (spec : CmdsSpec c),
      seCmds gconf sconf' symEnv' specs cmds = Except.ok spec →
      ∀ id, symEnv'.contains id ↔ spec.outSymEnv.contains id)
    (H_shape : ∀ (specs : List (FuncSpec c)) (sconf' : SymExecConfig c) (symEnv' : SymEnv c)
        (tb' eb' : List (ComWithMD c)) (tbSpec' ebSpec' : CmdsSpec c),
      seCmds gconf sconf' symEnv' specs tb' = Except.ok tbSpec' →
      seCmds gconf sconf' symEnv' specs eb' = Except.ok ebSpec' →
      ∀ id svTb svEb, tbSpec'.outSymEnv.get? id = some svTb →
        ebSpec'.outSymEnv.get? id = some svEb → sameShape svTb svEb) :
    ∀ (funcs donePart : Prog c) (specs : List (FuncSpec c)),
      WellShapedProg gconf (funcs.reverse ++ donePart) →
      hasDupFuncNames (funcs.reverse ++ donePart) = false →
      (∀ spec ∈ specs, spec.f.name = spec.name) →
      specs.map (·.name) = donePart.map funcWithMDName →
      (∀ (sconf : SymExecConfig c) (fname' : FName) (args : List (SimpleExpr c))
          (outs : List VarID) (md' : FuncMD) (func' : Func c) (p'' : Prog c),
        fetchFunc donePart fname' = Except.ok (FuncWithMD.mk md' func', p'') →
        (match func' with | Func.mk _ params _ _ => args.length = params.length) →
        (match func' with | Func.mk _ _ rets _ => outs.length = rets.length) → outs.Nodup →
        (∀ (env : Env c), ∃ vs : List (Value c), evalSimpleExprsToValue env args = Except.ok vs ∧
          ValuesMatchParams vs (match func' with | Func.mk _ params _ _ => params)) →
        TranslatesCorrectly gconf sconf specs
          (fun env => evalFuncCallCmd gconf donePart fname' args outs env)
          (fun symEnv => seFuncCall gconf sconf symEnv specs fname' args outs)) →
      ∀ (newSpecs : List (FuncSpec c)),
        seExecFuncs.loop gconf funcs specs = Except.ok newSpecs →
        (∀ spec ∈ newSpecs, spec.f.name = spec.name) ∧
        newSpecs.map (·.name) = (funcs.reverse ++ donePart).map funcWithMDName ∧
        (∀ (sconf : SymExecConfig c) (fname' : FName) (args : List (SimpleExpr c))
            (outs : List VarID) (md' : FuncMD) (func' : Func c) (p'' : Prog c),
          fetchFunc (funcs.reverse ++ donePart) fname' =
              Except.ok (FuncWithMD.mk md' func', p'') →
          (match func' with | Func.mk _ params _ _ => args.length = params.length) →
          (match func' with | Func.mk _ _ rets _ => outs.length = rets.length) → outs.Nodup →
          (∀ (env : Env c), ∃ vs : List (Value c),
            evalSimpleExprsToValue env args = Except.ok vs ∧
            ValuesMatchParams vs (match func' with | Func.mk _ params _ _ => params)) →
          TranslatesCorrectly gconf sconf newSpecs
            (fun env => evalFuncCallCmd gconf (funcs.reverse ++ donePart) fname' args outs env)
            (fun symEnv => seFuncCall gconf sconf symEnv newSpecs fname' args outs)) := by
  intro funcs
  induction funcs with
  | nil =>
      intro donePart specs _hwsp _hnodup hspecs_wf hnames_corr hHfc newSpecs hloop_eq
      simp only [List.reverse_nil, List.nil_append] at hloop_eq ⊢
      simp only [seExecFuncs.loop] at hloop_eq
      injection hloop_eq with hloop_eq
      exact ⟨hloop_eq ▸ hspecs_wf, hloop_eq ▸ hnames_corr, hloop_eq ▸ hHfc⟩
  | cons func funcs' ih =>
      intro donePart specs hwsp hnodup hspecs_wf hnames_corr hHfc newSpecs hloop_eq
      obtain ⟨md, name, params, rets, body⟩ := func
      have hlist_eq : (FuncWithMD.mk md (Func.mk name params rets body) :: funcs').reverse ++
          donePart =
          funcs'.reverse ++ (FuncWithMD.mk md (Func.mk name params rets body) :: donePart) := by
        simp [List.reverse_cons, List.append_assoc]
      rw [hlist_eq] at hwsp hnodup ⊢
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
        obtain ⟨hshaped, hBdisj, _hA'disj⟩ :=
          WellShapedProg_head_after_prefix gconf funcs'.reverse donePart
            (FuncWithMD.mk md (Func.mk name params rets body)) hwsp
        have hbody_eq : funcWithMDBody (FuncWithMD.mk md (Func.mk name params rets body)) =
            body := rfl
        have hname_eq2 : funcWithMDName (FuncWithMD.mk md (Func.mk name params rets body)) =
            name := rfl
        rw [hbody_eq] at hshaped
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
        -- H_funcCall for (thisFunc :: donePart) / (fspec :: specs)
        have hHfc' : ∀ (sconf : SymExecConfig c) (fname' : FName) (args : List (SimpleExpr c))
            (outs : List VarID) (md' : FuncMD) (func'' : Func c) (p'' : Prog c),
            fetchFunc (FuncWithMD.mk md (Func.mk name params rets body) :: donePart) fname' =
                Except.ok (FuncWithMD.mk md' func'', p'') →
            (match func'' with | Func.mk _ ps _ _ => args.length = ps.length) →
            (match func'' with | Func.mk _ _ rs _ => outs.length = rs.length) → outs.Nodup →
            (∀ (env : Env c), ∃ vs : List (Value c),
              evalSimpleExprsToValue env args = Except.ok vs ∧
              ValuesMatchParams vs (match func'' with | Func.mk _ ps _ _ => ps)) →
            TranslatesCorrectly gconf sconf (fspec :: specs)
              (fun env => evalFuncCallCmd gconf
                (FuncWithMD.mk md (Func.mk name params rets body) :: donePart) fname' args outs
                env)
              (fun symEnv => seFuncCall gconf sconf symEnv (fspec :: specs) fname' args outs) := by
          intro sconf fname' args outs md'' func'' p'' hfetch harglen houtlen houtnodup hargsdef
          simp only [fetchFunc] at hfetch
          by_cases hcase : name = fname'
          · subst hcase
            simp only [BEq.rfl, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at hfetch
            obtain ⟨hfeq, hpeq⟩ := hfetch
            injection hfeq with hmdeq hfunceq
            rw [← hfunceq] at harglen houtlen hargsdef
            have hargsdef' : ∀ (env : Env c), ∃ vs : List (Value c),
                evalSimpleExprsToValue env args = Except.ok vs ∧
                  ValuesMatchParams vs fspec.params := by
              intro env
              obtain ⟨vs, heval, hmatch⟩ := hargsdef env
              exact ⟨vs, heval, hparams_eq ▸ hmatch⟩
            exact seFuncCall_correct_via_seFunc gconf (FuncWithMD.mk md
                (Func.mk name params rets body) :: donePart) specs sconf name md
              (Func.mk name params rets body) donePart
              (by simp only [fetchFunc, BEq.rfl, ↓reduceIte])
              hnodup_head
              (H_simple specs) (hHfc) (H_domain specs) (H_shape specs) hshaped
              fspec hseFunc_eq args outs (hparams_eq ▸ harglen) (hrets_eq ▸ houtlen)
              houtnodup hargsdef'
          · have hbeq : (name == fname') = false := by simpa using hcase
            simp only [hbeq, Bool.false_eq_true, ↓reduceIte] at hfetch
            have hspec_old := hHfc sconf fname' args outs md'' func'' p'' hfetch harglen
              houtlen houtnodup hargsdef
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
        obtain ⟨hnewSpecs_wf, hnewSpecs_names, hnewSpecs_Hfc⟩ :=
          ih (FuncWithMD.mk md (Func.mk name params rets body) :: donePart) (fspec :: specs) hwsp
            hnodup hspecs_wf' hnames_corr' hHfc' newSpecs hloop_eq
        exact ⟨hnewSpecs_wf, hnewSpecs_names, hnewSpecs_Hfc⟩

-- ---------------------------------------------------------------------------
-- Whole-program wrappers: `seExecFuncs`/`seExecProg`
-- ---------------------------------------------------------------------------

/-- `seExecFuncs gconf p`, specialized from `seExecFuncs_loop_correct` at `funcs := p.reverse`,
    `donePart := []` (nothing processed yet, matching `seExecFuncs`'s own `loop p.reverse []`
    starting point) -- the base case's vacuous `specs := []`/`donePart := []` hypotheses discharge
    trivially, and `p.reverse.reverse ++ [] = p` collapses the conclusion down to a fact about the
    whole, un-reversed program `p` itself. -/
theorem seExecFuncs_correct {c : ZKConfig} (gconf : GlobalConfig c) (p : Prog c)
    (H_simple : ∀ (specs : List (FuncSpec c)) (sconf : SymExecConfig c) (i : ComWithMD c),
      TranslatesCorrectly gconf sconf specs (fun env => evalSimpleCmd gconf env i)
        (fun symEnv => seSimpleCmd gconf sconf symEnv specs i))
    (H_domain : ∀ (specs : List (FuncSpec c)) (sconf' : SymExecConfig c) (symEnv' : SymEnv c)
        (cmds : List (ComWithMD c)) (spec : CmdsSpec c),
      seCmds gconf sconf' symEnv' specs cmds = Except.ok spec →
      ∀ id, symEnv'.contains id ↔ spec.outSymEnv.contains id)
    (H_shape : ∀ (specs : List (FuncSpec c)) (sconf' : SymExecConfig c) (symEnv' : SymEnv c)
        (tb' eb' : List (ComWithMD c)) (tbSpec' ebSpec' : CmdsSpec c),
      seCmds gconf sconf' symEnv' specs tb' = Except.ok tbSpec' →
      seCmds gconf sconf' symEnv' specs eb' = Except.ok ebSpec' →
      ∀ id svTb svEb, tbSpec'.outSymEnv.get? id = some svTb →
        ebSpec'.outSymEnv.get? id = some svEb → sameShape svTb svEb)
    (hwsp : WellShapedProg gconf p) (hnodup : hasDupFuncNames p = false)
    (specs : List (FuncSpec c)) (hspecs_eq : seExecFuncs gconf p = Except.ok specs) :
    (∀ spec ∈ specs, spec.f.name = spec.name) ∧
    specs.map (·.name) = p.map funcWithMDName ∧
    (∀ (sconf : SymExecConfig c) (fname' : FName) (args : List (SimpleExpr c))
        (outs : List VarID) (md' : FuncMD) (func' : Func c) (p'' : Prog c),
      fetchFunc p fname' = Except.ok (FuncWithMD.mk md' func', p'') →
      (match func' with | Func.mk _ ps _ _ => args.length = ps.length) →
      (match func' with | Func.mk _ _ rs _ => outs.length = rs.length) → outs.Nodup →
      (∀ (env : Env c), ∃ vs : List (Value c), evalSimpleExprsToValue env args = Except.ok vs ∧
        ValuesMatchParams vs (match func' with | Func.mk _ ps _ _ => ps)) →
      TranslatesCorrectly gconf sconf specs
        (fun env => evalFuncCallCmd gconf p fname' args outs env)
        (fun symEnv => seFuncCall gconf sconf symEnv specs fname' args outs)) := by
  have hloop_eq : seExecFuncs.loop gconf p.reverse [] = Except.ok specs := by
    simp only [seExecFuncs, hnodup, Bool.false_eq_true, if_false] at hspecs_eq
    exact hspecs_eq
  have hwsp' : WellShapedProg gconf (p.reverse.reverse ++ ([] : Prog c)) := by
    simp only [List.reverse_reverse, List.append_nil]
    exact hwsp
  have hnodup' : hasDupFuncNames (p.reverse.reverse ++ ([] : Prog c)) = false := by
    simp only [List.reverse_reverse, List.append_nil]
    exact hnodup
  have hspecs_wf0 : ∀ spec ∈ ([] : List (FuncSpec c)), spec.f.name = spec.name :=
    fun spec hspec => absurd hspec (List.not_mem_nil)
  have hnames_corr0 : (([] : List (FuncSpec c)).map (·.name)) =
      (([] : Prog c)).map funcWithMDName := rfl
  have hHfc0 : ∀ (sconf : SymExecConfig c) (fname' : FName) (args : List (SimpleExpr c))
      (outs : List VarID) (md' : FuncMD) (func' : Func c) (p'' : Prog c),
      fetchFunc ([] : Prog c) fname' = Except.ok (FuncWithMD.mk md' func', p'') →
      (match func' with | Func.mk _ ps _ _ => args.length = ps.length) →
      (match func' with | Func.mk _ _ rs _ => outs.length = rs.length) → outs.Nodup →
      (∀ (env : Env c), ∃ vs : List (Value c), evalSimpleExprsToValue env args = Except.ok vs ∧
        ValuesMatchParams vs (match func' with | Func.mk _ ps _ _ => ps)) →
      TranslatesCorrectly gconf sconf ([] : List (FuncSpec c))
        (fun env => evalFuncCallCmd gconf ([] : Prog c) fname' args outs env)
        (fun symEnv => seFuncCall gconf sconf symEnv ([] : List (FuncSpec c)) fname' args outs) :=
    fun _ fname' _ _ _ _ _ hfetch _ _ _ _ => absurd hfetch (by simp [fetchFunc])
  obtain ⟨hspecs_wf, hnames_corr, hHfc⟩ := seExecFuncs_loop_correct gconf H_simple H_domain
    H_shape p.reverse [] [] hwsp' hnodup' hspecs_wf0 hnames_corr0 hHfc0 specs hloop_eq
  have hp_eq : p.reverse.reverse ++ ([] : Prog c) = p := by simp
  refine ⟨hspecs_wf, ?_, ?_⟩
  · rw [hnames_corr, hp_eq]
  · intro sconf fname' args outs md' func' p'' hfetch harglen houtlen houtnodup hargsdef
    have hfetch' : fetchFunc (p.reverse.reverse ++ ([] : Prog c)) fname' =
        Except.ok (FuncWithMD.mk md' func', p'') := by rw [hp_eq]; exact hfetch
    have := hHfc sconf fname' args outs md' func' p'' hfetch' harglen houtlen houtnodup hargsdef
    simpa [hp_eq] using this

/-- `seExecProg` wraps `seExecFuncs` in a `FFConstraintSystem` -- once `seExecFuncs_correct`
    gives whole-program `H_funcCall`-shaped correctness for the resulting `specs`, `seExecProg`'s
    own output (`macros := specs.map (·.f)`) directly carries that correctness. -/
theorem seExecProg_correct {c : ZKConfig} (gconf : GlobalConfig c) (p : ProgWithMD c)
    (H_simple : ∀ (specs : List (FuncSpec c)) (sconf : SymExecConfig c) (i : ComWithMD c),
      TranslatesCorrectly gconf sconf specs (fun env => evalSimpleCmd gconf env i)
        (fun symEnv => seSimpleCmd gconf sconf symEnv specs i))
    (H_domain : ∀ (specs : List (FuncSpec c)) (sconf' : SymExecConfig c) (symEnv' : SymEnv c)
        (cmds : List (ComWithMD c)) (spec : CmdsSpec c),
      seCmds gconf sconf' symEnv' specs cmds = Except.ok spec →
      ∀ id, symEnv'.contains id ↔ spec.outSymEnv.contains id)
    (H_shape : ∀ (specs : List (FuncSpec c)) (sconf' : SymExecConfig c) (symEnv' : SymEnv c)
        (tb' eb' : List (ComWithMD c)) (tbSpec' ebSpec' : CmdsSpec c),
      seCmds gconf sconf' symEnv' specs tb' = Except.ok tbSpec' →
      seCmds gconf sconf' symEnv' specs eb' = Except.ok ebSpec' →
      ∀ id svTb svEb, tbSpec'.outSymEnv.get? id = some svTb →
        ebSpec'.outSymEnv.get? id = some svEb → sameShape svTb svEb)
    (funcs : Prog c) (hp : p = ProgWithMD.mk (match p with | ProgWithMD.mk pmd _ => pmd) funcs)
    (hwsp : WellShapedProg gconf funcs) (hnodup : hasDupFuncNames funcs = false)
    (mainFuncName : FName) (cs : FFConstraintSystem c)
    (hcs_eq : seExecProg gconf p mainFuncName = Except.ok cs) :
    ∃ specs : List (FuncSpec c),
      cs = { macros := specs.map (·.f), main := mainFuncName } ∧
      (∀ spec ∈ specs, spec.f.name = spec.name) ∧
      specs.map (·.name) = funcs.map funcWithMDName ∧
      (∀ (sconf : SymExecConfig c) (fname' : FName) (args : List (SimpleExpr c))
          (outs : List VarID) (md' : FuncMD) (func' : Func c) (p'' : Prog c),
        fetchFunc funcs fname' = Except.ok (FuncWithMD.mk md' func', p'') →
        (match func' with | Func.mk _ ps _ _ => args.length = ps.length) →
        (match func' with | Func.mk _ _ rs _ => outs.length = rs.length) → outs.Nodup →
        (∀ (env : Env c), ∃ vs : List (Value c), evalSimpleExprsToValue env args = Except.ok vs ∧
          ValuesMatchParams vs (match func' with | Func.mk _ ps _ _ => ps)) →
        TranslatesCorrectly gconf sconf specs
          (fun env => evalFuncCallCmd gconf funcs fname' args outs env)
          (fun symEnv => seFuncCall gconf sconf symEnv specs fname' args outs)) := by
  rw [hp] at hcs_eq
  simp only [seExecProg] at hcs_eq
  cases hfuncSpecs : seExecFuncs gconf funcs with
  | error e =>
      rw [hfuncSpecs] at hcs_eq
      simp only [Bind.bind, Except.bind] at hcs_eq
      exact absurd hcs_eq (by simp)
  | ok specs =>
      rw [hfuncSpecs] at hcs_eq
      simp only [Bind.bind, Except.bind, pure, Except.pure] at hcs_eq
      injection hcs_eq with hcs_eq
      refine ⟨specs, hcs_eq.symm, ?_⟩
      exact seExecFuncs_correct gconf funcs H_simple H_domain H_shape hwsp hnodup specs hfuncSpecs

end Corellzk2smt.SymExec.ProgCorrectness
