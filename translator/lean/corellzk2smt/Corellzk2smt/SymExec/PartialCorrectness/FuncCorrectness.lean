import Corellzk2smt.SymExec.PartialCorrectness.Lemmas
import Corellzk2smt.SymExec.PartialCorrectness.Correctness
import Corellzk2smt.SymExec.PartialCorrectness.FuncCallCorrectness
import Corellzk2smt.SymExec.FuncCorrectness

/-
Partial-correctness analogue of `Corellzk2smt.SymExec.FuncCorrectness.seFunc_correct`.
See `PartialCorrectness/Lemmas.lean`'s header for the overall design, and
`PartialCorrectness/Correctness.lean`'s/`PartialCorrectness/FuncCallCorrectness.lean`'s headers
for the general translation pattern used here.

Every helper lemma in `SymExec/FuncCorrectness.lean` (`mintFreshParam_eq`,
`mintFreshParams_paramVars_shape`, `EnvMatches_mintFreshParams_bindInParams_general`,
`getOutParamsValues_construct_general`, ...) is reused unchanged via import -- none of it is
stated in terms of `TranslatesCorrectly` at all. Only the final theorem, `seFunc_correct` itself,
is restated here, and only ONE spot in its ~900-line body actually changes: the single call into
`seCmds_correct` for the function's own body. The old (unconditional) `seCmds_correct` produced
`bodySpec'`/`hbodySpec'_eq` existentially, which then had to be unified against the `bodySpec`
already known (from case-splitting on `seFunc`'s own definition) via `injection`/`subst`. The new
(conditional) `seCmds_correct` instead takes that already-known `bodySpec`/`hbs` directly as its
`spec`/`hspec_eq` arguments, so the `obtain .../subst` dance collapses to a direct `obtain` off the
call itself -- everything downstream in the proof is untouched, since it only ever referred to
`bodySpec` (the post-`subst` name in the old version), never `bodySpec'`.
-/
namespace Corellzk2smt.SymExec.PartialCorrectness.FuncCorrectness

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
open Corellzk2smt.SymExec.FuncCallCorrectness
open Corellzk2smt.SymExec.FuncCorrectness
open Corellzk2smt.SymExec.PartialCorrectness.Lemmas
open Corellzk2smt.SymExec.PartialCorrectness.Correctness
open Corellzk2smt.SymExec.PartialCorrectness.FuncCallCorrectness

/-- Exposes `seFunc`'s macro's own `params : List Var` field
    (`paramVars ++ retVars ++ auxVarsList` internally) *plus* the two disjointness facts needed to
    build a witness assignment for `seExecProg_call_complete`: the params/rets ranges don't
    overlap (`totalParamSize params ≤ retsOffset`), and every aux variable's own index avoids
    both ranges. This is a *different* theorem from `SymExec.FuncCorrectness.seFunc_f_params_split`
    (same name, different namespace) -- that one is a pure `seFunc`-unfold needing no correctness
    hypotheses, and gives everything *except* the disjointness facts, since those genuinely need
    `seCmds_correct`'s own `hbs_mono` (`nextVarId` only ever grows) to rule out the params/rets
    ranges overlapping -- a fact `seFunc`'s bare definition doesn't encode syntactically. -/
theorem seFunc_f_params_split {c : ZKConfig} (gconf : GlobalConfig c) (p : Prog c)
    (specs : List (FuncSpec c))
    (fname : FName) (md : FuncMD) (func : Func c) (p' : Prog c)
    (hfetch : fetchFunc p fname = Except.ok (FuncWithMD.mk md func, p'))
    (H_simple : ∀ (sconf : SymExecConfig c) (i : ComWithMD c),
      TranslatesCorrectly gconf sconf specs (fun env => evalSimpleCmd gconf env i)
        (fun symEnv => seSimpleCmd gconf sconf symEnv specs i))
    (H_funcCall : ∀ (sconf : SymExecConfig c) (fname' : FName) (args : List (SimpleExpr c))
        (outs : List VarID) (md' : FuncMD) (func' : Func c) (p'' : Prog c),
      fetchFunc p' fname' = Except.ok (FuncWithMD.mk md' func', p'') →
      (match func' with | Func.mk _ _ rets _ => outs.length = rets.length) →
      TranslatesCorrectly gconf sconf specs
        (fun env => evalFuncCallCmd gconf p' fname' args outs env)
        (fun symEnv => seFuncCall gconf sconf symEnv specs fname' args outs))
    (hspecs_cover : ∀ fname'', fname'' ∈ specs.map (·.name) → fname'' ∈ p'.map funcWithMDName)
    (hspecs_rets_cover : ∀ fname''' fspec', fetchFuncSpec specs fname''' = Except.ok fspec' →
      ∀ md func p''', fetchFunc p' fname''' = Except.ok (FuncWithMD.mk md func, p''') →
        match func with | Func.mk _ _ rets _ => fspec'.rets.length = rets.length)
    (hshaped : WellShapedCmds gconf p' (match func with | Func.mk _ _ _ body => body))
    (fspec : FuncSpec c) (hseFunc_eq : seFunc gconf specs func = Except.ok fspec) :
    ∃ (retsOffset : Nat) (auxVarsList : List Var),
      fspec.f.params =
        (List.range (totalParamSize fspec.params)).map (fun i => Var.ffv i) ++
        (List.range (totalParamSize fspec.rets)).map (fun i => Var.ffv (retsOffset + i)) ++
        auxVarsList ∧
      totalParamSize fspec.params ≤ retsOffset ∧
      (auxVarsList.filter isFFvVar).length = fspec.numAuxFFVars ∧
      (auxVarsList.filter (fun v => !isFFvVar v)).length = fspec.numAuxBoolVars ∧
      auxVarsList.Pairwise (fun a b => compare a b = .lt) ∧
      (∀ v ∈ auxVarsList, ∀ n, v = Var.ffv n →
        ¬(n < totalParamSize fspec.params) ∧
        ¬(retsOffset ≤ n ∧ n < retsOffset + totalParamSize fspec.rets)) := by
  cases func with
  | mk name params rets body =>
    simp only at hshaped
    simp only [seFunc] at hseFunc_eq
    cases hdup : hasDupNames (params.map (·.name)) || hasDupNames (rets.map (·.name)) with
    | true => simp [hdup] at hseFunc_eq
    | false =>
      simp only [hdup] at hseFunc_eq
      cases hmp : mintFreshParams (c := c) 0 params
          ((definedVarsOfFunc (Func.mk name params rets body)).foldl
            (fun env id => setVar env id (SymValue.simple (SimpleSymVal.const 0))) emptySymEnv)
        with
      | error e => simp [hmp] at hseFunc_eq
      | ok result =>
        obtain ⟨nv1, paramVars, inSymEnv⟩ := result
        simp only [hmp] at hseFunc_eq
        cases hbs : seCmds gconf { nextVarId := nv1 } inSymEnv specs body with
        | error e => simp [hbs] at hseFunc_eq
        | ok bodySpec =>
          simp only [hbs] at hseFunc_eq
          cases hmr : mintFreshRetsWithEq (c := c) bodySpec.nextVarId bodySpec.outSymEnv rets with
          | error e => simp [hmr] at hseFunc_eq
          | ok result2 =>
            obtain ⟨nv2, retVars, retBinds, retEqFormula⟩ := result2
            simp only [hmr] at hseFunc_eq
            injection hseFunc_eq with hseFunc_eq
            subst hseFunc_eq
            have hinSymEnv_below : varSetBelow (symEnvVars inSymEnv) nv1 :=
              mintFreshParams_symEnvVars_below 0 params _ (zeroSymEnv_below _ 0) nv1 paramVars
                inSymEnv hmp
            have hbody_pre : ∀ id, id ∈ definedVarsCmds
                (params.foldl (fun acc pm => acc.insert pm.name) emptyVarIDSet) body →
                inSymEnv.contains id := by
              intro id hid
              have hzero := zeroSymEnv_contains (c := c)
                (definedVarsOfFunc (Func.mk name params rets body)) id hid
              exact mintFreshParams_contains_mono 0 params _ nv1 paramVars inSymEnv hmp id hzero
            obtain ⟨_hbs_in, hbs_mono, _hbs_fresh, _hbs_below,
              _hbs_outbelow, _hbs_outfresh, _hbs_sound, _hbs_complete⟩ :=
              seCmds_correct gconf p' specs H_simple H_funcCall hspecs_cover hspecs_rets_cover
                (params.foldl (fun acc pm => acc.insert pm.name) emptyVarIDSet)
                { nextVarId := nv1 } body hshaped inSymEnv hinSymEnv_below hbody_pre bodySpec hbs
            set paramVarSet : VarSet := paramVars.foldl (fun acc v => acc.insert v) emptyVarSet
              with hParamVarSet_def
            set retVarSet : VarSet := retVars.foldl (fun acc v => acc.insert v) emptyVarSet
              with hRetVarSet_def
            set auxVarsList : List Var :=
              ((ffVarsOfFormula bodySpec.f ∪ bVarsOfFormula bodySpec.f ∪
                  ffVarsOfFormula retEqFormula ∪ bVarsOfFormula retEqFormula) \
                (paramVarSet ∪ retVarSet)).toList
              with hAuxVarsList_def
            have hpv := (mintFreshParams_paramVars_eq 0 params _ nv1 paramVars inSymEnv hmp).1
            have hnv1_eq : nv1 = totalParamSize params := by
              have := mintFreshParams_nv1_eq 0 params _ nv1 paramVars inSymEnv hmp
              omega
            have hrv := (mintFreshRetsWithEq_retVars_eq bodySpec.nextVarId bodySpec.outSymEnv rets
              nv2 retVars retBinds retEqFormula hmr).1
            have hParamVarSet_mem : ∀ v ∈ paramVars, v ∈ paramVarSet := fun v hv =>
              mem_foldl_insert_var paramVars v emptyVarSet (Or.inr hv)
            have hRetVarSet_mem : ∀ v ∈ retVars, v ∈ retVarSet := fun v hv =>
              mem_foldl_insert_var retVars v emptyVarSet (Or.inr hv)
            refine ⟨bodySpec.nextVarId, auxVarsList, ?_, hnv1_eq ▸ hbs_mono, ?_, ?_,
              (by rw [hAuxVarsList_def]; exact varSet_toList_pairwise_lt _), ?_⟩
            · simp only [hpv, hrv, Nat.zero_add]
            · rfl
            · show (auxVarsList.filter (fun v => !isFFvVar v)).length =
                auxVarsList.length - (auxVarsList.filter isFFvVar).length
              have := length_filter_add_length_filter_not isFFvVar auxVarsList
              omega
            · intro v hv n hveq
              have hvnotPR : v ∉ paramVarSet ∧ v ∉ retVarSet := by
                have hmem := Std.TreeSet.mem_toList.mp (hAuxVarsList_def ▸ hv)
                have := Std.TreeSet.mem_diff_iff.mp hmem
                exact ⟨fun hc => this.2 (Std.TreeSet.mem_union_of_left hc),
                  fun hc => this.2 (Std.TreeSet.mem_union_of_right hc)⟩
              constructor
              · intro hlt
                apply hvnotPR.1
                apply hParamVarSet_mem
                rw [hpv, hveq]
                exact List.mem_map.mpr ⟨n, List.mem_range.mpr hlt, by simp⟩
              · intro hcon
                obtain ⟨hge, hlt⟩ := hcon
                apply hvnotPR.2
                apply hRetVarSet_mem
                rw [hrv, hveq]
                exact List.mem_map.mpr ⟨n - bodySpec.nextVarId,
                  List.mem_range.mpr (nat_sub_lt_of_range hge hlt),
                  by rw [Nat.add_sub_cancel' hge]⟩

set_option maxHeartbeats 4000000 in
/-- Correctness of `seFunc`: the `FuncSpec` it produces for a function `func` (fetched from `p`
    at `fname`) satisfies exactly the two properties `seFuncCall_correct` needs from a callee's
    spec -- `hspec_retsShape` (a successful call always yields a right-*shaped* result, matching
    `fspec.rets`) and `H_specCorrect` (the call's formula, evaluated at all-const args/rets/aux,
    is satisfiable iff those are exactly the values `evalFunCall` computes). The macro-list `ms`
    used to evaluate `fspec.f`'s own call is `fspec.f :: specs.map (·.f)` -- `fspec` isn't a
    member of `specs` yet (it's freshly built, not yet inserted), so it has to be added
    explicitly for `fetchMacro` to find it; once `fetchMacro` finds it and evaluates its body,
    the macro list left over (`ms'`) is exactly `specs.map (·.f)`, matching what `H_funcCall`
    (and everything `seCmds_correct` needs for the function's own body) is stated over. -/
theorem seFunc_correct {c : ZKConfig} (gconf : GlobalConfig c) (p : Prog c)
    (specs : List (FuncSpec c))
    (fname : FName) (md : FuncMD) (func : Func c) (p' : Prog c)
    (hfetch : fetchFunc p fname = Except.ok (FuncWithMD.mk md func, p'))
    (hnodup_p : hasDupFuncNames p = false)
    (H_simple : ∀ (sconf : SymExecConfig c) (i : ComWithMD c),
      TranslatesCorrectly gconf sconf specs (fun env => evalSimpleCmd gconf env i)
        (fun symEnv => seSimpleCmd gconf sconf symEnv specs i))
    (H_funcCall : ∀ (sconf : SymExecConfig c) (fname' : FName) (args : List (SimpleExpr c))
        (outs : List VarID) (md' : FuncMD) (func' : Func c) (p'' : Prog c),
      fetchFunc p' fname' = Except.ok (FuncWithMD.mk md' func', p'') →
      (match func' with | Func.mk _ _ rets _ => outs.length = rets.length) →
      TranslatesCorrectly gconf sconf specs
        (fun env => evalFuncCallCmd gconf p' fname' args outs env)
        (fun symEnv => seFuncCall gconf sconf symEnv specs fname' args outs))
    (hspecs_cover : ∀ fname'', fname'' ∈ specs.map (·.name) → fname'' ∈ p'.map funcWithMDName)
    (hspecs_rets_cover : ∀ fname''' fspec', fetchFuncSpec specs fname''' = Except.ok fspec' →
      ∀ md func p''', fetchFunc p' fname''' = Except.ok (FuncWithMD.mk md func, p''') →
        match func with | Func.mk _ _ rets _ => fspec'.rets.length = rets.length)
    (hshaped : WellShapedCmds gconf p' (match func with | Func.mk _ _ _ body => body))
    (hspecs_wf : ∀ spec ∈ specs, spec.f.name = spec.name)
    (fspec : FuncSpec c) (hseFunc_eq : seFunc gconf specs func = Except.ok fspec) :
    (∀ (argVals : List (Value c)), ValuesMatchParams argVals fspec.params →
      ∀ (outVals : List (Value c)),
        evalFunCall gconf p fname argVals = Except.ok outVals →
        ValuesMatchParams outVals fspec.rets) ∧
    (∀ (badName : String), (∀ r, fetchFunc p' badName ≠ Except.ok r) →
      FormulaNamesBelow fspec.f.body badName) ∧
    (∀ (argVals : List (Value c)), ValuesMatchParams argVals fspec.params →
      (∀ (retVals : List (Value c)),
        evalFunCall gconf p fname argVals = Except.ok retVals →
        ValuesMatchParams retVals fspec.rets ∧
        ∃ (auxFF : List (FF c)) (auxBool : List Bool),
          auxFF.length = fspec.numAuxFFVars ∧ auxBool.length = fspec.numAuxBoolVars ∧
          ∀ (assign : Assignment c),
            evalFormula gconf assign
              (FFFormula.call fspec.f.name
                (flattenValuesParams argVals ++ flattenValuesParams retVals ++
                 auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
                 auxBool.map (fun v => MacroCallParam.const (Const.boolc v))))
              (fspec.f :: specs.map (·.f)) = Except.ok true) ∧
      (∀ (retVals : List (Value c)) (auxFF : List (FF c)) (auxBool : List Bool),
        ValuesMatchParams retVals fspec.rets → auxFF.length = fspec.numAuxFFVars →
        auxBool.length = fspec.numAuxBoolVars →
        (∀ (assign : Assignment c),
          evalFormula gconf assign
            (FFFormula.call fspec.f.name
              (flattenValuesParams argVals ++ flattenValuesParams retVals ++
               auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
               auxBool.map (fun v => MacroCallParam.const (Const.boolc v))))
            (fspec.f :: specs.map (·.f)) = Except.ok true) →
        evalFunCall gconf p fname argVals = Except.ok retVals)) := by
  cases func with
  | mk name params rets body =>
    simp only at hshaped
    simp only [seFunc] at hseFunc_eq
    cases hdup : hasDupNames (params.map (·.name)) || hasDupNames (rets.map (·.name)) with
    | true => simp [hdup] at hseFunc_eq
    | false =>
      simp only [hdup] at hseFunc_eq
      cases hmp : mintFreshParams (c := c) 0 params
          ((definedVarsOfFunc (Func.mk name params rets body)).foldl
            (fun env id => setVar env id (SymValue.simple (SimpleSymVal.const 0))) emptySymEnv)
        with
      | error e => simp [hmp] at hseFunc_eq
      | ok result =>
        obtain ⟨nv1, paramVars, inSymEnv⟩ := result
        simp only [hmp] at hseFunc_eq
        cases hbs : seCmds gconf { nextVarId := nv1 } inSymEnv specs body with
        | error e => simp [hbs] at hseFunc_eq
        | ok bodySpec =>
          simp only [hbs] at hseFunc_eq
          cases hmr : mintFreshRetsWithEq (c := c) bodySpec.nextVarId bodySpec.outSymEnv rets with
          | error e => simp [hmr] at hseFunc_eq
          | ok result2 =>
            obtain ⟨nv2, retVars, retBinds, retEqFormula⟩ := result2
            simp only [hmr] at hseFunc_eq
            injection hseFunc_eq with hseFunc_eq
            subst hseFunc_eq
            obtain ⟨hparamVars_ff, hparamVars_nodup, hparamVars_getD⟩ :=
              mintFreshParams_paramVars_shape 0 params _ nv1 paramVars inSymEnv hmp
            obtain ⟨hretVars_ff, hretVars_nodup, hretVars_getD⟩ :=
              mintFreshRetsWithEq_retVars_shape bodySpec.nextVarId bodySpec.outSymEnv rets
                nv2 retVars retBinds retEqFormula hmr
            have hinSymEnv_below : varSetBelow (symEnvVars inSymEnv) nv1 :=
              mintFreshParams_symEnvVars_below 0 params _ (zeroSymEnv_below _ 0) nv1 paramVars
                inSymEnv hmp
            have hbody_pre : ∀ id, id ∈ definedVarsCmds
                (params.foldl (fun acc pm => acc.insert pm.name) emptyVarIDSet) body →
                inSymEnv.contains id := by
              intro id hid
              have hzero := zeroSymEnv_contains (c := c)
                (definedVarsOfFunc (Func.mk name params rets body)) id hid
              exact mintFreshParams_contains_mono 0 params _ nv1 paramVars inSymEnv hmp id hzero
            obtain ⟨hbs_in, hbs_mono, hbs_fresh, hbs_below,
              hbs_outbelow, hbs_outfresh, hbs_sound, hbs_complete⟩ :=
              seCmds_correct gconf p' specs H_simple H_funcCall hspecs_cover hspecs_rets_cover
                (params.foldl (fun acc pm => acc.insert pm.name) emptyVarIDSet)
                { nextVarId := nv1 } body hshaped inSymEnv hinSymEnv_below hbody_pre bodySpec hbs
            have hcore : ∀ (argVals : List (Value c)), ValuesMatchParams argVals params →
                ∃ env0, bindInParams
                    (zeroInitEnv (definedVarsOfFunc (Func.mk name params rets body))) params
                    argVals = Except.ok env0 ∧
                  EnvMatches
                    { ff := fun k => if k < totalParamSize params
                        then (flattenValuesToFF argVals).getD k 0
                        else (default : Assignment c).ff k,
                      bool := (default : Assignment c).bool }
                    inSymEnv env0 := by
              intro argVals hargVals
              exact EnvMatches_mintFreshParams_bindInParams_general 0 params argVals _
                ((definedVarsOfFunc (Func.mk name params rets body)).foldl
                  (fun env id => setVar env id (SymValue.simple (SimpleSymVal.const 0)))
                  emptySymEnv)
                (zeroInitEnv (definedVarsOfFunc (Func.mk name params rets body)))
                hargVals
                (EnvMatches_zeroSymEnv_zeroInitEnv _
                  (definedVarsOfFunc (Func.mk name params rets body)))
                (fun i hi => by simp [hi])
                nv1 paramVars inSymEnv hmp
            refine ⟨?_, ?_, ?_⟩
            · intro argVals hargVals outVals hev
              obtain ⟨env0, hb0, _hmatch0⟩ := hcore argVals hargVals
              simp only [evalFunCall, hnodup_p, Bool.false_eq_true, if_false] at hev
              rw [hfetch] at hev
              simp only [hdup, hb0, Bool.false_eq_true, if_false] at hev
              cases hec : evalCmds gconf p' env0 body with
              | error e => simp [hec] at hev
              | ok bodyEnv' =>
                  rw [hec] at hev
                  simp only [] at hev
                  cases hgv : getOutParamsValues bodyEnv' rets with
                  | error e => rw [hgv] at hev; simp at hev
                  | ok vs =>
                      rw [hgv] at hev
                      simp only [] at hev
                      simp only [Except.ok.injEq] at hev
                      rw [← hev]
                      exact getOutParamsValues_shape bodyEnv' rets vs hgv
            · intro badName hunreach
              show FormulaNamesBelow (FFFormula.and bodySpec.f retEqFormula) badName
              exact ⟨seCmds_names_below gconf p' badName hunreach { nextVarId := nv1 } inSymEnv
                  specs hspecs_wf hspecs_cover body hshaped bodySpec hbs,
                mintFreshRetsWithEq_names_below bodySpec.nextVarId bodySpec.outSymEnv rets nv2
                  retVars retBinds retEqFormula hmr badName⟩
            · intro argVals hargVals
              set paramVarSet : VarSet := paramVars.foldl (fun acc v => acc.insert v) emptyVarSet
                with hParamVarSet_def
              set retVarSet : VarSet := retVars.foldl (fun acc v => acc.insert v) emptyVarSet
                with hRetVarSet_def
              set bodyVars : VarSet := ffVarsOfFormula bodySpec.f ∪ bVarsOfFormula bodySpec.f ∪
                ffVarsOfFormula retEqFormula ∪ bVarsOfFormula retEqFormula with hBodyVars_def
              set auxVarsList : List Var := (bodyVars \ (paramVarSet ∪ retVarSet)).toList
                with hAuxVarsList_def
              have hAuxSorted : auxVarsList.Pairwise (fun a b => compare a b = .lt) := by
                rw [hAuxVarsList_def]; exact varSet_toList_pairwise_lt _
              have hParamVarSet_mem : ∀ v ∈ paramVars, v ∈ paramVarSet := fun v hv =>
                mem_foldl_insert_var paramVars v emptyVarSet (Or.inr hv)
              have hRetVarSet_mem : ∀ v ∈ retVars, v ∈ retVarSet := fun v hv =>
                mem_foldl_insert_var retVars v emptyVarSet (Or.inr hv)
              have hBodyVars_bodySpec : ∀ v ∈ (ffVarsOfFormula bodySpec.f ∪ bVarsOfFormula bodySpec.f),
                  v ∈ bodyVars := by
                intro v hv
                rw [hBodyVars_def]
                rcases Std.TreeSet.mem_union_iff.mp hv with h | h
                · exact Std.TreeSet.mem_union_of_left (Std.TreeSet.mem_union_of_left
                    (Std.TreeSet.mem_union_of_left h))
                · exact Std.TreeSet.mem_union_of_left (Std.TreeSet.mem_union_of_left
                    (Std.TreeSet.mem_union_of_right h))
              have hBodyVars_retEq : ∀ v ∈ (ffVarsOfFormula retEqFormula ∪ bVarsOfFormula retEqFormula),
                  v ∈ bodyVars := by
                intro v hv
                rw [hBodyVars_def]
                rcases Std.TreeSet.mem_union_iff.mp hv with h | h
                · exact Std.TreeSet.mem_union_of_left (Std.TreeSet.mem_union_of_right h)
                · exact Std.TreeSet.mem_union_of_right h
              have hAux_of_bodyVars : ∀ v ∈ bodyVars, v ∉ paramVarSet → v ∉ retVarSet →
                  v ∈ auxVarsList := by
                intro v hv hnp hnr
                rw [hAuxVarsList_def, Std.TreeSet.mem_toList]
                apply Std.TreeSet.mem_diff_iff.mpr
                refine ⟨hv, ?_⟩
                intro hcon
                rcases Std.TreeSet.mem_union_iff.mp hcon with h | h
                · exact hnp h
                · exact hnr h
              have hnv1_eq : nv1 = totalParamSize params := by
                have := mintFreshParams_nv1_eq 0 params _ nv1 paramVars inSymEnv hmp
                omega
              have hParamVars_lt : ∀ v ∈ paramVars, varIndex v < nv1 := by
                intro v hv
                have heq := (mintFreshParams_paramVars_eq 0 params _ nv1 paramVars inSymEnv
                  hmp).1
                rw [heq] at hv
                obtain ⟨i, hi_range, hi_eq⟩ := List.mem_map.mp hv
                rw [List.mem_range] at hi_range
                rw [← hi_eq]
                simp only [varIndex]
                omega
              have hRetVars_ge : ∀ v ∈ retVars, bodySpec.nextVarId ≤ varIndex v := by
                intro v hv
                have heq := (mintFreshRetsWithEq_retVars_eq bodySpec.nextVarId bodySpec.outSymEnv
                  rets nv2 retVars retBinds retEqFormula hmr).1
                rw [heq] at hv
                obtain ⟨i, _, hi_eq⟩ := List.mem_map.mp hv
                rw [← hi_eq]
                simp only [varIndex]
                omega
              have hnv1_le_bs : nv1 ≤ bodySpec.nextVarId := hbs_mono
              have hNotParamVarSet_of_ge : ∀ v, nv1 ≤ varIndex v → v ∉ paramVarSet := by
                intro v hge hcon
                rcases foldl_insert_var_mem paramVars v emptyVarSet hcon with h1 | h1
                · exact absurd h1 (by simp)
                · have := hParamVars_lt v h1; omega
              have hNotRetVarSet_of_lt : ∀ v, varIndex v < bodySpec.nextVarId → v ∉ retVarSet := by
                intro v hlt hcon
                rcases foldl_insert_var_mem retVars v emptyVarSet hcon with h1 | h1
                · exact absurd h1 (by simp)
                · have := hRetVars_ge v h1; omega
              have hSpecVarsSub : ∀ v ∈ (ffVarsOfFormula bodySpec.f ∪ bVarsOfFormula bodySpec.f),
                  v ∈ paramVarSet ∨ v ∈ auxVarsList := by
                intro v hv
                rcases hbs_fresh v hv with hcase | hcase
                · rcases mintFreshParams_symEnvVars_subset 0 params _ nv1 paramVars inSymEnv hmp v
                    hcase with h1 | h1
                  · exact absurd
                      (zeroSymEnv_below (definedVarsOfFunc (Func.mk name params rets body)) 0 v h1)
                      (by omega)
                  · left; exact hParamVarSet_mem v h1
                · right
                  refine hAux_of_bodyVars v (hBodyVars_bodySpec v hv) (hNotParamVarSet_of_ge v hcase)
                    (hNotRetVarSet_of_lt v (hbs_below v hv))
              have hSvVarLocation : ∀ i, (hi : i < rets.length) → ∀ sv : SymValue c,
                  getVar bodySpec.outSymEnv (rets.getD i default).name = Except.ok sv →
                  ∀ w ∈ symValVars sv, w ∈ paramVarSet ∨ w ∈ auxVarsList := by
                intro i hi sv hgv w hw
                have hmemRetEq := mintFreshRetsWithEq_sv_vars_sub_general bodySpec.nextVarId
                  bodySpec.outSymEnv rets nv2 retVars retBinds retEqFormula hmr i hi sv hgv w hw
                have hwm : w ∈ symEnvVars bodySpec.outSymEnv := by
                  have hgv' : bodySpec.outSymEnv.get? (rets.getD i default).name = some sv :=
                    (getVar_eq_ok_iff_sym bodySpec.outSymEnv (rets.getD i default).name sv).mp hgv
                  exact getVar_mem_symEnvVars bodySpec.outSymEnv (rets.getD i default).name sv
                    hgv' w hw
                by_cases hp : w ∈ paramVarSet
                · left; exact hp
                · right
                  exact hAux_of_bodyVars w (hBodyVars_retEq w hmemRetEq) hp
                    (hNotRetVarSet_of_lt w (hbs_outbelow w hwm))
              have hParamVars_index : ∀ v ∈ paramVars,
                  ∃ i, i < totalParamSize params ∧ v = Var.ffv i := by
                intro v hv
                have heq := (mintFreshParams_paramVars_eq 0 params _ nv1 paramVars inSymEnv
                  hmp).1
                rw [heq] at hv
                obtain ⟨i, hi_range, hi_eq⟩ := List.mem_map.mp hv
                rw [List.mem_range] at hi_range
                exact ⟨i, hi_range, by rw [← hi_eq]; simp⟩
              have hRetVars_index : ∀ v ∈ retVars,
                  ∃ i, i < totalParamSize rets ∧ v = Var.ffv (bodySpec.nextVarId + i) := by
                intro v hv
                have heq := (mintFreshRetsWithEq_retVars_eq bodySpec.nextVarId bodySpec.outSymEnv
                  rets nv2 retVars retBinds retEqFormula hmr).1
                rw [heq] at hv
                obtain ⟨i, hi_range, hi_eq⟩ := List.mem_map.mp hv
                rw [List.mem_range] at hi_range
                exact ⟨i, hi_range, hi_eq.symm⟩
              set fMacro : FFMacro c :=
                { name := name, params := paramVars ++ retVars ++ auxVarsList,
                  body := FFFormula.and bodySpec.f retEqFormula } with hFMacro_def
              have hfm : fetchMacro gconf (fMacro :: specs.map (·.f)) fMacro.name =
                  Except.ok (fMacro, specs.map (·.f)) := by
                simp [fetchMacro, hFMacro_def]
              set auxFFVarsList := auxVarsList.filter isFFvVar with hAuxFFVarsList_def
              set auxBoolVarsList := auxVarsList.filter (fun v => !isFFvVar v)
                with hAuxBoolVarsList_def
              refine ⟨?_, ?_⟩
              · -- soundness
                intro retVals hev
                obtain ⟨env0, hb0, hmatch0⟩ := hcore argVals hargVals
                simp only [evalFunCall, hnodup_p, Bool.false_eq_true, if_false] at hev
                rw [hfetch] at hev
                simp only [hdup, hb0, Bool.false_eq_true, if_false] at hev
                cases hec : evalCmds gconf p' env0 body with
                | error e => simp [hec] at hev
                | ok bodyEnv' =>
                    rw [hec] at hev
                    simp only [] at hev
                    cases hgv : getOutParamsValues bodyEnv' rets with
                    | error e => rw [hgv] at hev; simp at hev
                    | ok vs =>
                        rw [hgv] at hev
                        simp only [] at hev
                        simp only [Except.ok.injEq] at hev
                        have hretVals_match : ValuesMatchParams retVals rets := by
                          have h0 := getOutParamsValues_shape bodyEnv' rets vs hgv
                          rw [hev] at h0
                          exact h0
                        have hretVals_len : (flattenValuesToFF retVals).length =
                            totalParamSize rets :=
                          flattenValuesToFF_length retVals rets hretVals_match
                        obtain ⟨assignment', hagreeFF, _hagreeBool, _hframeFF, _hframeBool,
                          hbodyEval, hmatch'⟩ := hbs_sound env0 _ hmatch0 bodyEnv' hec
                        refine ⟨hretVals_match, auxFFVarsList.map (fun v => assignment'.ff
                          (varIndex v)), auxBoolVarsList.map (fun v => assignment'.bool
                          (varIndex v)), ?_, ?_, ?_⟩
                        · rw [List.length_map]; rfl
                        · rw [List.length_map, hAuxBoolVarsList_def]
                          show (auxVarsList.filter (fun v => !isFFvVar v)).length =
                            auxVarsList.length -
                              (auxVarsList.filter isFFvVar).length
                          have := length_filter_add_length_filter_not isFFvVar auxVarsList
                          omega
                        · intro assign
                          have hargs_eq : (flattenValuesToFF argVals).length = paramVars.length := by
                            rw [flattenValuesToFF_length argVals params hargVals,
                              (mintFreshParams_paramVars_eq 0 params _ nv1 paramVars inSymEnv
                                hmp).1, List.length_map, List.length_range]
                          have hrets_eq : (flattenValuesToFF retVals).length = retVars.length := by
                            rw [hretVals_len,
                              (mintFreshRetsWithEq_retVars_eq bodySpec.nextVarId
                                bodySpec.outSymEnv rets nv2 retVars retBinds retEqFormula hmr).1,
                              List.length_map, List.length_range]
                          have hplen : paramVars.length = totalParamSize params := by
                            rw [(mintFreshParams_paramVars_eq 0 params _ nv1 paramVars inSymEnv
                              hmp).1, List.length_map, List.length_range]
                          have hrlen : retVars.length = totalParamSize rets := by
                            rw [(mintFreshRetsWithEq_retVars_eq bodySpec.nextVarId
                              bodySpec.outSymEnv rets nv2 retVars retBinds retEqFormula hmr).1,
                              List.length_map, List.length_range]
                          have hparams_le_bs : totalParamSize params ≤ bodySpec.nextVarId := by
                            rw [← hnv1_eq]; exact hnv1_le_bs
                          have hassignment'_param : ∀ k, k < totalParamSize params →
                              assignment'.ff k = (flattenValuesToFF argVals).getD k 0 := by
                            intro k hk
                            have hmem : Var.ffv k ∈ symEnvVars inSymEnv := by
                              simpa using mintFreshParams_block_mem_symEnvVars 0 params _
                                (hasDupNames_false_nodup _ (Bool.or_eq_false_iff.mp hdup).1)
                                nv1 paramVars inSymEnv hmp k hk
                            have heq := hagreeFF k hmem
                            simp only [hk, if_true] at heq
                            exact heq.symm
                          have hbodyEnv'_getD : ∀ i, i < rets.length →
                              bodyEnv'.get? (rets.getD i default).name =
                                some (retVals.getD i default) := by
                            intro i hi
                            have h1 := getOutParamsValues_getD bodyEnv' rets vs hgv i hi
                            rw [hev] at h1
                            exact h1
                          set auxFF := auxFFVarsList.map (fun v => assignment'.ff (varIndex v))
                            with hauxFF_def
                          set auxBool :=
                            auxBoolVarsList.map (fun v => assignment'.bool (varIndex v))
                            with hauxBool_def
                          have hforall_aux : List.Forall₂ varsArgsWellTyped auxVarsList
                              (auxFF.map (fun t => MacroCallParam.const (Const.ffc t)) ++
                                auxBool.map (fun t => MacroCallParam.const (Const.boolc t))) := by
                            apply forall2_aux_split auxVarsList hAuxSorted
                            · rw [hauxFF_def, List.length_map]
                            · rw [hauxBool_def, List.length_map, hAuxBoolVarsList_def]
                              show (auxVarsList.filter (fun v => !isFFvVar v)).length =
                                auxVarsList.length - (auxVarsList.filter isFFvVar).length
                              have := length_filter_add_length_filter_not isFFvVar auxVarsList
                              omega
                          simp only [evalFormula]
                          rw [hfm]
                          simp only []
                          rw [hFMacro_def]
                          rw [show paramVars ++ retVars ++ auxVarsList =
                              paramVars ++ (retVars ++ auxVarsList) from
                              (List.append_assoc paramVars retVars auxVarsList).symm ▸ rfl]
                          rw [show (flattenValuesParams argVals ++
                              flattenValuesParams retVals ++
                              auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
                              auxBool.map (fun v => MacroCallParam.const (Const.boolc v))) =
                              flattenValuesParams argVals ++
                                (flattenValuesParams retVals ++
                                  (auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
                                    auxBool.map
                                      (fun v => MacroCallParam.const (Const.boolc v)))) from
                              by rw [List.append_assoc, List.append_assoc]]
                          rw [flattenValuesParams_eq_map argVals, flattenValuesParams_eq_map
                            retVals]
                          simp only [newAssignment]
                          rw [newAssignment'_ff_prepend assign paramVars
                            (flattenValuesToFF argVals) (retVars ++ auxVarsList)
                            ((flattenValuesToFF retVals).map
                                (fun v => MacroCallParam.const (Const.ffc v)) ++
                              (auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
                                auxBool.map (fun v => MacroCallParam.const (Const.boolc v))))
                            (fun _ => 0) (fun _ => false) hargs_eq.symm hparamVars_ff]
                          rw [newAssignment'_ff_prepend assign retVars
                            (flattenValuesToFF retVals) auxVarsList
                            (auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
                              auxBool.map (fun v => MacroCallParam.const (Const.boolc v)))
                            (ffMapAfter paramVars (flattenValuesToFF argVals) (fun _ => 0))
                            (fun _ => false)
                            hrets_eq.symm hretVars_ff]
                          rw [← List.append_nil
                              (auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
                                auxBool.map (fun v => MacroCallParam.const (Const.boolc v))),
                            ← List.append_nil auxVarsList]
                          rw [newAssignment'_prepend assign auxVarsList
                            (auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
                              auxBool.map (fun v => MacroCallParam.const (Const.boolc v)))
                            [] []
                            (ffMapAfter retVars (flattenValuesToFF retVals)
                              (ffMapAfter paramVars (flattenValuesToFF argVals) (fun _ => 0)))
                            (fun _ => false) hforall_aux]
                          simp only [newAssignment']
                          set finalFFBase := (mapsAfter auxVarsList
                            (auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
                              auxBool.map (fun v => MacroCallParam.const (Const.boolc v)))
                            (ffMapAfter retVars (flattenValuesToFF retVals)
                              (ffMapAfter paramVars (flattenValuesToFF argVals) (fun _ => 0)))
                            (fun _ => false)).1 with hfinalFFBase_def
                          set finalBoolBase := (mapsAfter auxVarsList
                            (auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
                              auxBool.map (fun v => MacroCallParam.const (Const.boolc v)))
                            (ffMapAfter retVars (flattenValuesToFF retVals)
                              (ffMapAfter paramVars (flattenValuesToFF argVals) (fun _ => 0)))
                            (fun _ => false)).2 with hfinalBoolBase_def
                          have hA_ff_param : ∀ i, i < totalParamSize params →
                              finalFFBase i = (flattenValuesToFF argVals).getD i 0 := by
                            intro i hi
                            have hnotin_retVars : Var.ffv i ∉ retVars := by
                              intro hmem
                              obtain ⟨j, hj, hj_eq⟩ := hRetVars_index _ hmem
                              simp only [Var.ffv.injEq] at hj_eq
                              have h1 : i < bodySpec.nextVarId := lt_of_lt_of_le hi hparams_le_bs
                              rw [hj_eq] at h1
                              omega
                            have hnotin_aux : Var.ffv i ∉ auxVarsList := by
                              rw [hAuxVarsList_def, Std.TreeSet.mem_toList]
                              intro hcon
                              have hmemp : Var.ffv i ∈ paramVarSet :=
                                hParamVarSet_mem (Var.ffv i)
                                  (by
                                    have heq := (mintFreshParams_paramVars_eq 0 params _ nv1
                                      paramVars inSymEnv hmp).1
                                    rw [heq]
                                    exact List.mem_map.mpr ⟨i, by simp [hi], by simp⟩)
                              exact (Std.TreeSet.mem_diff_iff.mp hcon).2
                                (Std.TreeSet.mem_union_of_left hmemp)
                            rw [hfinalFFBase_def, mapsAfter_ff_frame auxVarsList _ _ _ i
                              hnotin_aux, ffMapAfter_frame retVars (flattenValuesToFF retVals) _ i
                              hnotin_retVars]
                            exact ffMapAfter_getD paramVars (flattenValuesToFF argVals)
                              (fun _ => 0) hargs_eq.symm
                              hparamVars_ff hparamVars_nodup i (by rw [hplen]; exact hi) i
                              (by simpa using hparamVars_getD i hi)
                          have hA_ff_ret : ∀ i, i < totalParamSize rets →
                              finalFFBase (bodySpec.nextVarId + i) =
                                (flattenValuesToFF retVals).getD i 0 := by
                            intro i hi
                            have hnotin_aux : Var.ffv (bodySpec.nextVarId + i) ∉ auxVarsList := by
                              rw [hAuxVarsList_def, Std.TreeSet.mem_toList]
                              intro hcon
                              have hmemr : Var.ffv (bodySpec.nextVarId + i) ∈ retVarSet :=
                                hRetVarSet_mem (Var.ffv (bodySpec.nextVarId + i))
                                  (by
                                    have heq := (mintFreshRetsWithEq_retVars_eq
                                      bodySpec.nextVarId bodySpec.outSymEnv rets nv2
                                      retVars retBinds retEqFormula hmr).1
                                    rw [heq]
                                    exact List.mem_map.mpr ⟨i, by simp [hi], by simp⟩)
                              exact (Std.TreeSet.mem_diff_iff.mp hcon).2
                                (Std.TreeSet.mem_union_of_right hmemr)
                            rw [hfinalFFBase_def, mapsAfter_ff_frame auxVarsList _ _ _
                              (bodySpec.nextVarId + i) hnotin_aux]
                            exact ffMapAfter_getD retVars (flattenValuesToFF retVals)
                              (ffMapAfter paramVars (flattenValuesToFF argVals) (fun _ => 0))
                              hrets_eq.symm
                              hretVars_ff hretVars_nodup i (by rw [hrlen]; exact hi)
                              (bodySpec.nextVarId + i) (hretVars_getD i hi)
                          have hA_ff_aux : ∀ v ∈ auxFFVarsList,
                              finalFFBase (varIndex v) = assignment'.ff (varIndex v) := by
                            intro v hv
                            obtain ⟨n, hn⟩ :=
                              (auxVarsList_ff_bool_split auxVarsList hAuxSorted).2.2.1 v
                                (by rw [hAuxFFVarsList_def] at hv; exact hv)
                            subst hn
                            have hmemAux : Var.ffv n ∈ auxVarsList := by
                              rw [hAuxFFVarsList_def] at hv
                              exact List.mem_of_mem_filter hv
                            simp only [varIndex]
                            rw [hfinalFFBase_def, hauxFF_def, hauxBool_def, hAuxFFVarsList_def,
                              hAuxBoolVarsList_def, List.map_map, List.map_map]
                            exact mapsAfter_reads_own_ff assignment' auxVarsList hAuxSorted _ _ n
                              hmemAux
                          have hA_bool_aux : ∀ v ∈ auxBoolVarsList,
                              finalBoolBase (varIndex v) = assignment'.bool (varIndex v) := by
                            intro v hv
                            obtain ⟨n, hn⟩ :=
                              (auxVarsList_ff_bool_split auxVarsList hAuxSorted).2.2.2 v
                                (by rw [hAuxBoolVarsList_def] at hv; exact hv)
                            subst hn
                            have hmemAux : Var.boolv n ∈ auxVarsList := by
                              rw [hAuxBoolVarsList_def] at hv
                              exact List.mem_of_mem_filter hv
                            simp only [varIndex]
                            rw [hfinalBoolBase_def, hauxFF_def, hauxBool_def, hAuxFFVarsList_def,
                              hAuxBoolVarsList_def, List.map_map, List.map_map]
                            exact mapsAfter_reads_own_bool assignment' auxVarsList hAuxSorted _ _ n
                              hmemAux
                          have hAssign_ff : agreesOnFF
                              (ffVarsOfFormula bodySpec.f ∪ bVarsOfFormula bodySpec.f)
                              { ff := finalFFBase, bool := finalBoolBase } assignment' := by
                            intro k hk
                            rcases hSpecVarsSub (Var.ffv k) hk with h1 | h1
                            · obtain ⟨i, hi, hi_eq⟩ :=
                                hParamVars_index (Var.ffv k)
                                  (by
                                    rcases foldl_insert_var_mem paramVars (Var.ffv k)
                                      emptyVarSet h1 with h2 | h2
                                    · exact absurd h2 (by simp)
                                    · exact h2)
                              injection hi_eq with hi_eq
                              subst hi_eq
                              show finalFFBase k = assignment'.ff k
                              rw [hA_ff_param k hi, hassignment'_param k hi]
                            · rw [hAuxFFVarsList_def] at hA_ff_aux
                              have hmemff : Var.ffv k ∈ auxVarsList.filter isFFvVar := by
                                rw [List.mem_filter]
                                exact ⟨h1, rfl⟩
                              show finalFFBase k = assignment'.ff k
                              have := hA_ff_aux (Var.ffv k) hmemff
                              simpa [varIndex] using this
                          have hAssign_bool : agreesOnBool
                              (ffVarsOfFormula bodySpec.f ∪ bVarsOfFormula bodySpec.f)
                              { ff := finalFFBase, bool := finalBoolBase } assignment' := by
                            intro k hk
                            rcases hSpecVarsSub (Var.boolv k) hk with h1 | h1
                            · exfalso
                              rcases foldl_insert_var_mem paramVars (Var.boolv k) emptyVarSet h1
                                with h2 | h2
                              · exact absurd h2 (by simp)
                              · obtain ⟨n, hn⟩ := hparamVars_ff (Var.boolv k) h2
                                exact absurd hn (by simp)
                            · have hmembool : Var.boolv k ∈ auxVarsList.filter
                                  (fun v => !isFFvVar v) := by
                                rw [List.mem_filter]
                                refine ⟨h1, ?_⟩
                                simp [isFFvVar]
                              show finalBoolBase k = assignment'.bool k
                              have := hA_bool_aux (Var.boolv k)
                                (by rw [hAuxBoolVarsList_def]; exact hmembool)
                              simpa [varIndex] using this
                          have hbodyEval : evalFormula gconf
                              { ff := finalFFBase, bool := finalBoolBase } bodySpec.f
                              (specs.map (·.f)) = Except.ok true := by
                            rw [evalFormula_congr gconf (specs.map (·.f)) bodySpec.f
                              { ff := finalFFBase, bool := finalBoolBase } assignment'
                              (agreesOnFF_mono (fun x hx => Std.TreeSet.mem_union_of_left hx)
                                hAssign_ff)
                              (agreesOnBool_mono (fun x hx => Std.TreeSet.mem_union_of_right hx)
                                hAssign_bool)]
                            exact hbodyEval
                          have hretEqEval : evalFormula gconf
                              { ff := finalFFBase, bool := finalBoolBase } retEqFormula
                              (specs.map (·.f)) = Except.ok true := by
                            apply retEqFormula_sound_general gconf (specs.map (·.f))
                              { ff := finalFFBase, bool := finalBoolBase } bodySpec.nextVarId
                              bodySpec.outSymEnv rets nv2 retVars retBinds retEqFormula hmr
                            intro i hi sv hgv j hj
                            have hmemw : ∀ w ∈ symValVars sv, w ∈ paramVarSet ∨
                                w ∈ auxVarsList := hSvVarLocation i hi sv hgv
                            have hgv' : bodySpec.outSymEnv.get? (rets.getD i default).name =
                                some sv :=
                              (getVar_eq_ok_iff_sym bodySpec.outSymEnv
                                (rets.getD i default).name sv).mp hgv
                            obtain ⟨v, hv1, hv2⟩ := hmatch'.2 (rets.getD i default).name sv hgv'
                            have hv_getD : v = retVals.getD i default := by
                              have hbv := hbodyEnv'_getD i hi
                              rw [hbv] at hv1
                              injection hv1 with hv1'
                              exact hv1'.symm
                            subst hv_getD
                            have hretVals_forall2 : List.Forall₂
                                (fun vv (p : Param) => ensureCorrectType vv p.type = Except.ok ())
                                retVals rets := hretVals_match
                            have hi' : i < retVals.length := by
                              rw [hretVals_forall2.length_eq]; exact hi
                            have htype_ok : ensureCorrectType (retVals.getD i default)
                                (rets.getD i default).type = Except.ok () :=
                              getD_pointwise_of_forall2
                                (fun vv p => ensureCorrectType vv p.type = Except.ok ()) default
                                default retVals rets hretVals_forall2 i hi'
                            obtain ⟨hlen_elems, helem_match⟩ :=
                              symValMatches_elems assignment'
                                sv (retVals.getD i default) (rets.getD i default).type htype_ok hv2
                            have hjlen : j < (symValueElems sv).length := by omega
                            have hterm_assignment' : evalTerm gconf assignment'
                                (simpleSymValToTerm ((symValueElems sv).getD j default))
                                (specs.map (·.f)) =
                                Except.ok
                                  ((flattenValueToFF (retVals.getD i default)).getD j 0) :=
                              evalTerm_simpleSymValToTerm gconf assignment'
                                ((symValueElems sv).getD j default)
                                ((flattenValueToFF (retVals.getD i default)).getD j 0)
                                (specs.map (·.f)) (helem_match j hj)
                            have hcongr : agreesOnFF
                                (ffVarsOfTerm (simpleSymValToTerm ((symValueElems sv).getD j
                                  default)))
                                { ff := finalFFBase, bool := finalBoolBase } assignment' ∧
                                agreesOnBool
                                  (bVarsOfTerm (simpleSymValToTerm ((symValueElems sv).getD j
                                    default)))
                                  { ff := finalFFBase, bool := finalBoolBase } assignment' := by
                              constructor
                              · intro k hk
                                rw [ffVarsOfTerm_simpleSymValToTerm] at hk
                                have hkmemw : Var.ffv k ∈ symValVars sv :=
                                  mem_symValVars_of_mem_symValueElems sv j hjlen (Var.ffv k) hk
                                rcases hmemw (Var.ffv k) hkmemw with h1 | h1
                                · obtain ⟨j', hj', hj_eq⟩ :=
                                    hParamVars_index (Var.ffv k)
                                      (by
                                        rcases foldl_insert_var_mem paramVars (Var.ffv k)
                                          emptyVarSet h1 with h2 | h2
                                        · exact absurd h2 (by simp)
                                        · exact h2)
                                  injection hj_eq with hj_eq
                                  subst hj_eq
                                  show finalFFBase k = assignment'.ff k
                                  rw [hA_ff_param k hj', hassignment'_param k hj']
                                · have hmemff : Var.ffv k ∈ auxVarsList.filter isFFvVar := by
                                    rw [List.mem_filter]; exact ⟨h1, rfl⟩
                                  show finalFFBase k = assignment'.ff k
                                  have := hA_ff_aux (Var.ffv k)
                                    (by rw [hAuxFFVarsList_def]; exact hmemff)
                                  simpa [varIndex] using this
                              · intro k hk
                                rw [bVarsOfTerm_simpleSymValToTerm] at hk
                                exact absurd hk Std.TreeSet.not_mem_emptyc
                            rw [evalTerm_congr gconf (specs.map (·.f))
                              (simpleSymValToTerm ((symValueElems sv).getD j default))
                              { ff := finalFFBase, bool := finalBoolBase } assignment'
                              hcongr.1 hcongr.2]
                            rw [hterm_assignment']
                            congr 1
                            show (flattenValueToFF (retVals.getD i default)).getD j 0 =
                              finalFFBase (bodySpec.nextVarId + totalParamSize (rets.take i) + j)
                            have hbound := totalParamSize_take_add_typeSize_le rets i hi
                            rw [show bodySpec.nextVarId + totalParamSize (rets.take i) + j =
                              bodySpec.nextVarId + (totalParamSize (rets.take i) + j) from
                              by omega]
                            rw [hA_ff_ret (totalParamSize (rets.take i) + j) (by omega)]
                            exact (flattenValuesToFF_getD_block retVals rets hretVals_match i hi
                              j hj).symm
                          simp only [evalFormula, hbodyEval, hretEqEval, Bool.and_self]
              · -- completeness
                intro retVals auxFF auxBool hretVals_match hauxFF_len hauxBool_len hassign_all
                have hev := hassign_all default
                have hargs_eq : (flattenValuesToFF argVals).length = paramVars.length := by
                  rw [flattenValuesToFF_length argVals params hargVals,
                    (mintFreshParams_paramVars_eq 0 params _ nv1 paramVars inSymEnv hmp).1,
                    List.length_map, List.length_range]
                have hrets_eq : (flattenValuesToFF retVals).length = retVars.length := by
                  rw [flattenValuesToFF_length retVals rets hretVals_match,
                    (mintFreshRetsWithEq_retVars_eq bodySpec.nextVarId bodySpec.outSymEnv rets nv2
                      retVars retBinds retEqFormula hmr).1,
                    List.length_map, List.length_range]
                have hplen : paramVars.length = totalParamSize params := by
                  rw [(mintFreshParams_paramVars_eq 0 params _ nv1 paramVars inSymEnv hmp).1,
                    List.length_map, List.length_range]
                have hrlen : retVars.length = totalParamSize rets := by
                  rw [(mintFreshRetsWithEq_retVars_eq bodySpec.nextVarId bodySpec.outSymEnv rets
                    nv2 retVars retBinds retEqFormula hmr).1, List.length_map, List.length_range]
                have hparams_le_bs : totalParamSize params ≤ bodySpec.nextVarId := by
                  rw [← hnv1_eq]; exact hnv1_le_bs
                have hforall_aux : List.Forall₂ varsArgsWellTyped auxVarsList
                    (auxFF.map (fun t => MacroCallParam.const (Const.ffc t)) ++
                      auxBool.map (fun t => MacroCallParam.const (Const.boolc t))) := by
                  apply forall2_aux_split auxVarsList hAuxSorted
                  · exact hauxFF_len
                  · exact hauxBool_len
                simp only [evalFormula] at hev
                rw [hfm] at hev
                simp only [] at hev
                rw [hFMacro_def] at hev
                rw [show paramVars ++ retVars ++ auxVarsList =
                    paramVars ++ (retVars ++ auxVarsList) from
                    (List.append_assoc paramVars retVars auxVarsList).symm ▸ rfl] at hev
                rw [show (flattenValuesParams argVals ++ flattenValuesParams retVals ++
                    auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
                    auxBool.map (fun v => MacroCallParam.const (Const.boolc v))) =
                    flattenValuesParams argVals ++
                      (flattenValuesParams retVals ++
                        (auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
                          auxBool.map (fun v => MacroCallParam.const (Const.boolc v)))) from
                    by rw [List.append_assoc, List.append_assoc]] at hev
                rw [flattenValuesParams_eq_map argVals, flattenValuesParams_eq_map retVals] at hev
                simp only [newAssignment] at hev
                rw [newAssignment'_ff_prepend default paramVars (flattenValuesToFF argVals)
                  (retVars ++ auxVarsList)
                  ((flattenValuesToFF retVals).map
                      (fun v => MacroCallParam.const (Const.ffc v)) ++
                    (auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
                      auxBool.map (fun v => MacroCallParam.const (Const.boolc v))))
                  (fun _ => 0) (fun _ => false) hargs_eq.symm hparamVars_ff] at hev
                rw [newAssignment'_ff_prepend default retVars (flattenValuesToFF retVals)
                  auxVarsList
                  (auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
                    auxBool.map (fun v => MacroCallParam.const (Const.boolc v)))
                  (ffMapAfter paramVars (flattenValuesToFF argVals) (fun _ => 0)) (fun _ => false)
                  hrets_eq.symm hretVars_ff] at hev
                rw [← List.append_nil
                    (auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
                      auxBool.map (fun v => MacroCallParam.const (Const.boolc v))),
                  ← List.append_nil auxVarsList] at hev
                rw [newAssignment'_prepend default auxVarsList
                  (auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
                    auxBool.map (fun v => MacroCallParam.const (Const.boolc v)))
                  [] []
                  (ffMapAfter retVars (flattenValuesToFF retVals)
                    (ffMapAfter paramVars (flattenValuesToFF argVals) (fun _ => 0)))
                  (fun _ => false) hforall_aux] at hev
                simp only [newAssignment'] at hev
                set finalFFBase := (mapsAfter auxVarsList
                  (auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
                    auxBool.map (fun v => MacroCallParam.const (Const.boolc v)))
                  (ffMapAfter retVars (flattenValuesToFF retVals)
                    (ffMapAfter paramVars (flattenValuesToFF argVals) (fun _ => 0)))
                  (fun _ => false)).1 with hfinalFFBase_def
                set finalBoolBase := (mapsAfter auxVarsList
                  (auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
                    auxBool.map (fun v => MacroCallParam.const (Const.boolc v)))
                  (ffMapAfter retVars (flattenValuesToFF retVals)
                    (ffMapAfter paramVars (flattenValuesToFF argVals) (fun _ => 0)))
                  (fun _ => false)).2 with hfinalBoolBase_def
                have hA_ff_param : ∀ i, i < totalParamSize params →
                    finalFFBase i = (flattenValuesToFF argVals).getD i 0 := by
                  intro i hi
                  have hnotin_retVars : Var.ffv i ∉ retVars := by
                    intro hmem
                    obtain ⟨j, hj, hj_eq⟩ := hRetVars_index _ hmem
                    simp only [Var.ffv.injEq] at hj_eq
                    have h1 : i < bodySpec.nextVarId := lt_of_lt_of_le hi hparams_le_bs
                    rw [hj_eq] at h1
                    omega
                  have hnotin_aux : Var.ffv i ∉ auxVarsList := by
                    rw [hAuxVarsList_def, Std.TreeSet.mem_toList]
                    intro hcon
                    have hmemp : Var.ffv i ∈ paramVarSet :=
                      hParamVarSet_mem (Var.ffv i)
                        (by
                          have heq := (mintFreshParams_paramVars_eq 0 params _ nv1
                            paramVars inSymEnv hmp).1
                          rw [heq]
                          exact List.mem_map.mpr ⟨i, by simp [hi], by simp⟩)
                    exact (Std.TreeSet.mem_diff_iff.mp hcon).2
                      (Std.TreeSet.mem_union_of_left hmemp)
                  rw [hfinalFFBase_def, mapsAfter_ff_frame auxVarsList _ _ _ i
                    hnotin_aux, ffMapAfter_frame retVars (flattenValuesToFF retVals) _ i
                    hnotin_retVars]
                  exact ffMapAfter_getD paramVars (flattenValuesToFF argVals) (fun _ => 0)
                    hargs_eq.symm
                    hparamVars_ff hparamVars_nodup i (by rw [hplen]; exact hi) i
                    (by simpa using hparamVars_getD i hi)
                have hA_ff_ret : ∀ i, i < totalParamSize rets →
                    finalFFBase (bodySpec.nextVarId + i) =
                      (flattenValuesToFF retVals).getD i 0 := by
                  intro i hi
                  have hnotin_aux : Var.ffv (bodySpec.nextVarId + i) ∉ auxVarsList := by
                    rw [hAuxVarsList_def, Std.TreeSet.mem_toList]
                    intro hcon
                    have hmemr : Var.ffv (bodySpec.nextVarId + i) ∈ retVarSet :=
                      hRetVarSet_mem (Var.ffv (bodySpec.nextVarId + i))
                        (by
                          have heq := (mintFreshRetsWithEq_retVars_eq
                            bodySpec.nextVarId bodySpec.outSymEnv rets nv2
                            retVars retBinds retEqFormula hmr).1
                          rw [heq]
                          exact List.mem_map.mpr ⟨i, by simp [hi], by simp⟩)
                    exact (Std.TreeSet.mem_diff_iff.mp hcon).2
                      (Std.TreeSet.mem_union_of_right hmemr)
                  rw [hfinalFFBase_def, mapsAfter_ff_frame auxVarsList _ _ _
                    (bodySpec.nextVarId + i) hnotin_aux]
                  exact ffMapAfter_getD retVars (flattenValuesToFF retVals)
                    (ffMapAfter paramVars (flattenValuesToFF argVals) (fun _ => 0)) hrets_eq.symm
                    hretVars_ff hretVars_nodup i (by rw [hrlen]; exact hi)
                    (bodySpec.nextVarId + i) (hretVars_getD i hi)
                set A : Assignment c := { ff := finalFFBase, bool := finalBoolBase } with hA_def
                have hA_ff_param' : ∀ i, i < totalParamSize params →
                    A.ff i = (flattenValuesToFF argVals).getD i 0 := hA_ff_param
                have hA_ff_ret' : ∀ i, i < totalParamSize rets →
                    A.ff (bodySpec.nextVarId + i) = (flattenValuesToFF retVals).getD i 0 :=
                  hA_ff_ret
                simp only [evalFormula] at hev
                cases hb : evalFormula gconf A bodySpec.f (specs.map (·.f)) with
                | error e => rw [hb] at hev; simp at hev
                | ok vb =>
                    rw [hb] at hev
                    cases hr : evalFormula gconf A retEqFormula (specs.map (·.f)) with
                    | error e => rw [hr] at hev; simp at hev
                    | ok vr =>
                        rw [hr] at hev
                        simp only [Except.ok.injEq] at hev
                        have hvb : vb = true := by by_contra hcon; simp [hcon] at hev
                        have hvr : vr = true := by by_contra hcon; simp [hcon] at hev
                        have hbodyEval_A : evalFormula gconf A bodySpec.f (specs.map (·.f)) =
                            Except.ok true := by rw [hb, hvb]
                        have hretEqEval_A : evalFormula gconf A retEqFormula (specs.map (·.f)) =
                            Except.ok true := by rw [hr, hvr]
                        obtain ⟨env0, hb0, hmatch0⟩ := hcore argVals hargVals
                        have hAssign_ff_param : agreesOnFF (symEnvVars inSymEnv)
                            { ff := fun k => if k < totalParamSize params
                                then (flattenValuesToFF argVals).getD k 0
                                else (default : Assignment c).ff k,
                              bool := (default : Assignment c).bool } A := by
                          intro k hk
                          rcases mintFreshParams_symEnvVars_subset 0 params _ nv1 paramVars
                              inSymEnv hmp (Var.ffv k) hk with h1 | h1
                          · exact absurd
                              (zeroSymEnv_below (definedVarsOfFunc (Func.mk name params rets
                                body)) 0 (Var.ffv k) h1) (by omega)
                          · obtain ⟨i, hi, hi_eq⟩ := hParamVars_index (Var.ffv k) h1
                            injection hi_eq with hi_eq
                            subst hi_eq
                            show (if k < totalParamSize params then
                              (flattenValuesToFF argVals).getD k 0
                              else (default : Assignment c).ff k) = A.ff k
                            simp only [hi, if_true]
                            exact (hA_ff_param' k hi).symm
                        obtain ⟨env', hec', hmatch'⟩ := hbs_complete env0 _ hmatch0 A
                          hAssign_ff_param hbodyEval_A
                        have hgv' : ∀ j, (hj : j < rets.length) →
                            env'.get? (rets.getD j default).name =
                              some (retVals.getD j default) := by
                          intro j hj
                          obtain ⟨sv, hsv⟩ := mintFreshRetsWithEq_getVar_exists_general
                            bodySpec.nextVarId bodySpec.outSymEnv rets nv2 retVars
                            retBinds retEqFormula hmr j hj
                          have hsv' : bodySpec.outSymEnv.get? (rets.getD j default).name =
                              some sv :=
                            (getVar_eq_ok_iff_sym bodySpec.outSymEnv (rets.getD j default).name
                              sv).mp hsv
                          obtain ⟨v, hv1, hv2⟩ := hmatch'.2 (rets.getD j default).name sv hsv'
                          have hretVals_forall2 : List.Forall₂
                              (fun vv (p : Param) => ensureCorrectType vv p.type = Except.ok ())
                              retVals rets := hretVals_match
                          have hj' : j < retVals.length := by
                            rw [hretVals_forall2.length_eq]; exact hj
                          have htype_ok : ensureCorrectType (retVals.getD j default)
                              (rets.getD j default).type = Except.ok () :=
                            getD_pointwise_of_forall2
                              (fun vv p => ensureCorrectType vv p.type = Except.ok ()) default
                              default retVals rets hretVals_forall2 j hj'
                          have hv_shape : ensureCorrectType v (rets.getD j default).type =
                              Except.ok () :=
                            ensureCorrectType_of_mintFreshRetsWithEq_getVar A
                              bodySpec.nextVarId bodySpec.outSymEnv rets nv2 retVars retBinds
                              retEqFormula hmr j hj sv v hsv hv2
                          have hveq_flat : ∀ k, k < typeSize (rets.getD j default).type →
                              (flattenValueToFF v).getD k 0 =
                                (flattenValueToFF (retVals.getD j default)).getD k 0 := by
                            intro k hk
                            have hterm := retEqFormula_complete_general gconf (specs.map (·.f)) A
                              bodySpec.nextVarId bodySpec.outSymEnv rets nv2 retVars
                              retBinds retEqFormula hmr hretEqEval_A j hj sv hsv k hk
                            have hbound := totalParamSize_take_add_typeSize_le rets j hj
                            rw [show bodySpec.nextVarId + totalParamSize (rets.take j) + k =
                                bodySpec.nextVarId + (totalParamSize (rets.take j) + k) from
                                by omega] at hterm
                            rw [hA_ff_ret' (totalParamSize (rets.take j) + k) (by omega)] at hterm
                            rw [flattenValuesToFF_getD_block retVals rets hretVals_match j hj k
                              hk] at hterm
                            obtain ⟨_, helem_match⟩ :=
                              symValMatches_elems A sv v (rets.getD j default).type hv_shape hv2
                            have helemk_match := helem_match k hk
                            have hevalv := evalTerm_simpleSymValToTerm gconf A
                              ((symValueElems sv).getD k default) ((flattenValueToFF v).getD k 0)
                              (specs.map (·.f)) helemk_match
                            rw [hevalv] at hterm
                            injection hterm with hterm
                          have hv_eq : v = retVals.getD j default :=
                            value_eq_of_flatten_eq v (retVals.getD j default)
                              (rets.getD j default).type hv_shape htype_ok hveq_flat
                          rw [hv1, hv_eq]
                        have hgOPV : getOutParamsValues env' rets = Except.ok retVals :=
                          getOutParamsValues_construct_general env' rets retVals hretVals_match
                            hgv'
                        simp only [evalFunCall, hnodup_p, Bool.false_eq_true, if_false]
                        rw [hfetch]
                        simp only [hdup, hb0, Bool.false_eq_true, if_false]
                        simp only [] at hec'
                        rw [hec']
                        simp only []
                        rw [hgOPV]

/-- Partial-correctness analogue of
    `Corellzk2smt.SymExec.FuncCorrectness.seFuncCall_correct_via_seFunc`: single-function wrapper
    connecting `seFunc_correct` to `seFuncCall_correct` (both conditional forms). The proof body
    is *identical* to the old, unconditional version -- `seFunc_correct`'s and
    `seFuncCall_correct`'s conclusions are directly `TranslatesCorrectly` values (conditional
    now, but still just values of that type), so composing them needs no existential-witness
    bookkeeping to begin with; only the referenced theorems (and hence the conclusion's own
    `TranslatesCorrectly`) are the new, conditional ones. -/
theorem seFuncCall_correct_via_seFunc {c : ZKConfig} (gconf : GlobalConfig c) (p : Prog c)
    (specs : List (FuncSpec c)) (sconf : SymExecConfig c)
    (fname : FName) (md : FuncMD) (func : Func c) (p' : Prog c)
    (hfetch : fetchFunc p fname = Except.ok (FuncWithMD.mk md func, p'))
    (hnodup_p : hasDupFuncNames p = false)
    (H_simple : ∀ (sconf : SymExecConfig c) (i : ComWithMD c),
      TranslatesCorrectly gconf sconf specs (fun env => evalSimpleCmd gconf env i)
        (fun symEnv => seSimpleCmd gconf sconf symEnv specs i))
    (H_funcCall : ∀ (sconf : SymExecConfig c) (fname' : FName) (args : List (SimpleExpr c))
        (outs : List VarID) (md' : FuncMD) (func' : Func c) (p'' : Prog c),
      fetchFunc p' fname' = Except.ok (FuncWithMD.mk md' func', p'') →
      (match func' with | Func.mk _ _ rets _ => outs.length = rets.length) →
      TranslatesCorrectly gconf sconf specs
        (fun env => evalFuncCallCmd gconf p' fname' args outs env)
        (fun symEnv => seFuncCall gconf sconf symEnv specs fname' args outs))
    (hspecs_cover : ∀ fname'', fname'' ∈ specs.map (·.name) → fname'' ∈ p'.map funcWithMDName)
    (hspecs_rets_cover : ∀ fname''' fspec', fetchFuncSpec specs fname''' = Except.ok fspec' →
      ∀ md func p''', fetchFunc p' fname''' = Except.ok (FuncWithMD.mk md func, p''') →
        match func with | Func.mk _ _ rets _ => fspec'.rets.length = rets.length)
    (hshaped : WellShapedCmds gconf p' (match func with | Func.mk _ _ _ body => body))
    (hspecs_wf : ∀ spec ∈ specs, spec.f.name = spec.name)
    (fspec : FuncSpec c) (hseFunc_eq : seFunc gconf specs func = Except.ok fspec)
    (args : List (SimpleExpr c)) (outs : List VarID) :
    TranslatesCorrectly gconf sconf (fspec :: specs)
      (fun env => evalFuncCallCmd gconf p fname args outs env)
      (fun symEnv => seFuncCall gconf sconf symEnv (fspec :: specs) fname args outs) := by
  cases func with
  | mk name params rets body =>
      obtain ⟨hfname, hfparams, hfrets⟩ :=
        seFunc_eq_shape gconf specs name params rets body fspec hseFunc_eq
      have hname_eq : name = fname :=
        fetchFunc_name_eq p fname md name params rets body p' hfetch
      have hspec_eq : fetchFuncSpec (fspec :: specs) fname = Except.ok fspec := by
        simp [fetchFuncSpec, hfname, hname_eq]
      obtain ⟨hspec_retsShape, _hnamesBelow, H_specCorrect⟩ := seFunc_correct gconf p specs fname
        md (Func.mk name params rets body) p' hfetch hnodup_p H_simple H_funcCall hspecs_cover
        hspecs_rets_cover hshaped hspecs_wf fspec hseFunc_eq
      exact seFuncCall_correct gconf p (fspec :: specs) sconf fname args outs fspec hspec_eq
        hspec_retsShape H_specCorrect

end Corellzk2smt.SymExec.PartialCorrectness.FuncCorrectness
