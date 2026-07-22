import Corellzk2smt.SymExec.PartialCorrectness.Lemmas
import Corellzk2smt.SymExec.FuncCallCorrectness

/-
Partial-correctness analogue of `Corellzk2smt.SymExec.FuncCallCorrectness.seFuncCall_correct`.
See `PartialCorrectness/Lemmas.lean`'s header for the overall design, and
`PartialCorrectness/Correctness.lean`'s header for the general translation pattern used here.

Every helper lemma in `SymExec/FuncCallCorrectness.lean` (`flattenArgVals_eq`, the
`mintFreshRets`/`mintFreshAuxParams` family, `constify*`, ...) is reused unchanged via import --
none of it is stated in terms of `TranslatesCorrectly` at all, just explicit facts about
`seFuncCall`'s own internal helper functions. Only the final theorem, `seFuncCall_correct`
itself, is restated here: its whole proof body (deriving `hseFuncCall_eq`, `hmono`, `hfresh`,
`hbelowProof`, `houtbelow`, `houtfresh`, `hsound`, `hcomplete`) is *identical* to the old,
unconditional version -- none of it depends on whether the surrounding `TranslatesCorrectly` is
conditional or not, it's all just facts about what `seFuncCall` computes. The only change is at
the very start (`intro symEnv hbelow spec hspec_witness` instead of `intro symEnv hbelow`, taking
the produced `spec` and success witness as given) and the very end (deriving `spec = {...}` via
`injection`/`subst` from `hspec_witness` against the freshly-computed `hseFuncCall_eq`, instead of
supplying the same literal as an existential witness).
-/
namespace Corellzk2smt.SymExec.PartialCorrectness.FuncCallCorrectness

open Corellzk2smt.Config
open Corellzk2smt.Language.Core.Syntax.AST
open Corellzk2smt.Language.Core.Semantics.Basic
open Corellzk2smt.Language.Core.Semantics.BigStep
open Corellzk2smt.SymExec.Basic
open Corellzk2smt.SymExec.BigStep
open Corellzk2smt.FFConstraints.Basic
open Corellzk2smt.FFConstraints.Satisfiability
open Corellzk2smt.FFConstraints.Satisfiability_th
open Corellzk2smt.SymExec.Lemmas
open Corellzk2smt.SymExec.Correctness
open Corellzk2smt.SymExec.FuncCallCorrectness
open Corellzk2smt.SymExec.PartialCorrectness.Lemmas

theorem seFuncCall_correct {c : ZKConfig} (gconf : GlobalConfig c) (p : Prog c)
    (specs : List (FuncSpec c)) (sconf : SymExecConfig c)
    (fname : FName) (args : List (SimpleExpr c)) (outs : List VarID)
    (fspec : FuncSpec c) (hspec_eq : fetchFuncSpec specs fname = Except.ok fspec)
    (houts_len : outs.length = fspec.rets.length)
    (hspec_retsShape : ∀ (argVals : List (Value c)), ValuesMatchParams argVals fspec.params →
      ∀ (outVals : List (Value c)),
        evalFunCall gconf p fname argVals = Except.ok outVals →
        ValuesMatchParams outVals fspec.rets)
    (H_specCorrect :
      ∀ (argVals : List (Value c)), ValuesMatchParams argVals fspec.params →
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
                (specs.map (·.f)) = Except.ok true) ∧
        (∀ (retVals : List (Value c)) (auxFF : List (FF c)) (auxBool : List Bool),
          ValuesMatchParams retVals fspec.rets → auxFF.length = fspec.numAuxFFVars →
          auxBool.length = fspec.numAuxBoolVars →
          (∀ (assign : Assignment c),
            evalFormula gconf assign
              (FFFormula.call fspec.f.name
                (flattenValuesParams argVals ++ flattenValuesParams retVals ++
                 auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
                 auxBool.map (fun v => MacroCallParam.const (Const.boolc v))))
              (specs.map (·.f)) = Except.ok true) →
          evalFunCall gconf p fname argVals = Except.ok retVals)) :
    TranslatesCorrectly gconf sconf specs
      (fun env => evalFuncCallCmd gconf p fname args outs env)
      (fun symEnv => seFuncCall gconf sconf symEnv specs fname args outs) := by
  intro symEnv hbelow spec hspec_witness
  have hspec_witness' := hspec_witness
  simp only [seFuncCall, hspec_eq] at hspec_witness'
  cases hargSV_eq : resolveSimpleExprsToSymValue symEnv args with
  | error e => rw [hargSV_eq] at hspec_witness'; simp at hspec_witness'
  | ok argSymVals =>
  rw [hargSV_eq] at hspec_witness'
  simp only [] at hspec_witness'
  cases hinputParams_eq : flattenArgVals fspec.params argSymVals with
  | error e => rw [hinputParams_eq] at hspec_witness'; simp at hspec_witness'
  | ok inputParams =>
  rw [hinputParams_eq] at hspec_witness'
  simp only [] at hspec_witness'
  have hargSV_forall : List.Forall₂ (fun s sv => resolveSimpleExprToSymValue symEnv s = Except.ok sv)
      args argSymVals :=
    resolveSimpleExprsToSymValue_forall_of_ok symEnv args argSymVals hargSV_eq
  have hargSV_vars : ∀ sv ∈ argSymVals, symValVars sv ⊆ symEnvVars symEnv := by
    intro sv hsv
    obtain ⟨s, _hs, hres⟩ := forall2_mem_right hargSV_forall sv hsv
    exact resolveSimpleExprToSymValue_vars_subset symEnv s sv hres
  have hshape : List.Forall₂ (fun (pm : Param) sv => symValueMatchesType sv pm.type)
      fspec.params argSymVals :=
    flattenArgVals_defined_of_ok fspec.params argSymVals inputParams hinputParams_eq
  have hflatten : flattenArgVals fspec.params argSymVals =
      Except.ok (flattenSymValuesParams argSymVals) :=
    flattenArgVals_eq fspec.params argSymVals hshape
  rcases hmintR : mintFreshRets (c := c) sconf.nextVarId fspec.rets with
    ⟨nv1, outputParams, outVals⟩
  rcases hmintA : mintFreshAuxParams (c := c) nv1 fspec.numAuxFFVars fspec.numAuxBoolVars with
    ⟨nv2, auxParams⟩
  have houtVals_len : outVals.length = fspec.rets.length := by
    have hh := mintFreshRets_outVals_length (c := c) sconf.nextVarId fspec.rets
    rw [hmintR] at hh; exact hh
  obtain ⟨outSymEnv', hOutSymEnv⟩ := setVars_defined_of_length_eq outs outVals symEnv
    (houts_len.trans houtVals_len.symm)
  set cf : FFFormula c :=
    FFFormula.call fspec.f.name (flattenSymValuesParams argSymVals ++ outputParams ++ auxParams)
    with hcf
  have hseFuncCall_eq : seFuncCall gconf sconf symEnv specs fname args outs =
      Except.ok { inSymEnv := symEnv, outSymEnv := outSymEnv', f := cf, nextVarId := nv2 } := by
    simp only [seFuncCall, hspec_eq, hargSV_eq, hflatten, hmintR, hmintA, hOutSymEnv, hcf]
  have hstartLeNv1 : sconf.nextVarId ≤ nv1 := by
    have hh := mintFreshRets_mono (c := c) sconf.nextVarId fspec.rets
    rw [hmintR] at hh; exact hh
  have hnv1LeNv2 : nv1 ≤ nv2 := by
    have hh := mintFreshAuxParams_mono (c := c) nv1 fspec.numAuxFFVars fspec.numAuxBoolVars
    rw [hmintA] at hh; exact hh
  have hmono : sconf.nextVarId ≤ nv2 := hstartLeNv1.trans hnv1LeNv2
  have houtParams_mem : ∀ mcp ∈ outputParams, ∃ n, mcp = MacroCallParam.var (Var.ffv n) ∧
      sconf.nextVarId ≤ n ∧ n < nv1 := by
    intro mcp hmcp
    have h := mintFreshRets_params_mem (c := c) fspec.rets sconf.nextVarId
    rw [hmintR] at h
    exact h mcp hmcp
  have hauxParams_mem : ∀ mcp ∈ auxParams,
      (∃ n, mcp = MacroCallParam.var (Var.ffv n) ∧ nv1 ≤ n ∧ n < nv1 + fspec.numAuxFFVars) ∨
      (∃ n, mcp = MacroCallParam.var (Var.boolv n) ∧ nv1 + fspec.numAuxFFVars ≤ n ∧ n < nv2) := by
    intro mcp hmcp
    have h := mintFreshAuxParams_params_mem (c := c) nv1 fspec.numAuxFFVars fspec.numAuxBoolVars
    rw [hmintA] at h
    exact h mcp hmcp
  have hfresh : ∀ v ∈ ffVarsOfFormula cf ∪ bVarsOfFormula cf,
      v ∈ symEnvVars symEnv ∨ sconf.nextVarId ≤ varIndex v := by
    intro v hv
    simp only [hcf, Std.TreeSet.mem_union_iff] at hv
    rcases hv with hvff | hvb
    · simp only [ffVarsOfFormula] at hvff
      rcases ffVars_call_mem_elim
          (flattenSymValuesParams argSymVals ++ outputParams ++ auxParams) emptyVarSet v hvff
        with hcon | ⟨n, hxmem, hveq⟩
      · exact absurd hcon Std.TreeSet.not_mem_emptyc
      rcases List.mem_append.mp hxmem with hx1 | hx3
      · rcases List.mem_append.mp hx1 with hxIn | hxOut
        · left
          rcases flattenSymValuesParams_mem_vars argSymVals (MacroCallParam.var (Var.ffv n)) hxIn
            with ⟨cv, hceq⟩ | ⟨n', hveq', v', hv'mem, hn'mem⟩
          · injection hceq
          · injection hveq' with hveq'
            apply hargSV_vars v' hv'mem
            rw [hveq, hveq']
            exact hn'mem
        · right
          obtain ⟨m, hmeq, hn1, _hn2⟩ := houtParams_mem (MacroCallParam.var (Var.ffv n)) hxOut
          injection hmeq with hmeq
          injection hmeq with hmeq
          simp only [varIndex, hveq]
          rw [hmeq]; exact hn1
      · right
        rcases hauxParams_mem (MacroCallParam.var (Var.ffv n)) hx3 with
          ⟨m, hmeq, hn1, _hn2⟩ | ⟨m, hmeq, _hn1, _hn2⟩
        · injection hmeq with hmeq
          injection hmeq with hmeq
          simp only [varIndex, hveq]
          rw [hmeq]; exact hstartLeNv1.trans hn1
        · injection hmeq with hmeq; injection hmeq
    · simp only [bVarsOfFormula] at hvb
      rcases bVars_call_mem_elim
          (flattenSymValuesParams argSymVals ++ outputParams ++ auxParams) emptyVarSet v hvb
        with hcon | ⟨n, hxmem, hveq⟩
      · exact absurd hcon Std.TreeSet.not_mem_emptyc
      rcases List.mem_append.mp hxmem with hx1 | hx3
      · rcases List.mem_append.mp hx1 with hxIn | hxOut
        · rcases flattenSymValuesParams_mem_vars argSymVals (MacroCallParam.var (Var.boolv n)) hxIn
            with ⟨cv, hceq⟩ | ⟨n', hveq', _⟩
          · injection hceq
          · injection hveq' with hveq'; injection hveq'
        · obtain ⟨m, hmeq, _hn1, _hn2⟩ := houtParams_mem (MacroCallParam.var (Var.boolv n)) hxOut
          injection hmeq with hmeq; injection hmeq
      · right
        rcases hauxParams_mem (MacroCallParam.var (Var.boolv n)) hx3 with
          ⟨m, hmeq, _hn1, _hn2⟩ | ⟨m, hmeq, hn1, _hn2⟩
        · injection hmeq with hmeq; injection hmeq
        · injection hmeq with hmeq
          injection hmeq with hmeq
          simp only [varIndex, hveq]
          rw [hmeq]
          exact hstartLeNv1.trans ((Nat.le_add_right nv1 fspec.numAuxFFVars).trans hn1)
  have hnv1eq : nv1 = sconf.nextVarId + totalParamSize fspec.rets := by
    obtain ⟨h, _⟩ := mintFreshRets_eq (c := c) sconf.nextVarId fspec.rets
    rw [hmintR] at h
    simpa using h
  have hnv2eq : nv2 = nv1 + fspec.numAuxFFVars + fspec.numAuxBoolVars := by
    have h : (mintFreshAuxParams (c := c) nv1 fspec.numAuxFFVars fspec.numAuxBoolVars).1 =
        nv1 + fspec.numAuxFFVars + fspec.numAuxBoolVars := by simp [mintFreshAuxParams]
    rw [hmintA] at h; exact h
  have hbelowProof : varSetBelow (ffVarsOfFormula cf ∪ bVarsOfFormula cf) nv2 := by
    intro v hv
    simp only [hcf, Std.TreeSet.mem_union_iff] at hv
    rcases hv with hvff | hvb
    · simp only [ffVarsOfFormula] at hvff
      rcases ffVars_call_mem_elim
          (flattenSymValuesParams argSymVals ++ outputParams ++ auxParams) emptyVarSet v hvff
        with hcon | ⟨n, hxmem, hveq⟩
      · exact absurd hcon Std.TreeSet.not_mem_emptyc
      rcases List.mem_append.mp hxmem with hx1 | hx3
      · rcases List.mem_append.mp hx1 with hxIn | hxOut
        · rcases flattenSymValuesParams_mem_vars argSymVals (MacroCallParam.var (Var.ffv n)) hxIn
            with ⟨cv, hceq⟩ | ⟨n', hveq', v', hv'mem, hn'mem⟩
          · injection hceq
          · injection hveq' with hveq'
            have hmem : v ∈ symEnvVars symEnv := by
              apply hargSV_vars v' hv'mem
              rw [hveq, hveq']
              exact hn'mem
            have hbv := hbelow v hmem
            rw [hveq] at hbv
            simp only [varIndex] at hbv
            rw [hveq]
            simp only [varIndex]
            exact Nat.lt_of_lt_of_le hbv hmono
        · obtain ⟨m, hmeq, _hn1, hn2⟩ := houtParams_mem (MacroCallParam.var (Var.ffv n)) hxOut
          injection hmeq with hmeq; injection hmeq with hmeq
          simp only [varIndex, hveq]
          rw [hmeq]
          exact Nat.lt_of_lt_of_le hn2 hnv1LeNv2
      · rcases hauxParams_mem (MacroCallParam.var (Var.ffv n)) hx3 with
          ⟨m, hmeq, _hn1, hn2⟩ | ⟨m, hmeq, _hn1, _hn2⟩
        · injection hmeq with hmeq; injection hmeq with hmeq
          simp only [varIndex, hveq]
          rw [hmeq]
          exact Nat.lt_of_lt_of_le hn2 (by omega)
        · injection hmeq with hmeq; injection hmeq
    · simp only [bVarsOfFormula] at hvb
      rcases bVars_call_mem_elim
          (flattenSymValuesParams argSymVals ++ outputParams ++ auxParams) emptyVarSet v hvb
        with hcon | ⟨n, hxmem, hveq⟩
      · exact absurd hcon Std.TreeSet.not_mem_emptyc
      rcases List.mem_append.mp hxmem with hx1 | hx3
      · rcases List.mem_append.mp hx1 with hxIn | hxOut
        · rcases flattenSymValuesParams_mem_vars argSymVals (MacroCallParam.var (Var.boolv n)) hxIn
            with ⟨cv, hceq⟩ | ⟨n', hveq', _⟩
          · injection hceq
          · injection hveq' with hveq'; injection hveq'
        · obtain ⟨m, hmeq, _hn1, _hn2⟩ := houtParams_mem (MacroCallParam.var (Var.boolv n)) hxOut
          injection hmeq with hmeq; injection hmeq
      · rcases hauxParams_mem (MacroCallParam.var (Var.boolv n)) hx3 with
          ⟨m, hmeq, _hn1, _hn2⟩ | ⟨m, hmeq, _hn1, hn2⟩
        · injection hmeq with hmeq; injection hmeq
        · injection hmeq with hmeq; injection hmeq with hmeq
          simp only [varIndex, hveq]
          rw [hmeq]
          exact hn2
  have houtVarsElim : ∀ v ∈ symEnvVars outSymEnv',
      v ∈ symEnvVars symEnv ∨ ∃ sv ∈ outVals, v ∈ symValVars sv :=
    symEnvVars_setVars_subset outs outVals symEnv outSymEnv' hOutSymEnv
  have houtVals_vars : ∀ sv ∈ outVals, ∀ v ∈ symValVars sv,
      ∃ n, v = Var.ffv n ∧ sconf.nextVarId ≤ n ∧ n < nv1 := by
    intro sv hsv v hv
    have h := mintFreshRets_outVals_vars_below (c := c) fspec.rets sconf.nextVarId
    rw [hmintR] at h
    simp only [] at h
    exact h sv hsv v hv
  have houtbelow : varSetBelow (symEnvVars outSymEnv') nv2 := by
    intro v hv
    rcases houtVarsElim v hv with h1 | ⟨sv, hsv, hvsv⟩
    · exact Nat.lt_of_lt_of_le (hbelow v h1) hmono
    · obtain ⟨n, hveq, _hn1, hn2⟩ := houtVals_vars sv hsv v hvsv
      rw [hveq]
      simp only [varIndex]
      exact Nat.lt_of_lt_of_le hn2 hnv1LeNv2
  have houtfresh : ∀ v ∈ symEnvVars outSymEnv',
      v ∈ symEnvVars symEnv ∨ sconf.nextVarId ≤ varIndex v := by
    intro v hv
    rcases houtVarsElim v hv with h1 | ⟨sv, hsv, hvsv⟩
    · exact Or.inl h1
    · obtain ⟨n, hveq, hn1, _hn2⟩ := houtVals_vars sv hsv v hvsv
      right
      rw [hveq]
      simp only [varIndex]
      exact hn1
  have hsound : ∀ (env : Env c) (assignment : Assignment c),
      EnvMatches assignment symEnv env →
      ∀ env', evalFuncCallCmd gconf p fname args outs env = Except.ok env' →
        ∃ assignment',
          agreesOnFF (symEnvVars symEnv) assignment assignment' ∧
          agreesOnBool (symEnvVars symEnv) assignment assignment' ∧
          (∀ n, Var.ffv n ∉ ffVarsOfFormula cf ∪ bVarsOfFormula cf →
            assignment'.ff n = assignment.ff n) ∧
          (∀ n, Var.boolv n ∉ ffVarsOfFormula cf ∪ bVarsOfFormula cf →
            assignment'.bool n = assignment.bool n) ∧
          evalFormula gconf assignment' cf (specs.map (·.f)) = Except.ok true ∧
          EnvMatches assignment' outSymEnv' env' := by
    intro env assignment hmatch env' hconcrete
    simp only [evalFuncCallCmd] at hconcrete
    obtain ⟨vs, hvs_eq, hvs_forall⟩ :=
      list_resolveSimpleExprToSymValue_correct symEnv env assignment hmatch args argSymVals
        hargSV_forall
    simp only [hvs_eq] at hconcrete
    have hvs_shape : ValuesMatchParams vs fspec.params := by
      have hchain := forall2_chain
        (fun (pm : Param) sv v (hp : symValueMatchesType sv pm.type)
            (hm : symValMatches assignment sv v) =>
          ensureCorrectType_of_symValueMatchesType_symValMatches assignment sv v pm.type hp hm)
        hshape hvs_forall
      exact forall2_flip hchain
    cases hFC : evalFunCall gconf p fname vs with
    | error e => rw [hFC] at hconcrete; simp at hconcrete
    | ok retVals =>
        rw [hFC] at hconcrete
        simp only [] at hconcrete
        have houtShape : ValuesMatchParams retVals fspec.rets :=
          hspec_retsShape vs hvs_shape retVals hFC
        obtain ⟨_hlen', auxFF, auxBool, hauxFF_len, hauxBool_len, hformula⟩ :=
          (H_specCorrect vs hvs_shape).1 retVals hFC
        cases hSV : Corellzk2smt.Language.Core.Semantics.Basic.setVars env outs retVals with
        | error e => rw [hSV] at hconcrete; simp at hconcrete
        | ok vars_env =>
            rw [hSV] at hconcrete
            injection hconcrete with hconcrete
            let assignment' : Assignment c := {
              ff := fun k =>
                if sconf.nextVarId ≤ k ∧ k < nv1 then
                  (flattenValuesToFF retVals).getD (k - sconf.nextVarId) 0
                else if nv1 ≤ k ∧ k < nv1 + fspec.numAuxFFVars then auxFF.getD (k - nv1) 0
                else assignment.ff k,
              bool := fun k =>
                if nv1 + fspec.numAuxFFVars ≤ k ∧ k < nv2 then
                  auxBool.getD (k - (nv1 + fspec.numAuxFFVars)) false
                else assignment.bool k
            }
            have hassignment'_ff : ∀ k, assignment'.ff k =
                if sconf.nextVarId ≤ k ∧ k < nv1 then
                  (flattenValuesToFF retVals).getD (k - sconf.nextVarId) 0
                else if nv1 ≤ k ∧ k < nv1 + fspec.numAuxFFVars then auxFF.getD (k - nv1) 0
                else assignment.ff k := fun _ => rfl
            have hassignment'_bool : ∀ k, assignment'.bool k =
                if nv1 + fspec.numAuxFFVars ≤ k ∧ k < nv2 then
                  auxBool.getD (k - (nv1 + fspec.numAuxFFVars)) false
                else assignment.bool k := fun _ => rfl
            have hagreeFF : agreesOnFF (symEnvVars symEnv) assignment assignment' := by
              intro n hn
              have hlt : n < sconf.nextVarId := hbelow _ hn
              have hneg1 : ¬(sconf.nextVarId ≤ n ∧ n < nv1) :=
                fun h => absurd h.1 (Nat.not_le.mpr hlt)
              have hneg2 : ¬(nv1 ≤ n ∧ n < nv1 + fspec.numAuxFFVars) :=
                fun h => absurd h.1 (Nat.not_le.mpr (Nat.lt_of_lt_of_le hlt hstartLeNv1))
              rw [hassignment'_ff, if_neg hneg1, if_neg hneg2]
            have hagreeBool : agreesOnBool (symEnvVars symEnv) assignment assignment' :=
              agreesOnBool_symEnvVars symEnv assignment assignment'
            have hframeFF : ∀ n, Var.ffv n ∉ ffVarsOfFormula cf ∪ bVarsOfFormula cf →
                assignment'.ff n = assignment.ff n := by
              intro n hn
              rw [hassignment'_ff]
              by_cases hc1 : sconf.nextVarId ≤ n ∧ n < nv1
              · exfalso
                apply hn
                apply Std.TreeSet.mem_union_of_left
                simp only [hcf, ffVarsOfFormula]
                have hbound : n - sconf.nextVarId < totalParamSize fspec.rets :=
                  nat_sub_lt_of_range hc1.1 (hnv1eq ▸ hc1.2)
                have hmem := mintFreshRets_params_mem_of_index (c := c) fspec.rets sconf.nextVarId
                  (n - sconf.nextVarId) hbound
                have heqn : sconf.nextVarId + (n - sconf.nextVarId) = n :=
                  Nat.add_sub_cancel' hc1.1
                rw [heqn, hmintR] at hmem
                exact mem_ffVars_call_of_mem _ emptyVarSet n
                  (List.mem_append_left _ (List.mem_append_right _ hmem))
              · rw [if_neg hc1]
                by_cases hc2 : nv1 ≤ n ∧ n < nv1 + fspec.numAuxFFVars
                · exfalso
                  apply hn
                  apply Std.TreeSet.mem_union_of_left
                  simp only [hcf, ffVarsOfFormula]
                  have hbound : n - nv1 < fspec.numAuxFFVars := nat_sub_lt_of_range hc2.1 hc2.2
                  have hmem := (mintFreshAuxParams_params_mem_of_index (c := c) nv1
                    fspec.numAuxFFVars fspec.numAuxBoolVars).1 (n - nv1) hbound
                  have heqn : nv1 + (n - nv1) = n := Nat.add_sub_cancel' hc2.1
                  rw [heqn, hmintA] at hmem
                  exact mem_ffVars_call_of_mem _ emptyVarSet n (List.mem_append_right _ hmem)
                · rw [if_neg hc2]
            have hframeBool : ∀ n, Var.boolv n ∉ ffVarsOfFormula cf ∪ bVarsOfFormula cf →
                assignment'.bool n = assignment.bool n := by
              intro n hn
              rw [hassignment'_bool]
              by_cases hc : nv1 + fspec.numAuxFFVars ≤ n ∧ n < nv2
              · exfalso
                apply hn
                apply Std.TreeSet.mem_union_of_right
                simp only [hcf, bVarsOfFormula]
                have hbound : n - (nv1 + fspec.numAuxFFVars) < fspec.numAuxBoolVars :=
                  nat_sub_lt_of_range hc.1 (hnv2eq ▸ hc.2)
                have hmem := (mintFreshAuxParams_params_mem_of_index (c := c) nv1
                  fspec.numAuxFFVars fspec.numAuxBoolVars).2
                  (n - (nv1 + fspec.numAuxFFVars)) hbound
                have heqn : nv1 + fspec.numAuxFFVars + (n - (nv1 + fspec.numAuxFFVars)) = n :=
                  Nat.add_sub_cancel' hc.1
                rw [heqn, hmintA] at hmem
                exact mem_bVars_call_of_mem _ emptyVarSet n (List.mem_append_right _ hmem)
              · rw [if_neg hc]
            have hEvalFormula : evalFormula gconf assignment' cf (specs.map (·.f)) =
                Except.ok true := by
              rw [hcf, evalFormula_call_constify gconf assignment' fspec.f.name
                (flattenSymValuesParams argSymVals ++ outputParams ++ auxParams)
                (specs.map (·.f))]
              have hInputEq : (flattenSymValuesParams argSymVals).map
                  (constifyMacroCallParam assignment') = flattenValuesParams vs :=
                constify_input_symvalues_eq symEnv assignment assignment'
                  (fun n hn => (hagreeFF n hn).symm) argSymVals vs hargSV_vars hvs_forall
              have houtRange : ∀ i, i < totalParamSize fspec.rets →
                  assignment'.ff (sconf.nextVarId + i) = (flattenValuesToFF retVals).getD i 0 := by
                intro i hi
                have hcond : sconf.nextVarId ≤ sconf.nextVarId + i ∧
                    sconf.nextVarId + i < nv1 := by omega
                have hidx : sconf.nextVarId + i - sconf.nextVarId = i := by omega
                rw [hassignment'_ff, if_pos hcond, hidx]
              have hOutputEq : outputParams.map (constifyMacroCallParam assignment') =
                  flattenValuesParams retVals := by
                have h := mintFreshRets_constify_eq assignment' fspec.rets sconf.nextVarId
                  retVals houtShape houtRange
                rw [hmintR] at h
                exact h
              have hauxFFRange : ∀ i, i < fspec.numAuxFFVars →
                  assignment'.ff (nv1 + i) = auxFF.getD i 0 := by
                intro i hi
                have hcond1 : ¬(sconf.nextVarId ≤ nv1 + i ∧ nv1 + i < nv1) := by omega
                have hcond2 : nv1 ≤ nv1 + i ∧ nv1 + i < nv1 + fspec.numAuxFFVars := by omega
                have hidx : nv1 + i - nv1 = i := by omega
                rw [hassignment'_ff, if_neg hcond1, if_pos hcond2, hidx]
              have hauxBoolRange : ∀ i, i < fspec.numAuxBoolVars →
                  assignment'.bool (nv1 + fspec.numAuxFFVars + i) = auxBool.getD i false := by
                intro i hi
                have hcond : nv1 + fspec.numAuxFFVars ≤ nv1 + fspec.numAuxFFVars + i ∧
                    nv1 + fspec.numAuxFFVars + i < nv2 := by omega
                have hidx : nv1 + fspec.numAuxFFVars + i - (nv1 + fspec.numAuxFFVars) = i := by
                  omega
                rw [hassignment'_bool, if_pos hcond, hidx]
              have hAuxEq : auxParams.map (constifyMacroCallParam assignment') =
                  auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
                    auxBool.map (fun v => MacroCallParam.const (Const.boolc v)) := by
                have h := mintFreshAuxParams_constify_eq assignment' nv1 fspec.numAuxFFVars
                  fspec.numAuxBoolVars auxFF auxBool hauxFF_len hauxBool_len hauxFFRange
                  hauxBoolRange
                rw [hmintA] at h
                exact h
              rw [List.map_append, List.map_append, hInputEq, hOutputEq, hAuxEq]
              simpa [List.append_assoc] using hformula assignment'
            have hEnvMatchesMid : EnvMatches assignment' symEnv env :=
              EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagreeFF hmatch
            have hOutValsMatch : List.Forall₂ (symValMatches assignment') outVals retVals := by
              have houtRange : ∀ i, i < totalParamSize fspec.rets →
                  assignment'.ff (sconf.nextVarId + i) = (flattenValuesToFF retVals).getD i 0 := by
                intro i hi
                have hcond : sconf.nextVarId ≤ sconf.nextVarId + i ∧
                    sconf.nextVarId + i < nv1 := by omega
                have hidx : sconf.nextVarId + i - sconf.nextVarId = i := by omega
                rw [hassignment'_ff, if_pos hcond, hidx]
              have h := mintFreshRets_outVals_symValMatches assignment' fspec.rets
                sconf.nextVarId retVals houtShape houtRange
              rw [hmintR] at h
              exact h
            have hEnvMatchesOut : EnvMatches assignment' outSymEnv' vars_env :=
              EnvMatches_setVars outs outVals retVals assignment' symEnv env
                hEnvMatchesMid hOutValsMatch outSymEnv' hOutSymEnv vars_env hSV
            refine ⟨assignment', hagreeFF, hagreeBool, hframeFF, hframeBool, hEvalFormula, ?_⟩
            rw [← hconcrete]
            exact hEnvMatchesOut
  have hcomplete : ∀ (env : Env c) (assignment : Assignment c),
      EnvMatches assignment symEnv env →
      ∀ assignment', agreesOnFF (symEnvVars symEnv) assignment assignment' →
        evalFormula gconf assignment' cf (specs.map (·.f)) = Except.ok true →
        ∃ env', evalFuncCallCmd gconf p fname args outs env = Except.ok env' ∧
          EnvMatches assignment' outSymEnv' env' := by
    intro env assignment hmatch assignment' hagree hformula_given
    obtain ⟨vs, hvs_eq, hvs_forall⟩ :=
      list_resolveSimpleExprToSymValue_correct symEnv env assignment hmatch args argSymVals
        hargSV_forall
    have hvs_shape : ValuesMatchParams vs fspec.params := by
      have hchain := forall2_chain
        (fun (pm : Param) sv v (hp : symValueMatchesType sv pm.type)
            (hm : symValMatches assignment sv v) =>
          ensureCorrectType_of_symValueMatchesType_symValMatches assignment sv v pm.type hp hm)
        hshape hvs_forall
      exact forall2_flip hchain
    set retVals : List (Value c) := reconstructValues assignment'.ff fspec.rets sconf.nextVarId
      with hretVals_def
    set auxFF : List (FF c) :=
      (List.range fspec.numAuxFFVars).map (fun i => assignment'.ff (nv1 + i)) with hauxFF_def
    set auxBool : List Bool :=
      (List.range fspec.numAuxBoolVars).map
        (fun i => assignment'.bool (nv1 + fspec.numAuxFFVars + i)) with hauxBool_def
    have hretVals_shape : ValuesMatchParams retVals fspec.rets := by
      rw [hretVals_def]
      exact reconstructValues_matches assignment'.ff fspec.rets sconf.nextVarId
    have hretVals_len : retVals.length = fspec.rets.length := hretVals_shape.length_eq
    have hauxFF_len : auxFF.length = fspec.numAuxFFVars := by rw [hauxFF_def]; simp
    have hauxBool_len : auxBool.length = fspec.numAuxBoolVars := by rw [hauxBool_def]; simp
    have houtRange : ∀ i, i < totalParamSize fspec.rets →
        assignment'.ff (sconf.nextVarId + i) = (flattenValuesToFF retVals).getD i 0 := by
      intro i hi
      rw [hretVals_def, reconstructValues_flattenToFF, range_map_getD _ _ i hi 0]
    have hauxFFRange : ∀ i, i < fspec.numAuxFFVars →
        assignment'.ff (nv1 + i) = auxFF.getD i 0 := by
      intro i hi; rw [hauxFF_def, range_map_getD _ _ i hi 0]
    have hauxBoolRange : ∀ i, i < fspec.numAuxBoolVars →
        assignment'.bool (nv1 + fspec.numAuxFFVars + i) = auxBool.getD i false := by
      intro i hi; rw [hauxBool_def, range_map_getD _ _ i hi false]
    have hInputEq : (flattenSymValuesParams argSymVals).map (constifyMacroCallParam assignment') =
        flattenValuesParams vs :=
      constify_input_symvalues_eq symEnv assignment assignment' (fun n hn => (hagree n hn).symm)
        argSymVals vs hargSV_vars hvs_forall
    have hOutputEq : outputParams.map (constifyMacroCallParam assignment') =
        flattenValuesParams retVals := by
      have h := mintFreshRets_constify_eq assignment' fspec.rets sconf.nextVarId retVals
        hretVals_shape houtRange
      rw [hmintR] at h
      exact h
    have hAuxEq : auxParams.map (constifyMacroCallParam assignment') =
        auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
          auxBool.map (fun v => MacroCallParam.const (Const.boolc v)) := by
      have h := mintFreshAuxParams_constify_eq assignment' nv1 fspec.numAuxFFVars
        fspec.numAuxBoolVars auxFF auxBool hauxFF_len hauxBool_len hauxFFRange hauxBoolRange
      rw [hmintA] at h
      exact h
    have hformula_const : evalFormula gconf assignment'
        (FFFormula.call fspec.f.name
          (flattenValuesParams vs ++ flattenValuesParams retVals ++
           auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
           auxBool.map (fun v => MacroCallParam.const (Const.boolc v))))
        (specs.map (·.f)) = Except.ok true := by
      rw [hcf, evalFormula_call_constify gconf assignment' fspec.f.name
        (flattenSymValuesParams argSymVals ++ outputParams ++ auxParams) (specs.map (·.f)),
        List.map_append, List.map_append, hInputEq, hOutputEq, hAuxEq] at hformula_given
      simpa [List.append_assoc] using hformula_given
    have hallconst : ∀ mcp ∈ (flattenValuesParams vs ++ flattenValuesParams retVals ++
        auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
        auxBool.map (fun v => MacroCallParam.const (Const.boolc v))),
        ∃ cv, mcp = MacroCallParam.const cv := by
      intro mcp hmcp
      rcases List.mem_append.mp hmcp with h1 | h2
      · rcases List.mem_append.mp h1 with h1a | h1b
        · rcases List.mem_append.mp h1a with h1a1 | h1a2
          · exact flattenValuesParams_all_const vs mcp h1a1
          · exact flattenValuesParams_all_const retVals mcp h1a2
        · obtain ⟨v, _, hveq⟩ := List.mem_map.mp h1b; exact ⟨Const.ffc v, hveq.symm⟩
      · obtain ⟨v, _, hveq⟩ := List.mem_map.mp h2; exact ⟨Const.boolc v, hveq.symm⟩
    have hformula_allassign : ∀ assign, evalFormula gconf assign
        (FFFormula.call fspec.f.name
          (flattenValuesParams vs ++ flattenValuesParams retVals ++
           auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
           auxBool.map (fun v => MacroCallParam.const (Const.boolc v))))
        (specs.map (·.f)) = Except.ok true := by
      intro assign
      rw [evalFormula_call_const_args_indep gconf assign assignment' fspec.f.name _
        (specs.map (·.f)) hallconst]
      exact hformula_const
    have hFC : evalFunCall gconf p fname vs = Except.ok retVals :=
      (H_specCorrect vs hvs_shape).2 retVals auxFF auxBool hretVals_shape hauxFF_len hauxBool_len
        hformula_allassign
    obtain ⟨vars_env, hSV⟩ := setVars_defined_of_length_eq_concrete outs retVals env
      (houts_len.trans hretVals_len.symm)
    refine ⟨vars_env, ?_, ?_⟩
    · simp only [evalFuncCallCmd, hvs_eq, hFC, hSV]
    · have hEnvMatchesMid : EnvMatches assignment' symEnv env :=
        EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagree hmatch
      have hOutValsMatch : List.Forall₂ (symValMatches assignment') outVals retVals := by
        have h := mintFreshRets_outVals_symValMatches assignment' fspec.rets sconf.nextVarId
          retVals hretVals_shape houtRange
        rw [hmintR] at h
        exact h
      exact EnvMatches_setVars outs outVals retVals assignment' symEnv env
        hEnvMatchesMid hOutValsMatch outSymEnv' hOutSymEnv vars_env hSV
  have hspec2 :
      spec = { inSymEnv := symEnv, outSymEnv := outSymEnv', f := cf, nextVarId := nv2 } := by
    injection (hspec_witness.symm.trans hseFuncCall_eq)
  subst hspec2
  exact ⟨rfl, hmono, hfresh, hbelowProof, houtbelow, houtfresh, hsound, hcomplete⟩

end Corellzk2smt.SymExec.PartialCorrectness.FuncCallCorrectness
