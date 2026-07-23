import Corellzk2smt.SymExec.Correctness.Lemmas
import Corellzk2smt.SymExec.Correctness.FuncCallCorrectness
import Corellzk2smt.Language.Core.Analysis.DefinedVars
import Corellzk2smt.Language.Core.Syntax.Lemmas

/-
This file merges what used to be two files: `SymExec/FuncCorrectness.lean` ("shared machinery"
for `seFunc` correctness, array-general -- function params/rets may be `.array`-typed: the
`mintFreshParam`/`mintFreshParams`/`mintFreshRetsWithEq` families,
`EnvMatches_mintFreshParams_bindInParams_general`, `getOutParamsValues_construct_general`,
`fetchFunc_name_eq`/`seFunc_eq_shape`, and their many supporting lemmas, none of it stated in
terms of `TranslatesCorrectly`) and `SymExec/Correctness/FuncCorrectness.lean` (the actual
`seFunc_correct`/`seFuncCall_correct_via_seFunc` theorems built on top of it). They were separate
because the shared machinery was meant to be reusable by both an unconditional and a conditional
(`TranslatesCorrectly`) formalization; the unconditional one was deleted once the conditional one
fully superseded it, leaving the split purely historical -- merged back into one file/namespace
now that there's only one consumer.

Note: the old file's own `seFunc_f_params_split` is renamed `seFunc_f_params_split_basic` here to
avoid clashing with this file's own, genuinely different `seFunc_f_params_split` below (same
underlying `seFunc`-unfold idea, but the new one additionally proves the params/rets-range
disjointness facts needed by `seExecProg_call_complete`, using `seCmds_correct`'s own `hbs_mono` --
a fact the bare `seFunc` definition doesn't encode syntactically). Both are still used by
different callers in `ProgCorrectness.lean`.
-/

namespace Corellzk2smt.SymExec.Correctness.FuncCorrectness

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
open Corellzk2smt.SymExec.Correctness.FuncCallCorrectness

/-- `mintFreshParam` mints exactly `typeSize type` consecutive fresh `.ffv`s, in closed form --
    unconditionally (unlike the old FF-only version, `mintFreshParam` never errors any more). -/
theorem mintFreshParam_eq {c : ZKConfig} (nextVarId : Nat) (type : VarType)
    (nv1 : Nat) (vs : List Var) (sv : SymValue c)
    (h : mintFreshParam (c := c) nextVarId type = Except.ok (nv1, vs, sv)) :
    vs = (List.range (typeSize type)).map (fun i => Var.ffv (nextVarId + i)) ∧
    nv1 = nextVarId + typeSize type := by
  cases type with
  | ff =>
      simp only [mintFreshParam, Except.ok.injEq, Prod.mk.injEq] at h
      simp [typeSize, ← h.1, ← h.2.1]
  | array n =>
      simp only [mintFreshParam, Except.ok.injEq, Prod.mk.injEq] at h
      refine ⟨?_, by simp [typeSize, ← h.1]⟩
      rw [← h.2.1, typeSize, List.map_map]
      rfl

/-- `mintFreshParams` mints exactly `totalParamSize params` consecutive fresh `.ffv`s, in one
    flattened block per param (each param's own block having exactly `paramSize` many, per
    `mintFreshParam_eq`) -- the direct generalization of the old FF-only closed form, which was
    the special case where every param occupies exactly one slot. -/
theorem mintFreshParams_paramVars_eq {c : ZKConfig} :
    ∀ (nextVarId : Nat) (params : List Param) (env : SymEnv c) (nv1 : Nat)
      (paramVars : List Var) (env' : SymEnv c),
      mintFreshParams (c := c) nextVarId params env = Except.ok (nv1, paramVars, env') →
      paramVars = (List.range (totalParamSize params)).map (fun i => Var.ffv (nextVarId + i)) ∧
      nv1 = nextVarId + totalParamSize params := by
  intro nextVarId params
  induction params generalizing nextVarId with
  | nil =>
      intro env nv1 paramVars env' h
      simp only [mintFreshParams, Except.ok.injEq, Prod.mk.injEq] at h
      simp [← h.2.1, ← h.1]
  | cons p ps ih =>
      intro env nv1 paramVars env' h
      simp only [mintFreshParams] at h
      cases hmp : mintFreshParam (c := c) nextVarId p.type with
      | error e => simp [hmp] at h
      | ok result =>
          obtain ⟨nv2, vs, sv⟩ := result
          simp only [hmp] at h
          cases hrest : mintFreshParams (c := c) nv2 ps (setVar env p.name sv) with
          | error e => simp [hrest] at h
          | ok result2 =>
              obtain ⟨nv3, vs2, env2⟩ := result2
              simp only [hrest, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨hvs_eq, hnv2_eq⟩ := mintFreshParam_eq nextVarId p.type nv2 vs sv hmp
              obtain ⟨hvs2_eq, hnv3_eq⟩ := ih nv2 (setVar env p.name sv) nv3 vs2 env2 hrest
              have hps : paramSize p = typeSize p.type := rfl
              have hnv3_final : nv3 = nextVarId + totalParamSize (p :: ps) := by
                rw [hnv3_eq, hnv2_eq, totalParamSize_cons, hps]; omega
              refine ⟨?_, ?_⟩
              · rw [← h.2.1, hvs_eq, hvs2_eq, hnv2_eq, totalParamSize_cons]
                rw [List.range_add, List.map_append, List.map_map]
                congr 1
                apply List.map_congr_left
                intro i _
                simp only [Function.comp, Var.ffv.injEq]
                rw [hps, Nat.add_assoc]
              · rw [← h.1]; exact hnv3_final


/-- Array-general version of `getOutParamsValues_ff_only_shape`: `getOutParamsValues` only ever
    succeeds with a value list matching `rets`'s own declared shapes (`ValuesMatchParams`) --
    direct consequence of every `getOutParamsValues` success internally requiring
    `ensureCorrectType v r.type = Except.ok ()`, which is exactly `ValuesMatchParams`'s own
    per-element relation. -/
theorem getOutParamsValues_shape {c : ZKConfig} :
    ∀ (env : Env c) (rets : List Param) (vs : List (Value c)),
      getOutParamsValues env rets = Except.ok vs → ValuesMatchParams vs rets := by
  intro env rets
  induction rets with
  | nil =>
      intro vs h
      simp only [getOutParamsValues, Except.ok.injEq] at h
      rw [← h]
      exact List.Forall₂.nil
  | cons r rs ih =>
      intro vs h
      simp only [getOutParamsValues] at h
      cases hg : getVar env r.name with
      | error e => rw [hg] at h; simp at h
      | ok v =>
          rw [hg] at h
          simp only [] at h
          cases hect : ensureCorrectType v r.type with
          | error e => rw [hect] at h; simp at h
          | ok u =>
              rw [hect] at h
              simp only [] at h
              cases hrest : getOutParamsValues env rs with
              | error e => rw [hrest] at h; simp at h
              | ok vsRest =>
                  rw [hrest] at h
                  simp only [Except.ok.injEq] at h
                  rw [← h]
                  exact List.Forall₂.cons hect (ih vsRest hrest)

/-- The "identity match" collapses to `e` itself -- needed because several recursive
    `Except`-returning definitions in this codebase (`Semantics.Basic.setVars`,
    `SymExec.Basic.setVars`, ...) wrap their recursive call in exactly this shape, which isn't
    syntactically (only semantically) equal to the bare call, so plain `simp`/`rw` alone can
    get stuck on it after unfolding. Two versions since the branch order in the source
    (`ok` first vs `error` first) affects whether `simp` matches it as a rewrite rule. -/
theorem except_id_match {α β : Type} (e : Except α β) :
    (match e with | Except.ok y => Except.ok y | Except.error x => Except.error x) = e := by
  cases e <;> rfl

theorem except_id_match' {α β : Type} (e : Except α β) :
    (match e with | Except.error x => Except.error x | Except.ok y => Except.ok y) = e := by
  cases e <;> rfl



/-- Two empty `Std.TreeMap`s trivially `EnvMatches` each other, under any assignment. -/
theorem EnvMatches_empty {c : ZKConfig} (assignment : Assignment c) :
    EnvMatches assignment (emptySymEnv (c := c)) (emptyEnv c) := by
  constructor
  · intro id; simp [emptySymEnv, emptyEnv]
  · intro id sv hsv
    simp only [emptySymEnv, Std.TreeMap.empty_eq_emptyc, Std.TreeMap.get?_eq_getElem?,
      Std.TreeMap.getElem?_emptyc] at hsv
    exact absurd hsv (by simp)

/-- A single `.const 0` `setVar` step, applied identically on both sides, preserves
    `EnvMatches` -- `simpleValMatches` for a `.const` value is just `v' = v`, independent of
    the assignment, so this holds regardless of what `assignment` is. -/
theorem EnvMatches_setVar_zero {c : ZKConfig} (assignment : Assignment c) (symEnv : SymEnv c)
    (env : Env c) (id : VarID) (h : EnvMatches assignment symEnv env) :
    EnvMatches assignment
      (Corellzk2smt.SymExec.Basic.setVar symEnv id (SymValue.simple (SimpleSymVal.const 0)))
      (Corellzk2smt.Language.Core.Semantics.Basic.setVar env id (Value.scalar 0)) := by
  constructor
  · intro id'
    simp only [Corellzk2smt.SymExec.Basic.setVar,
      Corellzk2smt.Language.Core.Semantics.Basic.setVar, Std.TreeMap.contains_insert]
    by_cases heq : id' = id
    · simp [heq]
    · simp [h.1 id']
  · intro id' sv' hsv'
    by_cases heq : id' = id
    · subst heq
      simp only [Corellzk2smt.SymExec.Basic.setVar, Std.TreeMap.get?_eq_getElem?,
        Std.TreeMap.getElem?_insert_self] at hsv'
      injection hsv' with hsv'
      refine ⟨Value.scalar 0, ?_, ?_⟩
      · simp only [Corellzk2smt.Language.Core.Semantics.Basic.setVar,
          Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert_self]
      · rw [← hsv']; simp [symValMatches, simpleValMatches]
    · have hne : id ≠ id' := fun hh => heq hh.symm
      simp only [Corellzk2smt.SymExec.Basic.setVar, Std.TreeMap.get?_eq_getElem?,
        Std.TreeMap.getElem?_insert, Std.compare_eq_iff_eq, hne, if_false] at hsv'
      rw [← Std.TreeMap.get?_eq_getElem?] at hsv'
      obtain ⟨v', hv', hm'⟩ := h.2 id' sv' hsv'
      refine ⟨v', ?_, hm'⟩
      simp only [Corellzk2smt.Language.Core.Semantics.Basic.setVar, Std.TreeMap.get?_eq_getElem?,
        Std.TreeMap.getElem?_insert, Std.compare_eq_iff_eq, hne, if_false]
      rw [← Std.TreeMap.get?_eq_getElem?]
      exact hv'

/-- Lifting `EnvMatches_setVar_zero` across a `List.foldl` of identical `.const 0` steps on
    both sides. -/
theorem EnvMatches_zeroFoldl {c : ZKConfig} :
    ∀ (l : List VarID) (assignment : Assignment c) (symEnv : SymEnv c) (env : Env c),
      EnvMatches assignment symEnv env →
      EnvMatches assignment
        (l.foldl (fun e id => Corellzk2smt.SymExec.Basic.setVar e id
          (SymValue.simple (SimpleSymVal.const 0))) symEnv)
        (l.foldl (fun e id => Corellzk2smt.Language.Core.Semantics.Basic.setVar e id
          (Value.scalar 0)) env) := by
  intro l
  induction l with
  | nil => intro assignment symEnv env h; simpa using h
  | cons id rest ih =>
      intro assignment symEnv env h
      simp only [List.foldl_cons]
      exact ih assignment _ _ (EnvMatches_setVar_zero assignment symEnv env id h)

/-- `seFunc`'s `zeroSymEnv` (built from `definedVarsOfFunc`) always `EnvMatches`
    `evalFunCall`'s `zeroInitEnv (definedVarsOfFunc func)`, under any assignment -- both fold
    the same `.const 0`/`Value.scalar 0` step over the same variable set, starting from
    matching empty environments. -/
theorem EnvMatches_zeroSymEnv_zeroInitEnv {c : ZKConfig} (assignment : Assignment c)
    (vars : VarIDSet) :
    EnvMatches assignment
      (vars.foldl (fun env id => Corellzk2smt.SymExec.Basic.setVar env id
        (SymValue.simple (SimpleSymVal.const 0))) emptySymEnv)
      (Corellzk2smt.Language.Core.Semantics.Basic.zeroInitEnv vars) := by
  simp only [Corellzk2smt.Language.Core.Semantics.Basic.zeroInitEnv,
    Std.TreeSet.foldl_eq_foldl_toList]
  exact EnvMatches_zeroFoldl vars.toList assignment emptySymEnv (emptyEnv c)
    (EnvMatches_empty assignment)

/-- No variable is ever tracked by `emptySymEnv`. -/
theorem symEnvVars_emptySymEnv_elim {c : ZKConfig} (v : Var)
    (h : v ∈ symEnvVars (emptySymEnv (c := c))) : False := by
  obtain ⟨id, sv, hget, _⟩ := symEnvVars_mem_elim emptySymEnv v h
  simp only [emptySymEnv, Std.TreeMap.empty_eq_emptyc, Std.TreeMap.get?_eq_getElem?,
    Std.TreeMap.getElem?_emptyc] at hget
  exact absurd hget (by simp)

/-- Folding `.const 0` `setVar` steps over `env` never introduces a variable beyond what `env`
    already had -- `.const` values mention no variables. -/
theorem symEnvVars_zeroFoldl_subset {c : ZKConfig} :
    ∀ (l : List VarID) (env : SymEnv c) (v : Var),
      v ∈ symEnvVars (l.foldl (fun e id => Corellzk2smt.SymExec.Basic.setVar e id
        (SymValue.simple (SimpleSymVal.const 0))) env) →
      v ∈ symEnvVars env := by
  intro l
  induction l with
  | nil => intro env v h; simpa using h
  | cons id rest ih =>
      intro env v h
      simp only [List.foldl_cons] at h
      have h' := ih (Corellzk2smt.SymExec.Basic.setVar env id
        (SymValue.simple (SimpleSymVal.const 0))) v h
      rcases symEnvVars_setVar_subset env id (SymValue.simple (SimpleSymVal.const 0)) v h' with
        h1 | h2
      · exact h1
      · simp only [symValVars, simpleValVars] at h2
        exact absurd h2 Std.TreeSet.not_mem_emptyc

/-- `seFunc`'s `zeroSymEnv` (folding `.const 0` over `definedVarsOfFunc`, starting from
    `emptySymEnv`) never tracks any variable -- so it is vacuously "below" any counter. -/
theorem zeroSymEnv_below {c : ZKConfig} (vars : VarIDSet) (n : Nat) :
    varSetBelow (symEnvVars (vars.foldl (fun env id => Corellzk2smt.SymExec.Basic.setVar env id
      (SymValue.simple (c := c) (SimpleSymVal.const 0))) emptySymEnv)) n := by
  intro v hv
  rw [Std.TreeSet.foldl_eq_foldl_toList] at hv
  exact absurd (symEnvVars_zeroFoldl_subset vars.toList emptySymEnv v hv)
    (symEnvVars_emptySymEnv_elim v)

/-- Folding `setVar` steps over a list only ever adds/updates keys -- an already-contained id
    stays contained. Generic helper, mirrors `foldl_insert_var_mono`
    (`Language/Core/Analysis/DefinedVars.lean`) one level up (`SymEnv`/`setVar` instead of
    `VarIDSet`/`insert`). -/
theorem foldl_setVar_contains_mono {c : ZKConfig} :
    ∀ (l : List VarID) (env : SymEnv c) (id : VarID) (v0 : SymValue c), env.contains id →
      (l.foldl (fun e id' => Corellzk2smt.SymExec.Basic.setVar e id' v0) env).contains id := by
  intro l
  induction l with
  | nil => intro env id v0 h; simpa using h
  | cons id0 rest ih =>
      intro env id v0 h
      simp only [List.foldl_cons]
      exact ih (Corellzk2smt.SymExec.Basic.setVar env id0 v0) id v0
        ((contains_insert_iff env id0 id v0).mpr (Or.inr h))

/-- Folding `.const 0` `setVar` steps over `env`, starting fresh, contains every id the fold
    list itself mentions -- the containment counterpart of `symEnvVars_zeroFoldl_subset`
    (freshness). -/
theorem symEnvVars_zeroFoldl_contains_of_mem {c : ZKConfig} :
    ∀ (l : List VarID) (env : SymEnv c) (id : VarID), id ∈ l →
      (l.foldl (fun e id' => Corellzk2smt.SymExec.Basic.setVar e id'
        (SymValue.simple (c := c) (SimpleSymVal.const 0))) env).contains id := by
  intro l
  induction l with
  | nil => intro env id h; exact absurd h List.not_mem_nil
  | cons id0 rest ih =>
      intro env id h
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp h with heq | hmem
      · rw [heq]
        exact foldl_setVar_contains_mono rest
          (Corellzk2smt.SymExec.Basic.setVar env id0 (SymValue.simple (SimpleSymVal.const 0)))
          id0 (SymValue.simple (SimpleSymVal.const 0))
          ((contains_insert_iff env id0 id0 (SymValue.simple (SimpleSymVal.const 0))).mpr
            (Or.inl rfl))
      · exact ih (Corellzk2smt.SymExec.Basic.setVar env id0
          (SymValue.simple (SimpleSymVal.const 0))) id hmem

/-- `seFunc`'s `zeroSymEnv` (folding `.const 0` over `definedVarsOfFunc`, starting from
    `emptySymEnv`) already contains every variable `definedVarsOfFunc` collects -- the
    containment counterpart of `zeroSymEnv_below` (freshness). Lets `seFunc_correct` discharge
    the body's domain-preservation precondition (`seCmds_domain_of_defined`'s `hpre`) internally,
    instead of needing it threaded in as an external hypothesis (`H_domain`). -/
theorem zeroSymEnv_contains {c : ZKConfig} (vars : VarIDSet) (id : VarID) (hid : id ∈ vars) :
    (vars.foldl (fun env id' => Corellzk2smt.SymExec.Basic.setVar env id'
      (SymValue.simple (c := c) (SimpleSymVal.const 0))) emptySymEnv).contains id := by
  rw [Std.TreeSet.foldl_eq_foldl_toList]
  exact symEnvVars_zeroFoldl_contains_of_mem vars.toList emptySymEnv id
    (Std.TreeSet.mem_toList.mpr hid)

/-- `mintFreshParams` only ever adds/updates keys (via `setVar`) as it mints fresh param
    bindings -- an already-contained id stays contained in the output. -/
theorem mintFreshParams_contains_mono {c : ZKConfig} :
    ∀ (nextVarId : Nat) (params : List Param) (env : SymEnv c) (nv : Nat) (vs : List Var)
      (env' : SymEnv c), mintFreshParams (c := c) nextVarId params env = Except.ok (nv, vs, env') →
      ∀ id, env.contains id → env'.contains id := by
  intro nextVarId params
  induction params generalizing nextVarId with
  | nil =>
      intro env nv vs env' heq id hid
      simp only [mintFreshParams, Except.ok.injEq, Prod.mk.injEq] at heq
      rw [← heq.2.2]; exact hid
  | cons p ps ih =>
      intro env nv vs env' heq id hid
      cases hmp : mintFreshParam (c := c) nextVarId p.type with
      | error e => simp only [mintFreshParams, hmp] at heq; exact absurd heq (by simp)
      | ok result =>
          obtain ⟨nv1, vs1, sv⟩ := result
          simp only [mintFreshParams, hmp] at heq
          cases hrec : mintFreshParams (c := c) nv1 ps
              (Corellzk2smt.SymExec.Basic.setVar env p.name sv) with
          | error e => simp only [hrec] at heq; exact absurd heq (by simp)
          | ok result2 =>
              obtain ⟨nv2, vs2, env''⟩ := result2
              simp only [hrec, Except.ok.injEq, Prod.mk.injEq] at heq
              rw [← heq.2.2]
              exact ih nv1 (Corellzk2smt.SymExec.Basic.setVar env p.name sv) nv2 vs2 env'' hrec id
                ((contains_insert_iff env p.name id sv).mpr (Or.inr hid))


-- ---------------------------------------------------------------------------
-- Array-general replacement for the old FF-only `EnvMatches_mintFreshParams_bindInParams`
-- (Phase 1 of the array-generalization plan; the FF-only version has since been removed).
-- ---------------------------------------------------------------------------

/-- `mintFreshParam`'s minted symbolic value is exactly `freshRetSymValue` at the same starting
    offset/type -- the two mint identical shapes (a single fresh `.ffv`, or an array of `size`
    consecutive fresh `.ffv`s), just via separately-named functions on the params side vs. the
    rets side (`Correctness.lean`). -/
theorem mintFreshParam_symValue_eq_freshRetSymValue {c : ZKConfig} (nextVarId : Nat)
    (type : VarType) (nv1 : Nat) (vs : List Var) (sv : SymValue c)
    (h : mintFreshParam (c := c) nextVarId type = Except.ok (nv1, vs, sv)) :
    sv = freshRetSymValue nextVarId type := by
  cases type with
  | ff =>
      simp only [mintFreshParam, Except.ok.injEq, Prod.mk.injEq] at h
      simp [freshRetSymValue, ← h.2.2]
  | array n =>
      simp only [mintFreshParam, Except.ok.injEq, Prod.mk.injEq] at h
      simp [freshRetSymValue, ← h.2.2]

/-- Array-general version of `EnvMatches_mintFreshParams_bindInParams`: given `argVals` matches
    `params`'s shape (`ValuesMatchParams`, scalar or array per param) and the assignment reads
    back `argVals`'s own flattened `FF` elements over the whole param list's block, binding
    `argVals` into a concrete env via `bindInParams` succeeds and `EnvMatches` the symbolic env
    `mintFreshParams` produces. Mirrors `mintFreshRets_outVals_symValMatches`
    (`FuncCallCorrectness.lean`)'s block-splitting pattern (`flattenValuesToFF_getD_head`/`_tail`),
    but builds up `EnvMatches` directly (one `setVar` step at a time) rather than a
    `List.Forall₂ symValMatches` list, since `mintFreshParams`, unlike `mintFreshRets`, doesn't
    expose its per-param `SymValue`s separately from the `SymEnv` it builds them into. -/
theorem EnvMatches_mintFreshParams_bindInParams_general {c : ZKConfig} :
    ∀ (nextVarId : Nat) (params : List Param) (argVals : List (Value c))
      (assignment : Assignment c) (symEnv : SymEnv c) (env : Env c),
      ValuesMatchParams argVals params →
      EnvMatches assignment symEnv env →
      (∀ i, i < totalParamSize params → assignment.ff (nextVarId + i) =
        (flattenValuesToFF argVals).getD i 0) →
      ∀ (nv1 : Nat) (paramVars : List Var) (symEnv' : SymEnv c),
        mintFreshParams (c := c) nextVarId params symEnv = Except.ok (nv1, paramVars, symEnv') →
        ∃ env', bindInParams env params argVals = Except.ok env' ∧
          EnvMatches assignment symEnv' env' := by
  intro nextVarId params
  induction params generalizing nextVarId with
  | nil =>
      intro argVals assignment symEnv env hmatch hEnvMatch _hassign nv1 paramVars symEnv' h
      cases hmatch
      simp only [mintFreshParams, Except.ok.injEq, Prod.mk.injEq] at h
      exact ⟨env, rfl, h.2.2 ▸ hEnvMatch⟩
  | cons p ps ih =>
      intro argVals assignment symEnv env hmatch hEnvMatch hassign nv1 paramVars symEnv' h
      cases hmatch with
      | cons hd tl =>
          rename_i v0 vs
          have ht : ensureCorrectType v0 p.type = Except.ok () := hd
          simp only [mintFreshParams] at h
          cases hmp : mintFreshParam (c := c) nextVarId p.type with
          | error e => simp [hmp] at h
          | ok result =>
              obtain ⟨nv2, ids0, sv⟩ := result
              simp only [hmp] at h
              have hsv_eq : sv = freshRetSymValue nextVarId p.type :=
                mintFreshParam_symValue_eq_freshRetSymValue nextVarId p.type nv2 ids0 sv hmp
              have hnv2_eq : nv2 = nextVarId + typeSize p.type :=
                (mintFreshParam_eq nextVarId p.type nv2 ids0 sv hmp).2
              have hps : paramSize p = typeSize p.type := rfl
              have hrange0 : ∀ i, i < typeSize p.type →
                  assignment.ff (nextVarId + i) = (flattenValueToFF v0).getD i 0 := by
                intro i hi
                have h1 := hassign i (by rw [totalParamSize_cons, hps]; omega)
                rw [h1, flattenValuesToFF_getD_head v0 vs i (by
                  rw [flattenValueToFF_length v0 p.type ht]; exact hi)]
              have hsvmatch : symValMatches assignment sv v0 := by
                rw [hsv_eq]
                exact freshRetSymValue_symValMatches assignment nextVarId p.type v0 ht hrange0
              have hmatch1 : EnvMatches assignment
                  (Corellzk2smt.SymExec.Basic.setVar symEnv p.name sv)
                  (Corellzk2smt.Language.Core.Semantics.Basic.setVar env p.name v0) := by
                constructor
                · intro id'
                  simp only [Corellzk2smt.SymExec.Basic.setVar,
                    Corellzk2smt.Language.Core.Semantics.Basic.setVar, Std.TreeMap.contains_insert]
                  by_cases heq : id' = p.name
                  · simp [heq]
                  · simp [hEnvMatch.1 id']
                · intro id' sv' hsv'
                  by_cases heq : id' = p.name
                  · subst heq
                    simp only [Corellzk2smt.SymExec.Basic.setVar, Std.TreeMap.get?_eq_getElem?,
                      Std.TreeMap.getElem?_insert_self] at hsv'
                    injection hsv' with hsv'
                    refine ⟨v0, ?_, ?_⟩
                    · simp only [Corellzk2smt.Language.Core.Semantics.Basic.setVar,
                        Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert_self]
                    · rw [← hsv']; exact hsvmatch
                  · have hne : p.name ≠ id' := fun hh => heq hh.symm
                    simp only [Corellzk2smt.SymExec.Basic.setVar, Std.TreeMap.get?_eq_getElem?,
                      Std.TreeMap.getElem?_insert, Std.compare_eq_iff_eq, hne, if_false] at hsv'
                    rw [← Std.TreeMap.get?_eq_getElem?] at hsv'
                    obtain ⟨v', hv', hm'⟩ := hEnvMatch.2 id' sv' hsv'
                    refine ⟨v', ?_, hm'⟩
                    simp only [Corellzk2smt.Language.Core.Semantics.Basic.setVar,
                      Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert,
                      Std.compare_eq_iff_eq, hne, if_false]
                    rw [← Std.TreeMap.get?_eq_getElem?]
                    exact hv'
              have hassign' : ∀ i, i < totalParamSize ps →
                  assignment.ff (nv2 + i) = (flattenValuesToFF vs).getD i 0 := by
                intro i hi
                have heqidx : nv2 + i = nextVarId + (typeSize p.type + i) := by
                  rw [hnv2_eq]; omega
                rw [heqidx]
                have h1 := hassign (typeSize p.type + i) (by rw [totalParamSize_cons, hps]; omega)
                rw [h1, flattenValuesToFF_getD_tail v0 vs (typeSize p.type + i) (by
                  rw [flattenValueToFF_length v0 p.type ht]; omega)]
                congr 1
                rw [flattenValueToFF_length v0 p.type ht]
                omega
              cases hrest : mintFreshParams (c := c) nv2 ps
                  (Corellzk2smt.SymExec.Basic.setVar symEnv p.name sv) with
              | error e => simp [hrest] at h
              | ok result2 =>
                  obtain ⟨nv3, ids2, symEnv2⟩ := result2
                  simp only [hrest, Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨env', hbindEq, hmatch'⟩ := ih nv2 vs assignment
                    (Corellzk2smt.SymExec.Basic.setVar symEnv p.name sv)
                    (Corellzk2smt.Language.Core.Semantics.Basic.setVar env p.name v0)
                    tl hmatch1 hassign' nv3 ids2 symEnv2 hrest
                  refine ⟨env', ?_, ?_⟩
                  · simp only [bindInParams, ht]
                    exact hbindEq
                  · rw [← h.2.2]; exact hmatch'

/-- `mintFreshParams` advances the counter by exactly `totalParamSize params` (not just "grows",
    per `mintFreshParams_mono`) -- thin restatement of `mintFreshParams_paramVars_eq`'s second
    component, kept under its old name since downstream code refers to it. -/
theorem mintFreshParams_nv1_eq {c : ZKConfig} :
    ∀ (nextVarId : Nat) (params : List Param) (symEnv : SymEnv c)
      (nv1 : Nat) (paramVars : List Var) (symEnv' : SymEnv c),
      mintFreshParams (c := c) nextVarId params symEnv = Except.ok (nv1, paramVars, symEnv') →
      nv1 = nextVarId + totalParamSize params :=
  fun nextVarId params symEnv nv1 paramVars symEnv' h =>
    (mintFreshParams_paramVars_eq nextVarId params symEnv nv1 paramVars symEnv' h).2

/-- `mintFreshParams` only ever grows the variable-id counter (mirrors
    `mintFreshRets_mono`/`mintFreshAuxParams_mono` for the call-site analogues). -/
theorem mintFreshParams_mono {c : ZKConfig} :
    ∀ (nextVarId : Nat) (params : List Param) (symEnv : SymEnv c)
      (nv1 : Nat) (paramVars : List Var) (symEnv' : SymEnv c),
      mintFreshParams (c := c) nextVarId params symEnv = Except.ok (nv1, paramVars, symEnv') →
      nextVarId ≤ nv1 :=
  fun nextVarId params symEnv nv1 paramVars symEnv' h => by
    rw [mintFreshParams_nv1_eq nextVarId params symEnv nv1 paramVars symEnv' h]
    omega

/-- Every variable mentioned by the array `SymValue` `mintFreshParam`/`mintFreshRetWithEq` mint
    for an `.array size` type is one of the `size` freshly-minted indices -- so it's below
    `start + size`. Reused for both the params side (`mintFreshParam`) and the rets side
    (`mintFreshRetWithEq`), since both mint exactly this shape of array value. -/
theorem symValVars_freshArray_below {c : ZKConfig} (start size : Nat) :
    varSetBelow (symValVars (SymValue.array (c := c)
        ((List.range size).map
          (fun i => SimpleSymVal.ffvar { var := start + i, bits := none })).toArray))
      (start + size) := by
  simp only [symValVars]
  rw [← Array.foldl_toList, List.toList_toArray]
  apply varSetBelow_foldl_union simpleValVars _ (start + size) emptyVarSet
    (fun v hv => absurd hv Std.TreeSet.not_mem_emptyc)
  intro s hs
  obtain ⟨i, hi, hieq⟩ := List.mem_map.mp hs
  subst hieq
  intro v hv
  simp only [simpleValVars] at hv
  rcases Std.TreeSet.mem_insert.mp hv with heq | hmem
  · rw [← Var_compare_eq_iff_eq.mp heq]
    simp only [varIndex]
    rw [List.mem_range] at hi
    omega
  · exact absurd hmem Std.TreeSet.not_mem_emptyc

/-- Every variable `mintFreshParam` mints for a single param is below the finishing counter it
    itself returns. -/
theorem mintFreshParam_symValVars_below {c : ZKConfig} (nextVarId : Nat) (type : VarType)
    (nv1 : Nat) (vs : List Var) (sv : SymValue c)
    (h : mintFreshParam (c := c) nextVarId type = Except.ok (nv1, vs, sv)) :
    varSetBelow (symValVars sv) nv1 := by
  cases type with
  | ff =>
      simp only [mintFreshParam, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.2.2, ← h.1]
      intro v hv
      simp only [symValVars, simpleValVars] at hv
      rcases Std.TreeSet.mem_insert.mp hv with heq | hmem
      · rw [← Var_compare_eq_iff_eq.mp heq]; simp [varIndex]
      · exact absurd hmem Std.TreeSet.not_mem_emptyc
  | array n =>
      simp only [mintFreshParam, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.2.2, ← h.1, List.map_map]
      exact symValVars_freshArray_below (c := c) nextVarId n

/-- Every variable `mintFreshParams` introduces on top of its starting `symEnv` stays below the
    counter it finishes at -- so if the starting `symEnv`'s vars are already below the starting
    counter, the resulting `symEnv'`'s vars are below the finishing counter `nv1` too. -/
theorem mintFreshParams_symEnvVars_below {c : ZKConfig} :
    ∀ (nextVarId : Nat) (params : List Param) (symEnv : SymEnv c),
      varSetBelow (symEnvVars symEnv) nextVarId →
      ∀ (nv1 : Nat) (paramVars : List Var) (symEnv' : SymEnv c),
        mintFreshParams (c := c) nextVarId params symEnv = Except.ok (nv1, paramVars, symEnv') →
        varSetBelow (symEnvVars symEnv') nv1 := by
  intro nextVarId params
  induction params generalizing nextVarId with
  | nil =>
      intro symEnv hbelow nv1 paramVars symEnv' h
      simp only [mintFreshParams, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.1, ← h.2.2]
      exact hbelow
  | cons p ps ih =>
      intro symEnv hbelow nv1 paramVars symEnv' h
      simp only [mintFreshParams] at h
      cases hmp : mintFreshParam (c := c) nextVarId p.type with
      | error e => simp [hmp] at h
      | ok result =>
          obtain ⟨nv2, vs, sv⟩ := result
          simp only [hmp] at h
          cases hrest : mintFreshParams (c := c) nv2 ps (setVar symEnv p.name sv) with
          | error e => simp [hrest] at h
          | ok result2 =>
              obtain ⟨nv3, vs2, env2⟩ := result2
              simp only [hrest, Except.ok.injEq, Prod.mk.injEq] at h
              have hsvbelow := mintFreshParam_symValVars_below nextVarId p.type nv2 vs sv hmp
              have hnv2_ge : nextVarId ≤ nv2 := by
                have := mintFreshParam_eq nextVarId p.type nv2 vs sv hmp
                omega
              have hbelow1 : varSetBelow (symEnvVars (Corellzk2smt.SymExec.Basic.setVar symEnv
                  p.name sv)) nv2 := by
                intro v hv
                rcases symEnvVars_setVar_subset symEnv p.name sv v hv with h1 | h2
                · exact lt_of_lt_of_le (hbelow v h1) hnv2_ge
                · exact hsvbelow v h2
              have hind := ih nv2 (setVar symEnv p.name sv) hbelow1 nv3 vs2 env2 hrest
              rw [← h.1, ← h.2.2]
              exact hind

/-- What `newAssignment'`'s `ffMap` accumulator becomes, in closed form, after processing a
    prefix segment `vs` (all `.ffv`) zipped positionally against `vals` -- a direct recursive
    mirror of `newAssignment'`'s own left-to-right accumulating recursion, so later entries of
    `vs` correctly override earlier ones ("last write wins"). Total (falls back to `base`
    immediately on a `.boolv` head or length mismatch), but only ever applied where every
    element of `vs` is `.ffv` and lengths match. -/
def ffMapAfter {c : ZKConfig} (vs : List Var) (vals : List (FF c)) (base : FFVar → FF c) :
    FFVar → FF c :=
  match vs, vals with
  | Var.ffv n :: vs', v :: vals' => ffMapAfter vs' vals' (fun id => if id == n then v else base id)
  | _, _ => base

/-- Bool-valued mirror of `ffMapAfter`, for a `.boolv`-only segment. No `ZKConfig` parameter --
    unlike `ffMapAfter` (values are `FF c`), nothing here mentions `c`. -/
def boolMapAfter (vs : List Var) (vals : List Bool) (base : BoolVar → Bool) :
    BoolVar → Bool :=
  match vs, vals with
  | Var.boolv n :: vs', v :: vals' => boolMapAfter vs' vals' (fun id => if id == n then v else base id)
  | _, _ => base

/-- The recursive equation characterizing `newAssignment'` after processing an all-`.ffv`
    prefix segment `vs` (paired positionally with the all-`.const`-wrapped `vals`) -- the rest
    of the computation (`restParams`/`restArgs`) proceeds exactly as if it had started from
    `ffMapAfter vs vals ffBase` instead of `ffBase`. -/
theorem newAssignment'_ff_prepend {c : ZKConfig} (assign : Assignment c) :
    ∀ (vs : List Var) (vals : List (FF c)) (restParams : List Var)
      (restArgs : List (MacroCallParam c)) (ffBase : FFVar → FF c) (boolBase : BoolVar → Bool),
      vs.length = vals.length →
      (∀ v ∈ vs, ∃ n, v = Var.ffv n) →
      newAssignment' assign (vals.map (fun v => MacroCallParam.const (Const.ffc v)) ++ restArgs)
          (vs ++ restParams) ffBase boolBase =
        newAssignment' assign restArgs restParams (ffMapAfter vs vals ffBase) boolBase := by
  intro vs
  induction vs with
  | nil =>
      intro vals restParams restArgs ffBase boolBase hlen _hff
      cases vals with
      | nil => simp [ffMapAfter]
      | cons _ _ => simp at hlen
  | cons v vs ih =>
      intro vals restParams restArgs ffBase boolBase hlen hff
      cases vals with
      | nil => simp at hlen
      | cons val vals =>
          obtain ⟨n, hn⟩ := hff v (List.mem_cons_self ..)
          subst hn
          simp only [List.map_cons, List.cons_append, newAssignment']
          rw [ih vals restParams restArgs (fun id => if id == n then val else ffBase id) boolBase
            (by simpa using hlen) (fun v' hv' => hff v' (List.mem_cons_of_mem _ hv'))]
          simp only [ffMapAfter]

/-- Bool-valued mirror of `newAssignment'_ff_prepend`, for a `.boolv`-only trailing segment. -/
theorem newAssignment'_bool_prepend {c : ZKConfig} (assign : Assignment c) :
    ∀ (vs : List Var) (vals : List Bool) (restParams : List Var)
      (restArgs : List (MacroCallParam c)) (ffBase : FFVar → FF c) (boolBase : BoolVar → Bool),
      vs.length = vals.length →
      (∀ v ∈ vs, ∃ n, v = Var.boolv n) →
      newAssignment' assign (vals.map (fun v => MacroCallParam.const (Const.boolc v)) ++ restArgs)
          (vs ++ restParams) ffBase boolBase =
        newAssignment' assign restArgs restParams ffBase (boolMapAfter vs vals boolBase) := by
  intro vs
  induction vs with
  | nil =>
      intro vals restParams restArgs ffBase boolBase hlen _hbool
      cases vals with
      | nil => simp [boolMapAfter]
      | cons _ _ => simp at hlen
  | cons v vs ih =>
      intro vals restParams restArgs ffBase boolBase hlen hbool
      cases vals with
      | nil => simp at hlen
      | cons val vals =>
          obtain ⟨n, hn⟩ := hbool v (List.mem_cons_self ..)
          subst hn
          simp only [List.map_cons, List.cons_append, newAssignment']
          rw [ih vals restParams restArgs ffBase (fun id => if id == n then val else boolBase id)
            (by simpa using hlen) (fun v' hv' => hbool v' (List.mem_cons_of_mem _ hv'))]
          simp only [boolMapAfter]

/-- `ffMapAfter` leaves `base` unchanged at any index `vs` never mentions (as `.ffv`). -/
theorem ffMapAfter_frame {c : ZKConfig} :
    ∀ (vs : List Var) (vals : List (FF c)) (base : FFVar → FF c) (n : FFVar),
      Var.ffv n ∉ vs → ffMapAfter vs vals base n = base n := by
  intro vs
  induction vs with
  | nil => intro vals base n _; simp [ffMapAfter]
  | cons v vs ih =>
      intro vals base n hn
      cases vals with
      | nil => simp [ffMapAfter]
      | cons val vals =>
          cases v with
          | boolv m => simp [ffMapAfter]
          | ffv m =>
              have hmn : m ≠ n := fun h => hn (h ▸ List.mem_cons_self ..)
              have hn' : Var.ffv n ∉ vs := fun h => hn (List.mem_cons_of_mem _ h)
              simp only [ffMapAfter]
              rw [ih vals (fun id => if id == m then val else base id) n hn']
              simp [Ne.symm hmn]

/-- Bool-valued mirror of `ffMapAfter_frame`. -/
theorem boolMapAfter_frame :
    ∀ (vs : List Var) (vals : List Bool) (base : BoolVar → Bool) (n : BoolVar),
      Var.boolv n ∉ vs → boolMapAfter vs vals base n = base n := by
  intro vs
  induction vs with
  | nil => intro vals base n _; simp [boolMapAfter]
  | cons v vs ih =>
      intro vals base n hn
      cases vals with
      | nil => simp [boolMapAfter]
      | cons val vals =>
          cases v with
          | ffv m => simp [boolMapAfter]
          | boolv m =>
              have hmn : m ≠ n := fun h => hn (h ▸ List.mem_cons_self ..)
              have hn' : Var.boolv n ∉ vs := fun h => hn (List.mem_cons_of_mem _ h)
              simp only [boolMapAfter]
              rw [ih vals (fun id => if id == m then val else base id) n hn']
              simp [Ne.symm hmn]

/-- Reading `ffMapAfter vs vals base` back at the `j`-th index of `vs` (given every element of
    `vs` is `.ffv` and `vs` has no repeated index) recovers exactly `vals`'s `j`-th entry. -/
theorem ffMapAfter_getD {c : ZKConfig} :
    ∀ (vs : List Var) (vals : List (FF c)) (base : FFVar → FF c),
      vs.length = vals.length → (∀ v ∈ vs, ∃ n, v = Var.ffv n) → vs.Nodup →
      ∀ j, (hj : j < vs.length) → ∀ n, vs.getD j (Var.ffv 0) = Var.ffv n →
        ffMapAfter vs vals base n = vals.getD j 0 := by
  intro vs
  induction vs with
  | nil => intro vals base _hlen _hff _hnodup j hj; simp at hj
  | cons v vs ih =>
      intro vals base hlen hff hnodup j hj n hveq
      cases vals with
      | nil => simp at hlen
      | cons val vals =>
          obtain ⟨m, hm⟩ := hff v (List.mem_cons_self ..)
          subst hm
          obtain ⟨hv_notmem, hvs_nodup⟩ := List.nodup_cons.mp hnodup
          cases j with
          | zero =>
              simp only [List.getD_cons_zero] at hveq
              injection hveq with hveq
              subst hveq
              simp only [ffMapAfter, List.getD_cons_zero]
              rw [ffMapAfter_frame vs vals (fun id => if id == m then val else base id) m hv_notmem]
              simp
          | succ j' =>
              simp only [List.getD_cons_succ] at hveq
              simp only [ffMapAfter]
              exact ih vals (fun id => if id == m then val else base id) (by simpa using hlen)
                (fun v' hv' => hff v' (List.mem_cons_of_mem _ hv')) hvs_nodup j' (by simpa using hj)
                n hveq

/-- Bool-valued mirror of `ffMapAfter_getD`. -/
theorem boolMapAfter_getD :
    ∀ (vs : List Var) (vals : List Bool) (base : BoolVar → Bool),
      vs.length = vals.length → (∀ v ∈ vs, ∃ n, v = Var.boolv n) → vs.Nodup →
      ∀ j, (hj : j < vs.length) → ∀ n, vs.getD j (Var.boolv 0) = Var.boolv n →
        boolMapAfter vs vals base n = vals.getD j false := by
  intro vs
  induction vs with
  | nil => intro vals base _hlen _hbool _hnodup j hj; simp at hj
  | cons v vs ih =>
      intro vals base hlen hbool hnodup j hj n hveq
      cases vals with
      | nil => simp at hlen
      | cons val vals =>
          obtain ⟨m, hm⟩ := hbool v (List.mem_cons_self ..)
          subst hm
          obtain ⟨hv_notmem, hvs_nodup⟩ := List.nodup_cons.mp hnodup
          cases j with
          | zero =>
              simp only [List.getD_cons_zero] at hveq
              injection hveq with hveq
              subst hveq
              simp only [boolMapAfter, List.getD_cons_zero]
              rw [boolMapAfter_frame vs vals (fun id => if id == m then val else base id) m
                hv_notmem]
              simp
          | succ j' =>
              simp only [List.getD_cons_succ] at hveq
              simp only [boolMapAfter]
              exact ih vals (fun id => if id == m then val else base id) (by simpa using hlen)
                (fun v' hv' => hbool v' (List.mem_cons_of_mem _ hv')) hvs_nodup j'
                (by simpa using hj) n hveq

/-- Mapping an injective function over a `Nodup` list preserves `Nodup` -- written by hand
    (direct induction) rather than relying on a guessed library combinator name. -/
theorem nodup_map_injective {α β : Type} (f : α → β) (hf : ∀ a b, f a = f b → a = b) :
    ∀ (l : List α), l.Nodup → (l.map f).Nodup := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
      intro hnodup
      obtain ⟨ha, hl⟩ := List.nodup_cons.mp hnodup
      simp only [List.map_cons]
      rw [List.nodup_cons]
      refine ⟨?_, ih hl⟩
      intro hmem
      obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hmem
      exact ha (hf a b hfb.symm ▸ hb)

/-- Plain-`Nat` helper for `a + 1 + i = a + Nat.succ i` -- `omega` silently fails when `i`'s
    local type is a reducible abbrev like `FFVar`/`BoolVar` rather than bare `Nat` (it doesn't
    unfold such abbrevs for atom detection), so this is proved once here (genuinely over `Nat`)
    and invoked at the `FFVar`-typed call site via defeq instead. -/
theorem nat_succ_add_comm_helper (a i : Nat) : a + 1 + i = a + Nat.succ i := by omega

/-- A `List.range`-based list of consecutive fresh `.ffv`s never repeats an index. -/
theorem range_map_ffv_nodup (n base : Nat) :
    ((List.range n).map (fun i => Var.ffv (base + i))).Nodup := by
  apply nodup_map_injective (fun i => Var.ffv (base + i))
  · intro a b hab
    injection hab with hab
    exact Nat.add_left_cancel hab
  · exact List.nodup_range

/-- Bundled corollaries of `mintFreshParams_paramVars_eq`: `paramVars` is all-`.ff`, `Nodup`,
    and its `j`-th entry is `Var.ffv (nextVarId + j)` -- generalized to arrays, `j` now ranges
    over `totalParamSize params` (the flattened count) rather than `params.length`. -/
theorem mintFreshParams_paramVars_shape {c : ZKConfig}
    (nextVarId : Nat) (params : List Param) (symEnv : SymEnv c)
    (nv1 : Nat) (paramVars : List Var) (symEnv' : SymEnv c)
    (h : mintFreshParams (c := c) nextVarId params symEnv = Except.ok (nv1, paramVars, symEnv')) :
    (∀ v ∈ paramVars, ∃ n, v = Var.ffv n) ∧ paramVars.Nodup ∧
    (∀ j, j < totalParamSize params → paramVars.getD j (Var.ffv 0) = Var.ffv (nextVarId + j)) := by
  obtain ⟨heq, _⟩ := mintFreshParams_paramVars_eq nextVarId params symEnv nv1 paramVars symEnv' h
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    rw [heq] at hv
    obtain ⟨i, _, hi⟩ := List.mem_map.mp hv
    exact ⟨nextVarId + i, hi.symm⟩
  · rw [heq]; exact range_map_ffv_nodup (totalParamSize params) nextVarId
  · intro j hj
    rw [heq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
    rfl


/-- `mintFreshRetWithEq` mints exactly `paramSize ret` consecutive fresh `.ffv`s, in closed
    form -- the return-side mirror of `mintFreshParam_eq`. -/
theorem mintFreshRetWithEq_eq {c : ZKConfig} (nextVarId : Nat) (bodySymEnv : SymEnv c)
    (ret : Param) (nv1 : Nat) (vs : List Var) (sv : SymValue c) (eqf : FFFormula c)
    (h : mintFreshRetWithEq (c := c) nextVarId bodySymEnv ret = Except.ok (nv1, vs, sv, eqf)) :
    vs = (List.range (paramSize ret)).map (fun i => Var.ffv (nextVarId + i)) ∧
    nv1 = nextVarId + paramSize ret := by
  simp only [paramSize]
  cases ret with
  | mk name type =>
    cases type with
    | ff =>
        simp only [mintFreshRetWithEq] at h
        cases hg : getVar bodySymEnv name with
        | error e => simp [hg] at h
        | ok res =>
            rw [hg] at h
            cases res with
            | array a => simp at h
            | simple sv0 =>
                simp only [Except.ok.injEq, Prod.mk.injEq] at h
                simp [typeSize, ← h.1, ← h.2.1]
    | array n =>
        simp only [mintFreshRetWithEq] at h
        cases hg : getVar bodySymEnv name with
        | error e => simp [hg] at h
        | ok res =>
            rw [hg] at h
            cases res with
            | simple sv0 => simp at h
            | array arr =>
                cases hsize : arr.size == n with
                | false => simp [hsize] at h
                | true =>
                    simp only [hsize, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
                    refine ⟨?_, by simp [typeSize, ← h.1]⟩
                    rw [← h.2.1, typeSize, List.map_map]
                    rfl

/-- `mintFreshRetWithEq`'s equality formula is built purely from `.eq`/`.and`/`.true` over
    `FFTerm.var`/`simpleSymValToTerm` -- it never contains a `.call`, so it's `FormulaNamesBelow`
    any name at all, unconditionally. -/
theorem mintFreshRetWithEq_names_below {c : ZKConfig} (nextVarId : Nat) (bodySymEnv : SymEnv c)
    (ret : Param) (nv1 : Nat) (vs : List Var) (sv : SymValue c) (eqf : FFFormula c)
    (h : mintFreshRetWithEq (c := c) nextVarId bodySymEnv ret = Except.ok (nv1, vs, sv, eqf))
    (badName : String) :
    FormulaNamesBelow eqf badName := by
  cases ret with
  | mk name type =>
    cases type with
    | ff =>
        simp only [mintFreshRetWithEq] at h
        cases hg : getVar bodySymEnv name with
        | error e => simp [hg] at h
        | ok res =>
            rw [hg] at h
            cases res with
            | array a => simp at h
            | simple sv0 =>
                simp only [Except.ok.injEq, Prod.mk.injEq] at h
                rw [← h.2.2.2]
                exact ⟨trivial, simpleSymValToTerm_names_below sv0 badName⟩
    | array n =>
        simp only [mintFreshRetWithEq] at h
        cases hg : getVar bodySymEnv name with
        | error e => simp [hg] at h
        | ok res =>
            rw [hg] at h
            cases res with
            | simple sv0 => simp at h
            | array arr =>
                cases hsize : arr.size == n with
                | false => simp [hsize] at h
                | true =>
                    simp only [hsize, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
                    rw [← h.2.2.2]
                    generalize
                      (arr.toList.zip ((List.range n).map (fun i => nextVarId + i))) = pairs
                    induction pairs with
                    | nil => simp only [List.map_nil, List.foldr_nil]; trivial
                    | cons pr prs ih =>
                        simp only [List.map_cons, List.foldr_cons, FormulaNamesBelow]
                        exact ⟨⟨trivial, simpleSymValToTerm_names_below pr.1 badName⟩, ih⟩

/-- `mintFreshRetsWithEq`'s combined equality formula, list version of
    `mintFreshRetWithEq_names_below` -- `retEqFormula` is a plain `.and`-chain of per-ret equality
    formulas, none of which ever contain a `.call`. -/
theorem mintFreshRetsWithEq_names_below {c : ZKConfig} :
    ∀ (nextVarId : Nat) (bodySymEnv : SymEnv c) (rets : List Param)
      (nv2 : Nat) (retVars : List Var) (retBinds : List (VarID × SymValue c))
      (retEqFormula : FFFormula c),
      mintFreshRetsWithEq (c := c) nextVarId bodySymEnv rets =
        Except.ok (nv2, retVars, retBinds, retEqFormula) →
      ∀ badName : String, FormulaNamesBelow retEqFormula badName := by
  intro nextVarId bodySymEnv rets
  induction rets generalizing nextVarId with
  | nil =>
      intro nv2 retVars retBinds retEqFormula h badName
      simp only [mintFreshRetsWithEq, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.2.2.2]; trivial
  | cons r rs ih =>
      intro nv2 retVars retBinds retEqFormula h badName
      simp only [mintFreshRetsWithEq] at h
      cases hmr : mintFreshRetWithEq (c := c) nextVarId bodySymEnv r with
      | error e => simp [hmr] at h
      | ok result =>
          obtain ⟨nv1, vs, sv, eqf⟩ := result
          simp only [hmr] at h
          cases hrest : mintFreshRetsWithEq (c := c) nv1 bodySymEnv rs with
          | error e => simp [hrest] at h
          | ok result2 =>
              obtain ⟨nv3, vs2, binds2, restf2⟩ := result2
              simp only [hrest, Except.ok.injEq, Prod.mk.injEq] at h
              rw [← h.2.2.2]
              exact ⟨mintFreshRetWithEq_names_below nextVarId bodySymEnv r nv1 vs sv eqf hmr
                  badName,
                ih nv1 nv3 vs2 binds2 restf2 hrest badName⟩

/-- `mintFreshRetsWithEq` mints exactly `totalParamSize rets` consecutive fresh `.ffv`s, in one
    flattened block per ret -- the return-side mirror of `mintFreshParams_paramVars_eq`. -/
theorem mintFreshRetsWithEq_retVars_eq {c : ZKConfig} :
    ∀ (nextVarId : Nat) (bodySymEnv : SymEnv c) (rets : List Param)
      (nv2 : Nat) (retVars : List Var) (retBinds : List (VarID × SymValue c))
      (retEqFormula : FFFormula c),
      mintFreshRetsWithEq (c := c) nextVarId bodySymEnv rets =
        Except.ok (nv2, retVars, retBinds, retEqFormula) →
      retVars = (List.range (totalParamSize rets)).map (fun i => Var.ffv (nextVarId + i)) ∧
      nv2 = nextVarId + totalParamSize rets := by
  intro nextVarId bodySymEnv rets
  induction rets generalizing nextVarId with
  | nil =>
      intro nv2 retVars retBinds retEqFormula h
      simp only [mintFreshRetsWithEq, Except.ok.injEq, Prod.mk.injEq] at h
      simp [← h.2.1, ← h.1]
  | cons r rs ih =>
      intro nv2 retVars retBinds retEqFormula h
      simp only [mintFreshRetsWithEq] at h
      cases hmr : mintFreshRetWithEq (c := c) nextVarId bodySymEnv r with
      | error e => simp [hmr] at h
      | ok result =>
          obtain ⟨nv1, vs, sv, eqf⟩ := result
          simp only [hmr] at h
          cases hrest : mintFreshRetsWithEq (c := c) nv1 bodySymEnv rs with
          | error e => simp [hrest] at h
          | ok result2 =>
              obtain ⟨nv3, vs2, binds2, restf2⟩ := result2
              simp only [hrest, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨hvs_eq, hnv1_eq⟩ := mintFreshRetWithEq_eq nextVarId bodySymEnv r nv1 vs sv
                eqf hmr
              obtain ⟨hvs2_eq, hnv3_eq⟩ := ih nv1 nv3 vs2 binds2 restf2 hrest
              have hps : paramSize r = typeSize r.type := rfl
              have hnv3_final : nv3 = nextVarId + totalParamSize (r :: rs) := by
                rw [hnv3_eq, hnv1_eq, totalParamSize_cons, hps]; omega
              refine ⟨?_, ?_⟩
              · rw [← h.2.1, hvs_eq, hvs2_eq, hnv1_eq, totalParamSize_cons]
                rw [List.range_add, List.map_append, List.map_map]
                congr 1
                apply List.map_congr_left
                intro i _
                simp only [Function.comp, Var.ffv.injEq]
                rw [hps, Nat.add_assoc]
              · rw [← h.1]; exact hnv3_final

/-- Bundled corollaries of `mintFreshRetsWithEq_retVars_eq`, mirroring
    `mintFreshParams_paramVars_shape`. -/
theorem mintFreshRetsWithEq_retVars_shape {c : ZKConfig}
    (nextVarId : Nat) (bodySymEnv : SymEnv c) (rets : List Param)
    (nv2 : Nat) (retVars : List Var) (retBinds : List (VarID × SymValue c))
    (retEqFormula : FFFormula c)
    (h : mintFreshRetsWithEq (c := c) nextVarId bodySymEnv rets =
      Except.ok (nv2, retVars, retBinds, retEqFormula)) :
    (∀ v ∈ retVars, ∃ n, v = Var.ffv n) ∧ retVars.Nodup ∧
    (∀ j, j < totalParamSize rets → retVars.getD j (Var.ffv 0) = Var.ffv (nextVarId + j)) := by
  obtain ⟨heq, _⟩ := mintFreshRetsWithEq_retVars_eq nextVarId bodySymEnv rets nv2 retVars retBinds
    retEqFormula h
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    rw [heq] at hv
    obtain ⟨i, _, hi⟩ := List.mem_map.mp hv
    exact ⟨nextVarId + i, hi.symm⟩
  · rw [heq]; exact range_map_ffv_nodup (totalParamSize rets) nextVarId
  · intro j hj
    rw [heq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
    rfl


/-- What `newAssignment'`'s `ff`/`bool` accumulators become, in closed form, after processing a
    prefix segment `vs` (mixed `.ffv`/`.boolv`, each matched against a correctly-typed `.const`
    argument) -- a direct recursive mirror of `newAssignment'`'s own recursion, generalizing
    `ffMapAfter`/`boolMapAfter` to a single interleaved pass (needed since `auxVarsList` mixes
    `.ffv` and `.boolv` entries, sorted ff-before-bool but not literally two separate lists in
    the macro's own `params` field). -/
def mapsAfter {c : ZKConfig} : List Var → List (MacroCallParam c) → (FFVar → FF c) →
    (BoolVar → Bool) → (FFVar → FF c) × (BoolVar → Bool)
  | Var.ffv n :: vs, MacroCallParam.const (Const.ffc t) :: args, ffBase, boolBase =>
      mapsAfter vs args (fun id => if id == n then t else ffBase id) boolBase
  | Var.boolv n :: vs, MacroCallParam.const (Const.boolc t) :: args, ffBase, boolBase =>
      mapsAfter vs args ffBase (fun id => if id == n then t else boolBase id)
  | _, _, ffBase, boolBase => (ffBase, boolBase)

/-- Every entry of `vs` is `.ffv` paired with `.const .ffc`, or `.boolv` paired with
    `.const .boolc` -- the well-typedness `mapsAfter`/`newAssignment'_prepend` need. -/
def varsArgsWellTyped {c : ZKConfig} (v : Var) (mcp : MacroCallParam c) : Prop :=
  match v, mcp with
  | Var.ffv _, MacroCallParam.const (Const.ffc _) => True
  | Var.boolv _, MacroCallParam.const (Const.boolc _) => True
  | _, _ => False

/-- The recursive equation characterizing `newAssignment'` after processing a well-typed mixed
    prefix segment `vs`/`args`. -/
theorem newAssignment'_prepend {c : ZKConfig} (assign : Assignment c) :
    ∀ (vs : List Var) (args : List (MacroCallParam c)) (restParams : List Var)
      (restArgs : List (MacroCallParam c)) (ffBase : FFVar → FF c) (boolBase : BoolVar → Bool),
      List.Forall₂ varsArgsWellTyped vs args →
      newAssignment' assign (args ++ restArgs) (vs ++ restParams) ffBase boolBase =
        newAssignment' assign restArgs restParams
          (mapsAfter vs args ffBase boolBase).1 (mapsAfter vs args ffBase boolBase).2 := by
  intro vs
  induction vs with
  | nil =>
      intro args restParams restArgs ffBase boolBase hforall
      cases args with
      | nil => simp [mapsAfter]
      | cons _ _ => cases hforall
  | cons v vs ih =>
      intro args restParams restArgs ffBase boolBase hforall
      cases args with
      | nil => cases hforall
      | cons a args =>
          obtain ⟨hd, tl⟩ := List.forall₂_cons.mp hforall
          cases v with
          | ffv n =>
              cases a with
              | var _ => cases hd
              | const cv =>
                cases cv with
                | boolc _ => cases hd
                | ffc t =>
                    simp only [List.cons_append, newAssignment']
                    rw [ih args restParams restArgs (fun id => if id == n then t else ffBase id)
                      boolBase tl]
                    simp only [mapsAfter]
          | boolv n =>
              cases a with
              | var _ => cases hd
              | const cv =>
                cases cv with
                | ffc _ => cases hd
                | boolc t =>
                    simp only [List.cons_append, newAssignment']
                    rw [ih args restParams restArgs ffBase
                      (fun id => if id == n then t else boolBase id) tl]
                    simp only [mapsAfter]

/-- Whether a `Var` is `.ffv`-tagged -- matches the anonymous predicate `seFunc` itself uses to
    compute `numAuxFFVars`, named here so lemmas about it can be stated once. -/
def isFFvVar (v : Var) : Bool := match v with | Var.ffv _ => true | Var.boolv _ => false

/-- In a list sorted by `Var`'s `Ord` (which puts every `.ffv` below every `.boolv`), the
    "take while `.ffv`" prefix is exactly the `.ffv` entries -- no `.boolv` can precede a later
    `.ffv`, since that would violate sortedness (`compare (.boolv _) (.ffv _) = .gt`, never
    `.lt`). -/
theorem sorted_takeWhile_isFFv_eq_filter :
    ∀ (l : List Var), l.Pairwise (fun a b => compare a b = .lt) →
      l.takeWhile isFFvVar = l.filter isFFvVar := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons v l ih =>
      intro hsorted
      obtain ⟨hrel, htail⟩ := List.pairwise_cons.mp hsorted
      cases v with
      | ffv n =>
          have hp : isFFvVar (Var.ffv n) = true := rfl
          rw [List.takeWhile_cons_of_pos hp, List.filter_cons_of_pos hp]
          congr 1
          exact ih htail
      | boolv n =>
          have hp : ¬ isFFvVar (Var.boolv n) = true := by simp [isFFvVar]
          have hnone : l.filter isFFvVar = [] := by
            rw [List.filter_eq_nil_iff]
            intro v hv
            cases v with
            | ffv m =>
                have hcmp := hrel (Var.ffv m) hv
                have hcontra : compare (Var.boolv n) (Var.ffv m) = Ordering.gt := rfl
                rw [hcontra] at hcmp
                simp at hcmp
            | boolv m => simp [isFFvVar]
          rw [List.takeWhile_cons_of_neg hp, List.filter_cons_of_neg hp, hnone]

/-- The complementary fact for `dropWhile`: everything left over after the `.ffv` prefix is
    `.boolv`-only. Proved directly, mirroring `sorted_takeWhile_isFFv_eq_filter`'s own induction
    (rather than via a "split/cancel" argument -- `l.filter p ++ l.filter (not p) = l` is false
    in general for unsorted `l`, so it isn't a usable intermediate fact here). -/
theorem sorted_dropWhile_isFFv_eq_filter_not :
    ∀ (l : List Var), l.Pairwise (fun a b => compare a b = .lt) →
      l.dropWhile isFFvVar = l.filter (fun v => !isFFvVar v) := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons v l ih =>
      intro hsorted
      obtain ⟨hrel, htail⟩ := List.pairwise_cons.mp hsorted
      cases v with
      | ffv n =>
          have hp : isFFvVar (Var.ffv n) = true := rfl
          rw [List.dropWhile_cons_of_pos hp, List.filter_cons_of_neg (by simp [isFFvVar])]
          exact ih htail
      | boolv n =>
          have hp : ¬ isFFvVar (Var.boolv n) = true := by simp [isFFvVar]
          rw [List.dropWhile_cons_of_neg hp]
          have hall : l.filter (fun v => !isFFvVar v) = l := by
            rw [List.filter_eq_self]
            intro v hv
            cases v with
            | ffv m =>
                have hcmp := hrel (Var.ffv m) hv
                have hcontra : compare (Var.boolv n) (Var.ffv m) = Ordering.gt := rfl
                rw [hcontra] at hcmp
                simp at hcmp
            | boolv m => simp [isFFvVar]
          rw [List.filter_cons_of_pos (by simp [isFFvVar]), hall]

/-- Bundled corollary: `auxVarsList`'s `numAuxFFVars`-prefix is all-`.ffv`, and everything from
    that point on is all-`.boolv`. -/
theorem auxVarsList_ff_bool_split (l : List Var)
    (hsorted : l.Pairwise (fun a b => compare a b = .lt)) :
    l.take (l.filter isFFvVar).length = l.filter isFFvVar ∧
    l.drop (l.filter isFFvVar).length = l.filter (fun v => !isFFvVar v) ∧
    (∀ v ∈ l.filter isFFvVar, ∃ n, v = Var.ffv n) ∧
    (∀ v ∈ l.filter (fun v => !isFFvVar v), ∃ n, v = Var.boolv n) := by
  have htw := sorted_takeWhile_isFFv_eq_filter l hsorted
  have hdw := sorted_dropWhile_isFFv_eq_filter_not l hsorted
  have hfull : l.takeWhile isFFvVar ++ l.dropWhile isFFvVar = l := List.takeWhile_append_dropWhile
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hthis := List.take_left' (l₁ := l.takeWhile isFFvVar) (l₂ := l.dropWhile isFFvVar)
      (congrArg List.length htw)
    rw [hfull] at hthis
    exact hthis.trans htw
  · have hthis := List.drop_left' (l₁ := l.takeWhile isFFvVar) (l₂ := l.dropWhile isFFvVar)
      (congrArg List.length htw)
    rw [hfull] at hthis
    exact hthis.trans hdw
  · intro v hv
    have := List.of_mem_filter hv
    cases v with
    | ffv n => exact ⟨n, rfl⟩
    | boolv n => simp [isFFvVar] at this
  · intro v hv
    have := List.of_mem_filter hv
    cases v with
    | ffv n => simp [isFFvVar] at this
    | boolv n => exact ⟨n, rfl⟩

/-- Any `VarSet`'s `.toList` is sorted by `Var`'s `Ord` -- feeds `auxVarsList_ff_bool_split`. -/
theorem varSet_toList_pairwise_lt (s : VarSet) :
    s.toList.Pairwise (fun a b => compare a b = .lt) :=
  Std.TreeSet.ordered_toList

/-- Any `VarSet`'s `.toList` has no repeats. -/
theorem varSet_toList_nodup (s : VarSet) : s.toList.Nodup := by
  have h := Std.TreeSet.distinct_toList (t := s)
  apply List.Pairwise.imp _ h
  intro a b hab heq
  exact hab (Var_compare_eq_iff_eq.mpr heq)

/-- `mapsAfter`'s `ff` component leaves `ffBase` unchanged at any index `vs` never mentions (as
    `.ffv`) -- mirrors `ffMapAfter_frame`, generalized to the mixed segment. -/
theorem mapsAfter_ff_frame {c : ZKConfig} :
    ∀ (vs : List Var) (args : List (MacroCallParam c)) (ffBase : FFVar → FF c)
      (boolBase : BoolVar → Bool) (n : FFVar),
      Var.ffv n ∉ vs → (mapsAfter vs args ffBase boolBase).1 n = ffBase n := by
  intro vs
  induction vs with
  | nil => intro args ffBase boolBase n _; cases args <;> simp [mapsAfter]
  | cons v vs ih =>
      intro args ffBase boolBase n hn
      cases args with
      | nil => simp [mapsAfter]
      | cons a args =>
          have hn' : Var.ffv n ∉ vs := fun h => hn (List.mem_cons_of_mem _ h)
          cases v with
          | ffv m =>
              cases a with
              | var _ => simp [mapsAfter]
              | const cv =>
                cases cv with
                | boolc _ => simp [mapsAfter]
                | ffc t =>
                    have hmn : m ≠ n := fun h => hn (h ▸ List.mem_cons_self ..)
                    simp only [mapsAfter]
                    rw [ih args (fun id => if id == m then t else ffBase id) boolBase n hn']
                    simp [Ne.symm hmn]
          | boolv m =>
              cases a with
              | var _ => simp [mapsAfter]
              | const cv =>
                cases cv with
                | ffc _ => simp [mapsAfter]
                | boolc t =>
                    simp only [mapsAfter]
                    exact ih args ffBase (fun id => if id == m then t else boolBase id) n hn'

/-- Bool-valued mirror of `mapsAfter_ff_frame`. -/
theorem mapsAfter_bool_frame {c : ZKConfig} :
    ∀ (vs : List Var) (args : List (MacroCallParam c)) (ffBase : FFVar → FF c)
      (boolBase : BoolVar → Bool) (n : BoolVar),
      Var.boolv n ∉ vs → (mapsAfter vs args ffBase boolBase).2 n = boolBase n := by
  intro vs
  induction vs with
  | nil => intro args ffBase boolBase n _; cases args <;> simp [mapsAfter]
  | cons v vs ih =>
      intro args ffBase boolBase n hn
      cases args with
      | nil => simp [mapsAfter]
      | cons a args =>
          have hn' : Var.boolv n ∉ vs := fun h => hn (List.mem_cons_of_mem _ h)
          cases v with
          | boolv m =>
              cases a with
              | var _ => simp [mapsAfter]
              | const cv =>
                cases cv with
                | ffc _ => simp [mapsAfter]
                | boolc t =>
                    have hmn : m ≠ n := fun h => hn (h ▸ List.mem_cons_self ..)
                    simp only [mapsAfter]
                    rw [ih args ffBase (fun id => if id == m then t else boolBase id) n hn']
                    simp [Ne.symm hmn]
          | ffv m =>
              cases a with
              | var _ => simp [mapsAfter]
              | const cv =>
                cases cv with
                | boolc _ => simp [mapsAfter]
                | ffc t =>
                    simp only [mapsAfter]
                    exact ih args (fun id => if id == m then t else ffBase id) boolBase n hn'

/-- Reading `mapsAfter vs args ffBase boolBase`'s `ff` component back at the `m`-th index of
    `vs` (given `vs.Nodup` and `vs`/`args` well-typed) recovers exactly the `.ffc` payload
    `args` holds at that same position. -/
theorem mapsAfter_ff_getD {c : ZKConfig} :
    ∀ (vs : List Var) (args : List (MacroCallParam c)) (ffBase : FFVar → FF c)
      (boolBase : BoolVar → Bool),
      List.Forall₂ varsArgsWellTyped vs args → vs.Nodup →
      ∀ m, (hm : m < vs.length) → ∀ n, vs.getD m (Var.ffv 0) = Var.ffv n →
        ∀ t, args.getD m (MacroCallParam.const (Const.ffc 0)) = MacroCallParam.const (Const.ffc t) →
          (mapsAfter vs args ffBase boolBase).1 n = t := by
  intro vs
  induction vs with
  | nil => intro args ffBase boolBase _hforall _hnodup m hm; simp at hm
  | cons v vs ih =>
      intro args ffBase boolBase hforall hnodup m hm n hveq t htveq
      cases args with
      | nil => cases hforall
      | cons a args =>
          obtain ⟨hd, tl⟩ := List.forall₂_cons.mp hforall
          obtain ⟨hv_notmem, hvs_nodup⟩ := List.nodup_cons.mp hnodup
          cases m with
          | zero =>
              simp only [List.getD_cons_zero] at hveq htveq
              subst hveq
              cases a with
              | var _ => simp [varsArgsWellTyped] at hd
              | const cv =>
                cases cv with
                | boolc _ => simp [varsArgsWellTyped] at hd
                | ffc t' =>
                    injection htveq with htveq; injection htveq with htveq
                    subst htveq
                    simp only [mapsAfter]
                    rw [mapsAfter_ff_frame vs args (fun id => if id == n then t' else ffBase id)
                      boolBase n hv_notmem]
                    simp
          | succ m' =>
              simp only [List.getD_cons_succ] at hveq htveq
              cases v with
              | ffv p =>
                  cases a with
                  | var _ => simp [varsArgsWellTyped] at hd
                  | const cv =>
                    cases cv with
                    | boolc _ => simp [varsArgsWellTyped] at hd
                    | ffc t' =>
                        simp only [mapsAfter]
                        exact ih args (fun id => if id == p then t' else ffBase id) boolBase tl
                          hvs_nodup m' (by simpa using hm) n hveq t htveq
              | boolv p =>
                  cases a with
                  | var _ => simp [varsArgsWellTyped] at hd
                  | const cv =>
                    cases cv with
                    | ffc _ => simp [varsArgsWellTyped] at hd
                    | boolc t' =>
                        simp only [mapsAfter]
                        exact ih args ffBase (fun id => if id == p then t' else boolBase id) tl
                          hvs_nodup m' (by simpa using hm) n hveq t htveq

/-- Bool-valued mirror of `mapsAfter_ff_getD`. -/
theorem mapsAfter_bool_getD {c : ZKConfig} :
    ∀ (vs : List Var) (args : List (MacroCallParam c)) (ffBase : FFVar → FF c)
      (boolBase : BoolVar → Bool),
      List.Forall₂ varsArgsWellTyped vs args → vs.Nodup →
      ∀ m, (hm : m < vs.length) → ∀ n, vs.getD m (Var.boolv 0) = Var.boolv n →
        ∀ t, args.getD m (MacroCallParam.const (Const.boolc false)) =
          MacroCallParam.const (Const.boolc t) →
          (mapsAfter vs args ffBase boolBase).2 n = t := by
  intro vs
  induction vs with
  | nil => intro args ffBase boolBase _hforall _hnodup m hm; simp at hm
  | cons v vs ih =>
      intro args ffBase boolBase hforall hnodup m hm n hveq t htveq
      cases args with
      | nil => cases hforall
      | cons a args =>
          obtain ⟨hd, tl⟩ := List.forall₂_cons.mp hforall
          obtain ⟨hv_notmem, hvs_nodup⟩ := List.nodup_cons.mp hnodup
          cases m with
          | zero =>
              simp only [List.getD_cons_zero] at hveq htveq
              subst hveq
              cases a with
              | var _ => simp [varsArgsWellTyped] at hd
              | const cv =>
                cases cv with
                | ffc _ => simp [varsArgsWellTyped] at hd
                | boolc t' =>
                    injection htveq with htveq; injection htveq with htveq
                    subst htveq
                    simp only [mapsAfter]
                    rw [mapsAfter_bool_frame vs args ffBase
                      (fun id => if id == n then t' else boolBase id) n hv_notmem]
                    simp
          | succ m' =>
              simp only [List.getD_cons_succ] at hveq htveq
              cases v with
              | ffv p =>
                  cases a with
                  | var _ => simp [varsArgsWellTyped] at hd
                  | const cv =>
                    cases cv with
                    | boolc _ => simp [varsArgsWellTyped] at hd
                    | ffc t' =>
                        simp only [mapsAfter]
                        exact ih args (fun id => if id == p then t' else ffBase id) boolBase tl
                          hvs_nodup m' (by simpa using hm) n hveq t htveq
              | boolv p =>
                  cases a with
                  | var _ => simp [varsArgsWellTyped] at hd
                  | const cv =>
                    cases cv with
                    | ffc _ => simp [varsArgsWellTyped] at hd
                    | boolc t' =>
                        simp only [mapsAfter]
                        exact ih args ffBase (fun id => if id == p then t' else boolBase id) tl
                          hvs_nodup m' (by simpa using hm) n hveq t htveq

/-- `mapsAfter`, fed the exact self-referential argument list built by reading `assignment'`
    off at each `.ffv`/`.boolv` entry of a *sorted* `l` (ff-tagged entries first, per `Var`'s
    `Ord`), reads back exactly `assignment'.ff n` at any `.ffv n` member of `l` -- the "you get
    back what you fed in" fact needed once `auxFF`/`auxBool` are themselves defined as such
    reads off `assignment'`. -/
theorem mapsAfter_reads_own_ff {c : ZKConfig} (assignment' : Assignment c) :
    ∀ (l : List Var), l.Pairwise (fun a b => compare a b = .lt) →
      ∀ (ffBase : FFVar → FF c) (boolBase : BoolVar → Bool) (n : Nat),
        Var.ffv n ∈ l →
        (mapsAfter l
          ((l.filter isFFvVar).map
              (fun v => MacroCallParam.const (Const.ffc (assignment'.ff (varIndex v)))) ++
           (l.filter (fun v => !isFFvVar v)).map
              (fun v => MacroCallParam.const (Const.boolc (assignment'.bool (varIndex v)))))
          ffBase boolBase).1 n = assignment'.ff n := by
  intro l
  induction l with
  | nil => intro _ ffBase boolBase n hn; simp at hn
  | cons v l ih =>
      intro hsorted ffBase boolBase n hn
      obtain ⟨hrel, htail⟩ := List.pairwise_cons.mp hsorted
      cases v with
      | ffv m =>
          have hp : isFFvVar (Var.ffv m) = true := rfl
          have hp2 : ¬ (fun v => !isFFvVar v) (Var.ffv m) = true := by simp [isFFvVar]
          have hnotin : Var.ffv m ∉ l := fun hmem => by
            have hc := hrel (Var.ffv m) hmem
            rw [Std.ReflCmp.compare_self (cmp := (compare : Var → Var → Ordering))] at hc
            exact absurd hc (by decide)
          simp only [List.filter_cons_of_pos hp, List.filter_cons_of_neg hp2,
            List.map_cons, List.cons_append, mapsAfter, varIndex]
          rcases List.mem_cons.mp hn with heq | hmem
          · injection heq with heq
            subst heq
            rw [mapsAfter_ff_frame l _ _ boolBase n hnotin]
            simp
          · exact ih htail (fun id => if id == m then assignment'.ff m else ffBase id) boolBase n
              hmem
      | boolv m =>
          have hp : ¬ isFFvVar (Var.boolv m) = true := by simp [isFFvVar]
          have hp' : (fun v => !isFFvVar v) (Var.boolv m) = true := by simp [isFFvVar]
          have hnone : l.filter isFFvVar = [] := by
            rw [List.filter_eq_nil_iff]
            intro w hw
            cases w with
            | ffv k =>
                have hc := hrel (Var.ffv k) hw
                have hcontra : compare (Var.boolv m) (Var.ffv k) = Ordering.gt := rfl
                rw [hcontra] at hc
                simp at hc
            | boolv k => simp [isFFvVar]
          simp only [hnone, List.map_nil, List.nil_append] at ih
          rw [List.filter_cons_of_neg hp, hnone,
            List.filter_cons_of_pos (p := fun v => !isFFvVar v) (a := Var.boolv m) hp',
            List.map_nil, List.nil_append, List.map_cons]
          simp only [mapsAfter, varIndex]
          have hne : Var.ffv n ≠ Var.boolv m := by simp
          rcases List.mem_cons.mp hn with heq | hmem
          · exact absurd heq hne
          · exact ih htail ffBase (fun id => if id == m then assignment'.bool m else boolBase id) n
              hmem

/-- Bool-valued mirror of `mapsAfter_reads_own_ff`. -/
theorem mapsAfter_reads_own_bool {c : ZKConfig} (assignment' : Assignment c) :
    ∀ (l : List Var), l.Pairwise (fun a b => compare a b = .lt) →
      ∀ (ffBase : FFVar → FF c) (boolBase : BoolVar → Bool) (n : Nat),
        Var.boolv n ∈ l →
        (mapsAfter l
          ((l.filter isFFvVar).map
              (fun v => MacroCallParam.const (Const.ffc (assignment'.ff (varIndex v)))) ++
           (l.filter (fun v => !isFFvVar v)).map
              (fun v => MacroCallParam.const (Const.boolc (assignment'.bool (varIndex v)))))
          ffBase boolBase).2 n = assignment'.bool n := by
  intro l
  induction l with
  | nil => intro _ ffBase boolBase n hn; simp at hn
  | cons v l ih =>
      intro hsorted ffBase boolBase n hn
      obtain ⟨hrel, htail⟩ := List.pairwise_cons.mp hsorted
      cases v with
      | ffv m =>
          have hp : isFFvVar (Var.ffv m) = true := rfl
          have hp2 : ¬ (fun v => !isFFvVar v) (Var.ffv m) = true := by simp [isFFvVar]
          have hne : Var.boolv n ≠ Var.ffv m := by simp
          rw [List.filter_cons_of_pos hp,
            List.filter_cons_of_neg (p := fun v => !isFFvVar v) (a := Var.ffv m) hp2,
            List.map_cons, List.cons_append]
          simp only [mapsAfter, varIndex]
          rcases List.mem_cons.mp hn with heq | hmem
          · exact absurd heq hne
          · exact ih htail (fun id => if id == m then assignment'.ff m else ffBase id) boolBase n
              hmem
      | boolv m =>
          have hp : ¬ isFFvVar (Var.boolv m) = true := by simp [isFFvVar]
          have hp' : (fun v => !isFFvVar v) (Var.boolv m) = true := by simp [isFFvVar]
          have hnone : l.filter isFFvVar = [] := by
            rw [List.filter_eq_nil_iff]
            intro w hw
            cases w with
            | ffv k =>
                have hc := hrel (Var.ffv k) hw
                have hcontra : compare (Var.boolv m) (Var.ffv k) = Ordering.gt := rfl
                rw [hcontra] at hc
                simp at hc
            | boolv k => simp [isFFvVar]
          have hnotin : Var.boolv m ∉ l := fun hmem => by
            have hc := hrel (Var.boolv m) hmem
            rw [Std.ReflCmp.compare_self (cmp := (compare : Var → Var → Ordering))] at hc
            exact absurd hc (by decide)
          simp only [hnone, List.map_nil, List.nil_append] at ih
          rw [List.filter_cons_of_neg hp, hnone,
            List.filter_cons_of_pos (p := fun v => !isFFvVar v) (a := Var.boolv m) hp',
            List.map_nil, List.nil_append, List.map_cons]
          simp only [mapsAfter, varIndex]
          rcases List.mem_cons.mp hn with heq | hmem
          · injection heq with heq
            subst heq
            rw [mapsAfter_bool_frame l _ ffBase _ n hnotin]
            simp
          · exact ih htail ffBase (fun id => if id == m then assignment'.bool m else boolBase id) n
              hmem





/-- Filtering by a predicate and by its negation always splits a list's length. -/
theorem length_filter_add_length_filter_not {α : Type} (p : α → Bool) (l : List α) :
    (l.filter p).length + (l.filter (fun x => !p x)).length = l.length :=
  (List.length_eq_length_filter_add p).symm

/-- Generic append lemma for `List.Forall₂` (not found under an obvious name in the vendored
    `Std`/core library, so proved by hand). -/
theorem forall2_append {α β : Type} {R : α → β → Prop} :
    ∀ {l1 l1' : List α} {l2 l2' : List β},
      List.Forall₂ R l1 l2 → List.Forall₂ R l1' l2' → List.Forall₂ R (l1 ++ l1') (l2 ++ l2') := by
  intro l1 l1' l2 l2' h1 h2
  induction h1 with
  | nil => simpa using h2
  | cons hd tl ih => simpa using List.Forall₂.cons hd ih

/-- A length-matched all-`.ffv` prefix, zipped against `.const .ffc`-wrapped values, is always
    well-typed (`varsArgsWellTyped` is trivially `True` on every `.ffv`/`.const .ffc` pair). -/
theorem forall2_ff_const {c : ZKConfig} :
    ∀ (vs : List Var) (vals : List (FF c)),
      vs.length = vals.length → (∀ v ∈ vs, ∃ n, v = Var.ffv n) →
      List.Forall₂ varsArgsWellTyped vs
        (vals.map (fun t => MacroCallParam.const (Const.ffc t))) := by
  intro vs
  induction vs with
  | nil =>
      intro vals hlen _hff
      cases vals with
      | nil => exact List.Forall₂.nil
      | cons _ _ => simp at hlen
  | cons v vs ih =>
      intro vals hlen hff
      cases vals with
      | nil => simp at hlen
      | cons val vals =>
          obtain ⟨n, hn⟩ := hff v (List.mem_cons_self ..)
          subst hn
          simp only [List.map_cons]
          exact List.Forall₂.cons trivial
            (ih vals (by simpa using hlen) (fun v' hv' => hff v' (List.mem_cons_of_mem _ hv')))

/-- Bool-valued mirror of `forall2_ff_const`. -/
theorem forall2_bool_const {c : ZKConfig} :
    ∀ (vs : List Var) (vals : List Bool),
      vs.length = vals.length → (∀ v ∈ vs, ∃ n, v = Var.boolv n) →
      List.Forall₂ (varsArgsWellTyped (c := c)) vs
        (vals.map (fun t => MacroCallParam.const (Const.boolc t))) := by
  intro vs
  induction vs with
  | nil =>
      intro vals hlen _hbool
      cases vals with
      | nil => exact List.Forall₂.nil
      | cons _ _ => simp at hlen
  | cons v vs ih =>
      intro vals hlen hbool
      cases vals with
      | nil => simp at hlen
      | cons val vals =>
          obtain ⟨n, hn⟩ := hbool v (List.mem_cons_self ..)
          subst hn
          simp only [List.map_cons]
          exact List.Forall₂.cons trivial
            (ih vals (by simpa using hlen) (fun v' hv' => hbool v' (List.mem_cons_of_mem _ hv')))

/-- Combines `auxVarsList_ff_bool_split` with `forall2_ff_const`/`forall2_bool_const`: given
    `auxFF`/`auxBool` whose lengths match the aux list's own `.ffv`/`.boolv` counts, the whole
    aux segment (`.ffv`-then-`.boolv`, per `l`'s sortedness) pairs correctly against
    `auxFF`'s/`auxBool`'s `.const`-wrapped values, in that same concatenated order. -/
theorem forall2_aux_split {c : ZKConfig} (l : List Var)
    (hsorted : l.Pairwise (fun a b => compare a b = .lt))
    (auxFF : List (FF c)) (auxBool : List Bool)
    (hFFlen : auxFF.length = (l.filter isFFvVar).length)
    (hBoollen : auxBool.length = l.length - (l.filter isFFvVar).length) :
    List.Forall₂ varsArgsWellTyped l
      (auxFF.map (fun t => MacroCallParam.const (Const.ffc t)) ++
        auxBool.map (fun t => MacroCallParam.const (Const.boolc t))) := by
  obtain ⟨htake, hdrop, hffmem, hboolmem⟩ := auxVarsList_ff_bool_split l hsorted
  have hlensplit : l.length = (l.filter isFFvVar).length + auxBool.length := by
    rw [hBoollen]
    have : (l.filter isFFvVar).length ≤ l.length := List.length_filter_le _ _
    omega
  have hFF := forall2_ff_const (l.take (l.filter isFFvVar).length) auxFF
    (by rw [htake, hFFlen]) (by rw [htake]; exact hffmem)
  have hBool := forall2_bool_const (c := c) (l.drop (l.filter isFFvVar).length) auxBool
    (by rw [List.length_drop]; omega) (by rw [hdrop]; exact hboolmem)
  have hcomb := forall2_append hFF hBool
  rw [List.take_append_drop] at hcomb
  exact hcomb


/-- Every variable `mintFreshParam` mints for a single param is mentioned by the returned
    `SymValue` exactly iff it's one of the freshly-minted `Var`s -- i.e. `sv`'s vars and `vs`
    coincide exactly (not just "below a bound", the way `mintFreshParam_symValVars_below` puts
    it). -/
theorem mintFreshParam_symValVars_mem_iff {c : ZKConfig} (nextVarId : Nat) (type : VarType)
    (nv1 : Nat) (vs : List Var) (sv : SymValue c)
    (h : mintFreshParam (c := c) nextVarId type = Except.ok (nv1, vs, sv)) (v : Var) :
    v ∈ symValVars sv ↔ v ∈ vs := by
  obtain ⟨hvs_eq, _⟩ := mintFreshParam_eq nextVarId type nv1 vs sv h
  cases type with
  | ff =>
      simp only [mintFreshParam, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.2.2, hvs_eq]
      simp only [symValVars, simpleValVars, typeSize, List.range_one, List.map_cons, List.map_nil]
      rw [List.mem_singleton]
      simp only [Nat.add_zero]
      constructor
      · intro hv
        rcases Std.TreeSet.mem_insert.mp hv with heq | hmem
        · exact (Var_compare_eq_iff_eq.mp heq).symm
        · exact absurd hmem Std.TreeSet.not_mem_emptyc
      · intro hv; subst hv; exact Std.TreeSet.mem_insert_self
  | array n =>
      simp only [mintFreshParam, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.2.2, hvs_eq]
      simp only [symValVars]
      rw [← Array.foldl_toList, List.toList_toArray, List.map_map]
      constructor
      · intro hv
        rcases foldl_union_mem_elim simpleValVars _ emptyVarSet v hv with h1 | ⟨s, hs, h2⟩
        · exact absurd h1 Std.TreeSet.not_mem_emptyc
        · obtain ⟨i, hi, hieq⟩ := List.mem_map.mp hs
          subst hieq
          simp only [Function.comp, simpleValVars] at h2
          rcases Std.TreeSet.mem_insert.mp h2 with heq | hmem
          · rw [← Var_compare_eq_iff_eq.mp heq]
            exact List.mem_map.mpr ⟨i, hi, rfl⟩
          · exact absurd hmem Std.TreeSet.not_mem_emptyc
      · intro hv
        obtain ⟨i, hi, hieq⟩ := List.mem_map.mp hv
        apply foldl_union_mem_subset simpleValVars ((List.range n).map
            (fun i => SimpleSymVal.ffvar { var := nextVarId + i, bits := none }))
          (SimpleSymVal.ffvar { var := nextVarId + i, bits := none })
          (List.mem_map.mpr ⟨i, hi, rfl⟩) emptyVarSet
        rw [← hieq]
        simp only [simpleValVars]
        exact Std.TreeSet.mem_insert_self

theorem mintFreshParams_symEnvVars_subset {c : ZKConfig} :
    ∀ (nextVarId : Nat) (params : List Param) (symEnv : SymEnv c),
      ∀ (nv1 : Nat) (paramVars : List Var) (symEnv' : SymEnv c),
        mintFreshParams (c := c) nextVarId params symEnv = Except.ok (nv1, paramVars, symEnv') →
        ∀ v ∈ symEnvVars symEnv', v ∈ symEnvVars symEnv ∨ v ∈ paramVars := by
  intro nextVarId params
  induction params generalizing nextVarId with
  | nil =>
      intro symEnv nv1 paramVars symEnv' h v hv
      simp only [mintFreshParams, Except.ok.injEq, Prod.mk.injEq] at h
      left
      rw [h.2.2]
      exact hv
  | cons p ps ih =>
      intro symEnv nv1 paramVars symEnv' h v hv
      simp only [mintFreshParams] at h
      cases hmp : mintFreshParam (c := c) nextVarId p.type with
      | error e => simp [hmp] at h
      | ok result =>
          obtain ⟨nv2, vs, sv⟩ := result
          simp only [hmp] at h
          cases hrest : mintFreshParams (c := c) nv2 ps (setVar symEnv p.name sv) with
          | error e => simp [hrest] at h
          | ok result2 =>
              obtain ⟨nv3, vs2, env2⟩ := result2
              simp only [hrest, Except.ok.injEq, Prod.mk.injEq] at h
              have hind := ih nv2 (setVar symEnv p.name sv) nv3 vs2 env2 hrest
              rw [← h.2.2] at hv
              rcases hind v hv with h1 | h2
              · rcases symEnvVars_setVar_subset symEnv p.name sv v h1 with h1a | h1b
                · left; exact h1a
                · right
                  rw [← h.2.1]
                  exact List.mem_append_left _
                    ((mintFreshParam_symValVars_mem_iff nextVarId p.type nv2 vs sv hmp v).mp h1b)
              · right
                rw [← h.2.1]
                exact List.mem_append_right _ h2

/-- `getVar`'s own definition, stated as an iff against `.get?` directly (used to connect
    `getOutParamsValues`'s per-position reads back to a concrete `Env`'s stored values). -/
theorem getVar_eq_ok_iff {c : ZKConfig} (env : Env c) (id : VarID) (v : Value c) :
    getVar env id = Except.ok v ↔ env.get? id = some v := by
  simp only [Corellzk2smt.Language.Core.Semantics.Basic.getVar]
  cases env.get? id with
  | none => simp
  | some v' => simp

/-- Symbolic-side mirror of `getVar_eq_ok_iff`. -/
theorem getVar_eq_ok_iff_sym {c : ZKConfig} (env : SymEnv c) (id : VarID) (v : SymValue c) :
    Corellzk2smt.SymExec.Basic.getVar env id = Except.ok v ↔ env.get? id = some v := by
  simp only [Corellzk2smt.SymExec.Basic.getVar]
  cases env.get? id with
  | none => simp
  | some v' => simp

/-- If `getOutParamsValues` succeeds, every value it returns is exactly whatever concrete value
    already sat at that ret's name in `env` -- the read-position mirror of
    `getOutParamsValues_construct`. -/
theorem getOutParamsValues_getD {c : ZKConfig} :
    ∀ (env : Env c) (rets : List Param) (vs : List (Value c)),
      getOutParamsValues env rets = Except.ok vs →
      ∀ i, i < rets.length → env.get? (rets.getD i default).name = some (vs.getD i default) := by
  intro env rets
  induction rets with
  | nil => intro vs _h i hi; simp at hi
  | cons r rs ih =>
      intro vs h i hi
      simp only [getOutParamsValues] at h
      cases hg : getVar env r.name with
      | error e => simp [hg] at h
      | ok v =>
          simp only [hg] at h
          cases hect : ensureCorrectType v r.type with
          | error e => simp [hect] at h
          | ok _ =>
              simp only [hect] at h
              cases hrest : getOutParamsValues env rs with
              | error e => simp [hrest] at h
              | ok vsRest =>
                  simp only [hrest, Except.ok.injEq] at h
                  cases i with
                  | zero =>
                      simp only [List.getD_cons_zero]
                      rw [← h]
                      simp only [List.getD_cons_zero]
                      exact (getVar_eq_ok_iff env r.name v).mp hg
                  | succ i' =>
                      simp only [List.getD_cons_succ]
                      rw [← h]
                      simp only [List.getD_cons_succ]
                      exact ih vsRest hrest i' (by simpa using hi)

/-- Every element of `l` (or already in `s`) survives folding `insert` over `l` starting from
    `s` -- used to show `paramVars`/`retVars` (as lists) inject into `paramVarSet`/`retVarSet`
    (the `VarSet`s `seFunc` builds from them). -/
theorem mem_foldl_insert_var :
    ∀ (l : List Var) (v : Var) (s : VarSet),
      v ∈ s ∨ v ∈ l → v ∈ l.foldl (fun acc x => acc.insert x) s := by
  intro l
  induction l with
  | nil =>
      intro v s h
      rcases h with h | h
      · exact h
      · exact absurd h (by simp)
  | cons x l ih =>
      intro v s h
      simp only [List.foldl_cons]
      apply ih v (s.insert x)
      rcases h with h | h
      · left; exact Std.TreeSet.mem_insert.mpr (Or.inr h)
      · rcases List.mem_cons.mp h with heq | hmem
        · left; subst heq; exact Std.TreeSet.mem_insert.mpr (Or.inl (Var_compare_eq_iff_eq.mpr rfl))
        · right; exact hmem

/-- Converse of `mem_foldl_insert_var`. -/
theorem foldl_insert_var_mem :
    ∀ (l : List Var) (v : Var) (s : VarSet),
      v ∈ l.foldl (fun acc x => acc.insert x) s → v ∈ s ∨ v ∈ l := by
  intro l
  induction l with
  | nil => intro v s h; left; exact h
  | cons x l ih =>
      intro v s h
      simp only [List.foldl_cons] at h
      rcases ih v (s.insert x) h with h1 | h1
      · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
        · right
          have hxv : x = v := Var_compare_eq_iff_eq.mp heq
          rw [← hxv]; exact List.mem_cons_self ..
        · left; exact hmem
      · right; exact List.mem_cons_of_mem _ h1

/-- `hasDupNames l = false` means `l` has no repeated element -- direct induction mirroring
    `hasDupNames`'s own recursive structure. -/
theorem hasDupNames_false_nodup : ∀ (l : List VarID), hasDupNames l = false → l.Nodup := by
  intro l
  induction l with
  | nil => intro _; exact List.nodup_nil
  | cons a l ih =>
      intro h
      simp only [hasDupNames, Bool.or_eq_false_iff] at h
      exact List.nodup_cons.mpr ⟨by simpa using h.1, ih h.2⟩

/-- `mintFreshParams` never disturbs a key it doesn't itself mint a fresh var for. -/
theorem mintFreshParams_preserves_getVar {c : ZKConfig} :
    ∀ (nextVarId : Nat) (params : List Param) (symEnv : SymEnv c) (id : VarID) (sv : SymValue c),
      id ∉ params.map (·.name) →
      symEnv.get? id = some sv →
      ∀ (nv1 : Nat) (paramVars : List Var) (symEnv' : SymEnv c),
        mintFreshParams (c := c) nextVarId params symEnv = Except.ok (nv1, paramVars, symEnv') →
        symEnv'.get? id = some sv := by
  intro nextVarId params
  induction params generalizing nextVarId with
  | nil =>
      intro symEnv id sv _hnotmem hget nv1 paramVars symEnv' h
      simp only [mintFreshParams, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.2.2]; exact hget
  | cons p ps ih =>
      intro symEnv id sv hnotmem hget nv1 paramVars symEnv' h
      simp only [mintFreshParams] at h
      cases hmp : mintFreshParam (c := c) nextVarId p.type with
      | error e => simp [hmp] at h
      | ok result =>
          obtain ⟨nv2, vs, sv0⟩ := result
          simp only [hmp] at h
          cases hrest : mintFreshParams (c := c) nv2 ps (setVar symEnv p.name sv0) with
          | error e => simp [hrest] at h
          | ok result2 =>
              obtain ⟨nv3, vs2, env2⟩ := result2
              simp only [hrest, Except.ok.injEq, Prod.mk.injEq] at h
              rw [← h.2.2]
              have hne : p.name ≠ id := fun heq => hnotmem (heq ▸ List.mem_cons_self ..)
              have hget1 : (Corellzk2smt.SymExec.Basic.setVar symEnv p.name sv0).get?
                  id = some sv := by
                simp only [Corellzk2smt.SymExec.Basic.setVar, Std.TreeMap.get?_eq_getElem?,
                  Std.TreeMap.getElem?_insert, Std.compare_eq_iff_eq, hne, if_false]
                rw [← Std.TreeMap.get?_eq_getElem?]; exact hget
              exact ih nv2 _ id sv (fun hmem => hnotmem (List.mem_cons_of_mem _ hmem))
                hget1 nv3 vs2 env2 hrest


/-- `List.map Value.scalar` is injective -- `Value.scalar` is a constructor. -/
theorem list_scalar_map_injective {c : ZKConfig} :
    ∀ (l1 l2 : List (FF c)), l1.map Value.scalar = l2.map Value.scalar → l1 = l2 := by
  intro l1
  induction l1 with
  | nil => intro l2 h; cases l2 with | nil => rfl | cons _ _ => simp at h
  | cons a l1 ih =>
      intro l2 h
      cases l2 with
      | nil => simp at h
      | cons b l2 =>
          simp only [List.map_cons, List.cons.injEq] at h
          obtain ⟨hab, htl⟩ := h
          injection hab with hab
          rw [hab, ih l2 htl]

/-- `flattenValuesToFF`'s length is exactly `totalParamSize params`, given `vs` matches `params`'s
    shape -- the flattened-block-size companion to `flattenValueToFF_length` (single value),
    needed to feed `ffMapAfter`/`newAssignment'_ff_prepend`'s plain length-matching hypothesis
    once `argVals`/`retVals` become array-general `List (Value c)` instead of `List (FF c)`. -/
theorem flattenValuesToFF_length {c : ZKConfig} :
    ∀ (vs : List (Value c)) (params : List Param), ValuesMatchParams vs params →
      (flattenValuesToFF vs).length = totalParamSize params := by
  intro vs params hmatch
  induction hmatch with
  | nil => rfl
  | cons hd tl ih =>
      rename_i v p vs' params'
      have hstep : flattenValuesToFF (v :: vs') = flattenValueToFF v ++ flattenValuesToFF vs' := by
        simp only [flattenValuesToFF, List.map_cons, List.flatten_cons]
      rw [hstep, List.length_append, totalParamSize_cons, flattenValueToFF_length v p.type hd, ih]
      rfl

/-- Reading `flattenValuesToFF vs` at the block belonging to `params[i]` (offset
    `totalParamSize (params.take i)`, `j`-th element within that block) agrees with reading
    `vs[i]`'s own flattening at position `j` -- the "which value does this flattened position
    belong to" fact needed to connect a flat assignment position back to a specific arg/ret's own
    (possibly array-shaped) value. -/
theorem flattenValuesToFF_getD_block {c : ZKConfig} :
    ∀ (vs : List (Value c)) (params : List Param), ValuesMatchParams vs params →
      ∀ i, (hi : i < params.length) → ∀ j, j < typeSize (params.getD i default).type →
        (flattenValuesToFF vs).getD (totalParamSize (params.take i) + j) 0 =
          (flattenValueToFF (vs.getD i default)).getD j 0 := by
  intro vs params hmatch
  induction hmatch with
  | nil => intro i hi; simp at hi
  | cons hd tl ih =>
      rename_i v p vs' params'
      intro i hi j hj
      cases i with
      | zero =>
          simp only [List.getD_cons_zero, List.take_zero, totalParamSize_nil, Nat.zero_add]
          have hjlt : j < (flattenValueToFF v).length := by
            rw [flattenValueToFF_length v p.type hd]; exact hj
          exact flattenValuesToFF_getD_head v vs' j hjlt
      | succ i' =>
          simp only [List.getD_cons_succ]
          have hstep : totalParamSize ((p :: params').take (i' + 1)) =
              (flattenValueToFF v).length + totalParamSize (params'.take i') := by
            rw [List.take_succ_cons, totalParamSize_cons, flattenValueToFF_length v p.type hd]
            rfl
          rw [hstep]
          have hge : (flattenValueToFF v).length ≤
              (flattenValueToFF v).length + totalParamSize (params'.take i') + j := by omega
          rw [flattenValuesToFF_getD_tail v vs' _ hge]
          rw [show (flattenValueToFF v).length + totalParamSize (params'.take i') + j -
              (flattenValueToFF v).length = totalParamSize (params'.take i') + j from by omega]
          exact ih i' (by simpa using hi) j hj

/-- The block `params[i]` occupies (`totalParamSize (params.take i)`, `typeSize (params[i]).type`
    wide) fits entirely inside `[0, totalParamSize params)` -- needed to relate a per-element
    `(i, j)` position back to a flat bound on the whole list. -/
theorem totalParamSize_take_add_typeSize_le :
    ∀ (params : List Param) (i : Nat), i < params.length →
      totalParamSize (params.take i) + typeSize (params.getD i default).type ≤
        totalParamSize params := by
  intro params
  induction params with
  | nil => intro i hi; simp at hi
  | cons p ps ih =>
      intro i hi
      cases i with
      | zero =>
          simp only [List.take_zero, totalParamSize_nil, Nat.zero_add, List.getD_cons_zero]
          rw [totalParamSize_cons]
          have hps : paramSize p = typeSize p.type := rfl
          omega
      | succ i' =>
          simp only [List.getD_cons_succ, List.take_succ_cons, totalParamSize_cons]
          have hind := ih i' (by simpa using hi)
          have hps : paramSize p = typeSize p.type := rfl
          omega

-- ---------------------------------------------------------------------------
-- Array-general replacement for the old FF-only `retEqFormula_sound`/`retEqFormula_complete`/
-- `mintFreshRetsWithEq_sv_vars_sub`/`mintFreshRetsWithEq_getVar_exists`/
-- `getOutParamsValues_construct` (Phase 3b of the array-generalization plan; the FF-only versions
-- have since been removed). `mintFreshRetWithEq` mints a *block* of `typeSize r.type` fresh vars
-- per return (1 for `.ff`, `size` for `.array size`), each tied to the corresponding element of
-- whatever `SimpleSymVal` the body actually computed there via a per-element `.eq`, conjoined
-- (`.and`/`.foldr`) across the whole block. These generalize to arbitrary block sizes via
-- `symValueElems`, mirroring `mintFreshRets_outVals_symValMatches` (`FuncCallCorrectness.lean`)'s
-- own array-block reasoning.
-- ---------------------------------------------------------------------------

/-- The flat list of `SimpleSymVal`s a `SymValue` denotes -- one element for `.simple`, `arr`'s
    own elements (in order) for `.array`. -/
def symValueElems {c : ZKConfig} (sv : SymValue c) : List (SimpleSymVal c) :=
  match sv with
  | SymValue.simple s => [s]
  | SymValue.array arr => arr.toList


/-- Soundness of a block of per-element tie-back equations, at consecutive assignment offsets
    starting at `nextVarId`: if the assignment agrees with each element's own denoted value there,
    the whole conjunction evaluates `true`. The generic "block of equations" core both
    `mintFreshRetWithEq`'s `.ff` and `.array` branches reduce to. -/
theorem eqs_sound {c : ZKConfig} (gconf : GlobalConfig c) (ms : List (FFMacro c))
    (assign : Assignment c) :
    ∀ (elems : List (SimpleSymVal c)) (nextVarId : Nat),
      (∀ j, j < elems.length →
        evalTerm gconf assign (simpleSymValToTerm (elems.getD j default)) ms =
          Except.ok (assign.ff (nextVarId + j))) →
      evalFormula gconf assign
        (((elems.zip ((List.range elems.length).map (fun i => nextVarId + i))).map
          (fun p => FFFormula.eq (FFTerm.var p.2) (simpleSymValToTerm p.1))).foldr
          FFFormula.and FFFormula.true) ms = Except.ok true := by
  intro elems
  induction elems with
  | nil => intro nextVarId _; simp [evalFormula]
  | cons e es ih =>
      intro nextVarId hrange
      have hrange0 := hrange 0 (by simp)
      simp only [List.getD_cons_zero, Nat.add_zero] at hrange0
      have hrange' : ∀ j, j < es.length →
          evalTerm gconf assign (simpleSymValToTerm (es.getD j default)) ms =
            Except.ok (assign.ff (nextVarId + 1 + j)) := by
        intro j hj
        have h1 := hrange (j+1) (by simp; omega)
        have hnat : nextVarId + (j+1) = nextVarId + 1 + j := by omega
        rw [hnat] at h1
        simpa using h1
      have hih := ih (nextVarId+1) hrange'
      simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
      simp only [List.zip_cons_cons, List.map_cons, List.foldr_cons]
      simp only [evalFormula]
      rw [hrange0]
      have hcongr : (List.range es.length).map ((fun i => nextVarId + i) ∘ Nat.succ) =
          (List.range es.length).map (fun i => nextVarId + 1 + i) := by
        apply List.map_congr_left
        intro i _
        show nextVarId + (i + 1) = nextVarId + 1 + i
        omega
      rw [hcongr]
      simp only [evalTerm, Nat.add_zero, BEq.rfl, Bool.true_and]
      rw [hih]

/-- Converse of `eqs_sound`. -/
theorem eqs_complete {c : ZKConfig} (gconf : GlobalConfig c) (ms : List (FFMacro c))
    (assign : Assignment c) :
    ∀ (elems : List (SimpleSymVal c)) (nextVarId : Nat),
      evalFormula gconf assign
        (((elems.zip ((List.range elems.length).map (fun i => nextVarId + i))).map
          (fun p => FFFormula.eq (FFTerm.var p.2) (simpleSymValToTerm p.1))).foldr
          FFFormula.and FFFormula.true) ms = Except.ok true →
      ∀ j, j < elems.length →
        evalTerm gconf assign (simpleSymValToTerm (elems.getD j default)) ms =
          Except.ok (assign.ff (nextVarId + j)) := by
  intro elems
  induction elems with
  | nil => intro nextVarId _heval j hj; simp at hj
  | cons e es ih =>
      intro nextVarId heval j hj
      simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map] at heval
      have hcongr : (List.range es.length).map ((fun i => nextVarId + i) ∘ Nat.succ) =
          (List.range es.length).map (fun i => nextVarId + 1 + i) := by
        apply List.map_congr_left
        intro i _
        show nextVarId + (i + 1) = nextVarId + 1 + i
        omega
      rw [hcongr] at heval
      simp only [List.zip_cons_cons, List.map_cons, List.foldr_cons, Nat.add_zero] at heval
      set eqf : FFFormula c := FFFormula.eq (FFTerm.var nextVarId) (simpleSymValToTerm e)
        with heqf_def
      set restf : FFFormula c := List.foldr FFFormula.and FFFormula.true
          (List.map (fun p => FFFormula.eq (FFTerm.var p.2) (simpleSymValToTerm p.1))
            (es.zip (List.map (fun i => nextVarId + 1 + i) (List.range es.length))))
        with hrestf_def
      clear_value eqf restf
      simp only [evalFormula] at heval
      cases heq1 : evalFormula gconf assign eqf ms with
      | error e' => rw [heq1] at heval; simp at heval
      | ok b1 =>
        rw [heq1] at heval
        cases heq2 : evalFormula gconf assign restf ms with
        | error e'' => rw [heq2] at heval; simp at heval
        | ok b2 =>
          rw [heq2] at heval
          simp only [Except.ok.injEq] at heval
          have hb1 : b1 = true := by by_contra hcon; simp [hcon] at heval
          have hb2 : b2 = true := by by_contra hcon; simp [hcon] at heval
          cases j with
          | zero =>
              simp only [List.getD_cons_zero, Nat.add_zero]
              rw [heqf_def] at heq1
              simp only [evalFormula] at heq1
              cases ht1 : evalTerm gconf assign (FFTerm.var nextVarId) ms with
              | error e3 => rw [ht1] at heq1; simp at heq1
              | ok ta =>
                rw [ht1] at heq1
                cases ht2 : evalTerm gconf assign (simpleSymValToTerm e) ms with
                | error e4 => rw [ht2] at heq1; simp at heq1
                | ok tb =>
                  rw [ht2] at heq1
                  simp only [Except.ok.injEq] at heq1
                  rw [hb1] at heq1
                  have htab' : ta = tb := by
                    have := heq1.symm
                    simpa using this
                  have hta : assign.ff nextVarId = ta := by
                    simp only [evalTerm] at ht1
                    injection ht1
                  have htb : tb = assign.ff nextVarId := by rw [← htab', hta]
                  rw [htb]
          | succ j' =>
              have heval2 : evalFormula gconf assign restf ms = Except.ok true :=
                heq2.trans (congrArg Except.ok hb2)
              rw [hrestf_def] at heval2
              have hind := ih (nextVarId+1) heval2 j' (by simpa using hj)
              have hnat : nextVarId + 1 + j' = nextVarId + (j' + 1) := by omega
              rw [hnat] at hind
              simpa using hind

/-- Vars-membership companion to `eqs_sound`/`eqs_complete`: every var mentioned by the `j`-th
    element (`j < elems.length`) is captured by the whole block's own var-set. -/
theorem eqs_vars_mem {c : ZKConfig} :
    ∀ (elems : List (SimpleSymVal c)) (nextVarId : Nat) (j : Nat), j < elems.length →
      ∀ w ∈ simpleValVars (elems.getD j default),
        w ∈ ffVarsOfFormula
              (((elems.zip ((List.range elems.length).map (fun i => nextVarId + i))).map
                (fun p => FFFormula.eq (FFTerm.var p.2) (simpleSymValToTerm p.1))).foldr
                FFFormula.and FFFormula.true) ∪
            bVarsOfFormula
              (((elems.zip ((List.range elems.length).map (fun i => nextVarId + i))).map
                (fun p => FFFormula.eq (FFTerm.var p.2) (simpleSymValToTerm p.1))).foldr
                FFFormula.and FFFormula.true) := by
  intro elems
  induction elems with
  | nil => intro nextVarId j hj; simp at hj
  | cons e es ih =>
      intro nextVarId j hj w hw
      have hcongr : (List.range es.length).map ((fun i => nextVarId + i) ∘ Nat.succ) =
          (List.range es.length).map (fun i => nextVarId + 1 + i) := by
        apply List.map_congr_left
        intro i _
        show nextVarId + (i + 1) = nextVarId + 1 + i
        omega
      simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, hcongr,
        List.zip_cons_cons, List.foldr_cons, Nat.add_zero]
      simp only [ffVarsOfFormula, bVarsOfFormula]
      cases j with
      | zero =>
          simp only [List.getD_cons_zero] at hw
          simp only [ffVarsOfFormula, bVarsOfFormula, ffVarsOfTerm, ffVarsOfTerm_simpleSymValToTerm,
            bVarsOfTerm, bVarsOfTerm_simpleSymValToTerm]
          exact Std.TreeSet.mem_union_of_left
            (Std.TreeSet.mem_union_of_left (Std.TreeSet.mem_union_of_right hw))
      | succ j' =>
          simp only [List.getD_cons_succ] at hw
          have hind := ih (nextVarId + 1) j' (by simpa using hj) w hw
          rcases Std.TreeSet.mem_union_iff.mp hind with hind' | hind'
          · exact Std.TreeSet.mem_union_of_left (Std.TreeSet.mem_union_of_right hind')
          · exact Std.TreeSet.mem_union_of_right (Std.TreeSet.mem_union_of_right hind')

/-- Soundness of a single ret's own tie-back equation(s) (`mintFreshRetWithEq`'s `eqf` output),
    given the assignment agrees with `sv`'s own flattened elements (`symValueElems`) over the
    ret's block -- covers both the `.ff` (one element) and `.array` (`size` elements) cases via
    `eqs_sound`. -/
theorem mintFreshRetWithEq_eqf_sound {c : ZKConfig} (gconf : GlobalConfig c) (ms : List (FFMacro c))
    (assign : Assignment c) (nextVarId : Nat) (bodySymEnv : SymEnv c) (r : Param)
    (nv1 : Nat) (vs : List Var) (sv' : SymValue c) (eqf : FFFormula c)
    (h : mintFreshRetWithEq (c := c) nextVarId bodySymEnv r = Except.ok (nv1, vs, sv', eqf))
    (sv : SymValue c) (hgv : getVar bodySymEnv r.name = Except.ok sv)
    (hrange : ∀ j, j < typeSize r.type →
      evalTerm gconf assign (simpleSymValToTerm ((symValueElems sv).getD j default)) ms =
        Except.ok (assign.ff (nextVarId + j))) :
    evalFormula gconf assign eqf ms = Except.ok true := by
  cases htype : r.type with
  | ff =>
      simp only [mintFreshRetWithEq, htype] at h
      rw [hgv] at h
      cases sv with
      | array a => simp at h
      | simple sv0 =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          have heqf1 : eqf = FFFormula.eq (FFTerm.var nextVarId) (simpleSymValToTerm sv0) :=
            h.2.2.2.symm
          rw [heqf1]
          have hval0 := hrange 0 (by rw [htype]; simp [typeSize])
          simp only [symValueElems, List.getD_cons_zero] at hval0
          simp only [evalFormula, evalTerm, hval0, BEq.beq]
          simp
  | array n =>
      simp only [mintFreshRetWithEq, htype] at h
      rw [hgv] at h
      cases sv with
      | simple s => simp at h
      | array arr =>
          by_cases hsize : arr.size = n
          · simp only [hsize, BEq.rfl, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
            have heqf1 : eqf =
                ((arr.toList.zip ((List.range n).map (fun i => nextVarId + i))).map
                  (fun p => FFFormula.eq (FFTerm.var p.2) (simpleSymValToTerm p.1))).foldr
                  FFFormula.and FFFormula.true := h.2.2.2.symm
            have hlen : n = arr.toList.length := by rw [Array.length_toList]; exact hsize.symm
            rw [heqf1, hlen]
            apply eqs_sound gconf ms assign arr.toList nextVarId
            intro j hj
            have := hrange j (by rw [htype]; simp only [typeSize]; rwa [hlen])
            simpa [symValueElems] using this
          · simp [hsize] at h

/-- Converse of `mintFreshRetWithEq_eqf_sound`. -/
theorem mintFreshRetWithEq_eqf_complete {c : ZKConfig} (gconf : GlobalConfig c)
    (ms : List (FFMacro c)) (assign : Assignment c) (nextVarId : Nat) (bodySymEnv : SymEnv c)
    (r : Param) (nv1 : Nat) (vs : List Var) (sv' : SymValue c) (eqf : FFFormula c)
    (h : mintFreshRetWithEq (c := c) nextVarId bodySymEnv r = Except.ok (nv1, vs, sv', eqf))
    (sv : SymValue c) (hgv : getVar bodySymEnv r.name = Except.ok sv)
    (heval : evalFormula gconf assign eqf ms = Except.ok true) :
    ∀ j, j < typeSize r.type →
      evalTerm gconf assign (simpleSymValToTerm ((symValueElems sv).getD j default)) ms =
        Except.ok (assign.ff (nextVarId + j)) := by
  cases htype : r.type with
  | ff =>
      simp only [mintFreshRetWithEq, htype] at h
      rw [hgv] at h
      cases sv with
      | array a => simp at h
      | simple sv0 =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          have heqf1 : eqf = FFFormula.eq (FFTerm.var nextVarId) (simpleSymValToTerm sv0) :=
            h.2.2.2.symm
          rw [heqf1] at heval
          intro j hj
          simp only [typeSize] at hj
          interval_cases j
          simp only [symValueElems, List.getD_cons_zero, Nat.add_zero]
          simp only [evalFormula] at heval
          cases ht1 : evalTerm gconf assign (FFTerm.var nextVarId) ms with
          | error e => rw [ht1] at heval; simp at heval
          | ok ta =>
            rw [ht1] at heval
            cases ht2 : evalTerm gconf assign (simpleSymValToTerm sv0) ms with
            | error e => rw [ht2] at heval; simp at heval
            | ok tb =>
              rw [ht2] at heval
              simp only [Except.ok.injEq, beq_iff_eq] at heval
              have hta : assign.ff nextVarId = ta := by
                simp only [evalTerm] at ht1
                injection ht1
              exact congrArg Except.ok (hta.trans heval).symm
  | array n =>
      simp only [mintFreshRetWithEq, htype] at h
      rw [hgv] at h
      cases sv with
      | simple s => simp at h
      | array arr =>
          by_cases hsize : arr.size = n
          · simp only [hsize, BEq.rfl, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
            have heqf1 : eqf =
                ((arr.toList.zip ((List.range n).map (fun i => nextVarId + i))).map
                  (fun p => FFFormula.eq (FFTerm.var p.2) (simpleSymValToTerm p.1))).foldr
                  FFFormula.and FFFormula.true := h.2.2.2.symm
            have hlen : n = arr.toList.length := by rw [Array.length_toList]; exact hsize.symm
            rw [heqf1, hlen] at heval
            intro j hj
            simp only [typeSize, hlen] at hj
            have := eqs_complete gconf ms assign arr.toList nextVarId heval j hj
            simpa [symValueElems] using this
          · simp [hsize] at h

/-- Membership in a `foldl`-with-union accumulator splits into "already in the starting
    accumulator" or "in one of the list's own elements' contributions". -/
theorem mem_foldl_union_simpleValVars {c : ZKConfig} :
    ∀ (l : List (SimpleSymVal c)) (init : VarSet) (w : Var),
      w ∈ l.foldl (fun acc s => acc ∪ simpleValVars s) init ↔
        w ∈ init ∨ ∃ j, j < l.length ∧ w ∈ simpleValVars (l.getD j default) := by
  intro l
  induction l with
  | nil => intro init w; simp
  | cons s l ih =>
      intro init w
      simp only [List.foldl_cons]
      rw [ih (init ∪ simpleValVars s) w]
      constructor
      · rintro (h1 | ⟨j, hj, hw⟩)
        · rcases Std.TreeSet.mem_union_iff.mp h1 with h1' | h1'
          · exact Or.inl h1'
          · exact Or.inr ⟨0, by simp, by simpa using h1'⟩
        · exact Or.inr ⟨j + 1, by simp only [List.length_cons]; omega, by simpa using hw⟩
      · rintro (h1 | ⟨j, hj, hw⟩)
        · exact Or.inl (Std.TreeSet.mem_union_of_left h1)
        · cases j with
          | zero => exact Or.inl (Std.TreeSet.mem_union_of_right (by simpa using hw))
          | succ j' => exact Or.inr ⟨j', by simpa using hj, by simpa using hw⟩

/-- Specialization of `mem_foldl_union_simpleValVars` starting from `emptyVarSet`. -/
theorem mem_foldl_simpleValVars_union {c : ZKConfig} (l : List (SimpleSymVal c)) (w : Var)
    (hw : w ∈ l.foldl (fun acc s => acc ∪ simpleValVars s) emptyVarSet) :
    ∃ j, j < l.length ∧ w ∈ simpleValVars (l.getD j default) := by
  rcases (mem_foldl_union_simpleValVars l emptyVarSet w).mp hw with h | h
  · exact absurd h Std.TreeSet.not_mem_emptyc
  · exact h

/-- Every var mentioned by one of `sv`'s own flattened elements (`symValueElems`) is mentioned by
    `sv` as a whole (`symValVars`) -- connects `symValueElems`-indexed element reasoning back to
    plain `symValVars` membership. -/
theorem getD_pointwise_of_forall2 {α β : Type} (R : α → β → Prop) (da : α) (db : β) :
    ∀ (la : List α) (lb : List β), List.Forall₂ R la lb →
      ∀ i, i < la.length → R (la.getD i da) (lb.getD i db) := by
  intro la lb hforall
  induction hforall with
  | nil => intro i hi; simp at hi
  | cons hd tl ih =>
      intro i hi
      cases i with
      | zero => simpa using hd
      | succ i' => simpa using ih i' (by simpa using hi)

theorem mem_symValVars_of_mem_symValueElems {c : ZKConfig} (sv : SymValue c) (j : Nat)
    (hj : j < (symValueElems sv).length) :
    ∀ w ∈ simpleValVars ((symValueElems sv).getD j default), w ∈ symValVars sv := by
  cases sv with
  | simple s =>
      simp only [symValueElems, List.length_cons, List.length_nil] at hj
      have hj0 : j = 0 := by omega
      subst hj0
      simp only [symValueElems, List.getD_cons_zero, symValVars]
      exact fun w hw => hw
  | array arr =>
      intro w hw
      simp only [symValueElems] at hj hw
      simp only [symValVars]
      rw [← Array.foldl_toList, List.toList_toArray]
      exact (mem_foldl_union_simpleValVars arr.toList emptyVarSet w).mpr
        (Or.inr ⟨j, hj, hw⟩)

/-- Unpacks `symValMatches` into its own element-wise view via `symValueElems`/`flattenValueToFF`
    -- the shape (`.simple`/`.scalar` vs `.array`/`.array`) is forced to agree by `symValMatches`
    itself (its `False` cases rule out a mismatch), and `ensureCorrectType` pins the exact size. -/
theorem symValMatches_elems {c : ZKConfig} (assignment : Assignment c) (sv : SymValue c)
    (v : Value c) (type : VarType) (ht : ensureCorrectType v type = Except.ok ())
    (hm : symValMatches assignment sv v) :
    (symValueElems sv).length = typeSize type ∧
    ∀ j, j < typeSize type →
      simpleValMatches assignment ((symValueElems sv).getD j default)
        ((flattenValueToFF v).getD j 0) := by
  cases type with
  | ff =>
      cases v with
      | array _ => simp [ensureCorrectType] at ht
      | scalar vv =>
          cases sv with
          | array _ => simp [symValMatches] at hm
          | simple s =>
              simp only [symValMatches] at hm
              refine ⟨by simp [symValueElems, typeSize], ?_⟩
              intro j hj
              simp only [typeSize] at hj
              have hj0 : j = 0 := by omega
              subst hj0
              simp only [symValueElems, List.getD_cons_zero, flattenValueToFF]
              simpa using hm
  | array n =>
      cases v with
      | scalar _ => simp [ensureCorrectType] at ht
      | array varr =>
          cases sv with
          | simple _ => simp [symValMatches] at hm
          | array arr =>
              simp only [ensureCorrectType] at ht
              have hsize : varr.size = n := by
                by_contra hcon
                simp [hcon] at ht
              simp only [symValMatches] at hm
              have hlen : arr.toList.length = varr.toList.length := hm.length_eq
              have hlen' : arr.size = n := by
                rw [← Array.length_toList, hlen, Array.length_toList, hsize]
              refine ⟨?_, ?_⟩
              · simp only [symValueElems, typeSize]
                rw [Array.length_toList, hlen']
              · intro j hj
                simp only [typeSize] at hj
                simp only [symValueElems, flattenValueToFF]
                apply getD_pointwise_of_forall2 (simpleValMatches assignment) default 0
                  arr.toList varr.toList hm
                rw [Array.length_toList, hlen']
                exact hj

/-- Converse of `symValVars_freshRetSymValue_below` (`FuncCallCorrectness.lean`): every var in the
    block `[start, start + typeSize type)` is actually mentioned by `freshRetSymValue start type`.
    Needed to show a flattened param/ret position lands in `symEnvVars`, without having to first
    identify which specific param/ret it belongs to. -/
theorem mem_symValVars_freshRetSymValue {c : ZKConfig} (start : Nat) (type : VarType) :
    ∀ n, start ≤ n → n < start + typeSize type →
      Var.ffv n ∈ symValVars (freshRetSymValue (c := c) start type) := by
  intro n hle hlt
  cases type with
  | ff =>
      simp only [typeSize] at hlt
      have hn : n = start := by omega
      subst hn
      simp only [freshRetSymValue, symValVars, simpleValVars]
      exact Std.TreeSet.mem_insert_self ..
  | array size =>
      simp only [typeSize] at hlt
      simp only [freshRetSymValue, symValVars]
      rw [← Array.foldl_toList, List.toList_toArray]
      have hi : n - start < size := by omega
      apply (mem_foldl_union_simpleValVars _ emptyVarSet (Var.ffv n)).mpr
      refine Or.inr ⟨n - start, by simpa using hi, ?_⟩
      rw [range_map_getD size (fun i => SimpleSymVal.ffvar
        ({ var := start + i, bits := none } : FFVarWithBinRep c)) (n - start) hi default]
      have hn : start + (n - start) = n := by omega
      simp only [simpleValVars, hn]
      exact Std.TreeSet.mem_insert_self ..

/-- Every flattened position `nextVarId + k` in the block `mintFreshParams` mints for `params`
    (`k < totalParamSize params`) ends up in the resulting environment's var set -- the
    array-general replacement for the old FF-only "each param has its own single fresh var"
    reasoning (`mintFreshParams_paramVars_getVar` + `getVar_mem_symEnvVars`), needed since here a
    position doesn't have to be identified with a *specific* param to land in `symEnvVars`. -/
theorem mintFreshParams_block_mem_symEnvVars {c : ZKConfig} :
    ∀ (nextVarId : Nat) (params : List Param) (symEnv : SymEnv c),
      (params.map (·.name)).Nodup →
      ∀ (nv1 : Nat) (paramVars : List Var) (symEnv' : SymEnv c),
        mintFreshParams (c := c) nextVarId params symEnv = Except.ok (nv1, paramVars, symEnv') →
        ∀ k, k < totalParamSize params → Var.ffv (nextVarId + k) ∈ symEnvVars symEnv' := by
  intro nextVarId params
  induction params generalizing nextVarId with
  | nil => intro symEnv _hnodup nv1 paramVars symEnv' _h k hk; simp [totalParamSize] at hk
  | cons p ps ih =>
      intro symEnv hnodup nv1 paramVars symEnv' h k hk
      simp only [mintFreshParams] at h
      cases hmp : mintFreshParam (c := c) nextVarId p.type with
      | error e => simp [hmp] at h
      | ok result =>
          obtain ⟨nv2, vs, sv⟩ := result
          simp only [hmp] at h
          cases hrest : mintFreshParams (c := c) nv2 ps
              (Corellzk2smt.SymExec.Basic.setVar symEnv p.name sv) with
          | error e => simp [hrest] at h
          | ok result2 =>
              obtain ⟨nv3, vs2, symEnv2⟩ := result2
              simp only [hrest, Except.ok.injEq, Prod.mk.injEq] at h
              have hnv2_eq : nv2 = nextVarId + typeSize p.type :=
                (mintFreshParam_eq nextVarId p.type nv2 vs sv hmp).2
              have hnotmem : p.name ∉ ps.map (·.name) := (List.nodup_cons.mp hnodup).1
              rw [totalParamSize_cons] at hk
              have hps : paramSize p = typeSize p.type := rfl
              rcases Nat.lt_or_ge k (typeSize p.type) with hklt | hkge
              · have hsv_eq : sv = freshRetSymValue nextVarId p.type :=
                  mintFreshParam_symValue_eq_freshRetSymValue nextVarId p.type nv2 vs sv hmp
                have hmemv : Var.ffv (nextVarId + k) ∈ symValVars sv := by
                  rw [hsv_eq]
                  exact mem_symValVars_freshRetSymValue nextVarId p.type (nextVarId + k)
                    (by omega) (by omega)
                have hget : (Corellzk2smt.SymExec.Basic.setVar symEnv p.name sv).get? p.name =
                    some sv := by
                  simp only [Corellzk2smt.SymExec.Basic.setVar, Std.TreeMap.get?_eq_getElem?,
                    Std.TreeMap.getElem?_insert_self]
                have hget2 : symEnv2.get? p.name = some sv :=
                  mintFreshParams_preserves_getVar nv2 ps
                    (Corellzk2smt.SymExec.Basic.setVar symEnv p.name sv) p.name sv
                    hnotmem hget nv3 vs2 symEnv2 hrest
                have hsub := getVar_mem_symEnvVars symEnv2 p.name sv hget2
                rw [← h.2.2]
                exact hsub (Var.ffv (nextVarId + k)) hmemv
              · have hind := ih nv2 (Corellzk2smt.SymExec.Basic.setVar symEnv p.name sv)
                  ((List.nodup_cons.mp hnodup).2) nv3 vs2 symEnv2 hrest
                  (k - typeSize p.type) (by omega)
                have hnat : nextVarId + k = nv2 + (k - typeSize p.type) := by omega
                rw [← h.2.2, hnat]
                exact hind

/-- Vars-membership companion to `mintFreshRetWithEq_eqf_sound`/`_complete`: every var mentioned
    by `sv`'s own denoted value is captured by `eqf`'s own var-set. -/
theorem mintFreshRetWithEq_eqf_vars_sub {c : ZKConfig} (nextVarId : Nat) (bodySymEnv : SymEnv c)
    (r : Param) (nv1 : Nat) (vs : List Var) (sv' : SymValue c) (eqf : FFFormula c)
    (h : mintFreshRetWithEq (c := c) nextVarId bodySymEnv r = Except.ok (nv1, vs, sv', eqf))
    (sv : SymValue c) (hgv : getVar bodySymEnv r.name = Except.ok sv) :
    ∀ w ∈ symValVars sv, w ∈ ffVarsOfFormula eqf ∪ bVarsOfFormula eqf := by
  cases htype : r.type with
  | ff =>
      simp only [mintFreshRetWithEq, htype] at h
      rw [hgv] at h
      cases sv with
      | array a => simp at h
      | simple sv0 =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          have heqf1 : eqf = FFFormula.eq (FFTerm.var nextVarId) (simpleSymValToTerm sv0) :=
            h.2.2.2.symm
          rw [heqf1]
          intro w hw
          simp only [symValVars] at hw
          simp only [ffVarsOfFormula, bVarsOfFormula, ffVarsOfTerm, ffVarsOfTerm_simpleSymValToTerm,
            bVarsOfTerm, bVarsOfTerm_simpleSymValToTerm]
          exact Std.TreeSet.mem_union_of_left (Std.TreeSet.mem_union_of_right hw)
  | array n =>
      simp only [mintFreshRetWithEq, htype] at h
      rw [hgv] at h
      cases sv with
      | simple s => simp at h
      | array arr =>
          by_cases hsize : arr.size = n
          · simp only [hsize, BEq.rfl, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
            have heqf1 : eqf =
                ((arr.toList.zip ((List.range n).map (fun i => nextVarId + i))).map
                  (fun p => FFFormula.eq (FFTerm.var p.2) (simpleSymValToTerm p.1))).foldr
                  FFFormula.and FFFormula.true := h.2.2.2.symm
            have hlen : n = arr.toList.length := by rw [Array.length_toList]; exact hsize.symm
            rw [heqf1, hlen]
            intro w hw
            simp only [symValVars] at hw
            rw [← Array.foldl_toList, List.toList_toArray] at hw
            obtain ⟨j, hj, hw'⟩ := mem_foldl_simpleValVars_union arr.toList w hw
            exact eqs_vars_mem arr.toList nextVarId j hj w hw'
          · simp [hsize] at h


/-- A concrete `Value` is determined by its shape (via `ensureCorrectType`) plus its own flattened
    `FF` elements -- the "reconstruct from elements" direction needed to identify a symbolically
    matched value once its flattened elements are pinned down elementwise. -/
theorem value_eq_of_flatten_eq {c : ZKConfig} (v1 v2 : Value c) (type : VarType)
    (h1 : ensureCorrectType v1 type = Except.ok ())
    (h2 : ensureCorrectType v2 type = Except.ok ())
    (heq : ∀ j, j < typeSize type →
      (flattenValueToFF v1).getD j 0 = (flattenValueToFF v2).getD j 0) :
    v1 = v2 := by
  cases type with
  | ff =>
      cases v1 with
      | array _ => simp [ensureCorrectType] at h1
      | scalar x1 =>
          cases v2 with
          | array _ => simp [ensureCorrectType] at h2
          | scalar x2 =>
              have h0 := heq 0 (by simp [typeSize])
              simp only [flattenValueToFF, List.getD_cons_zero] at h0
              rw [h0]
  | array n =>
      cases v1 with
      | scalar _ => simp [ensureCorrectType] at h1
      | array arr1 =>
          cases v2 with
          | scalar _ => simp [ensureCorrectType] at h2
          | array arr2 =>
              have hsize1 : arr1.size = n := by
                by_contra hc; simp [ensureCorrectType, hc] at h1
              have hsize2 : arr2.size = n := by
                by_contra hc; simp [ensureCorrectType, hc] at h2
              have : arr1 = arr2 := by
                apply Array.ext (hsize1.trans hsize2.symm)
                intro i hi1 hi2
                have hj : i < typeSize (VarType.array n) := by
                  simp only [typeSize]; omega
                have hi' := heq i hj
                simp only [flattenValueToFF] at hi'
                rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
                  List.getElem?_eq_getElem (by rw [Array.length_toList]; omega),
                  List.getElem?_eq_getElem (by rw [Array.length_toList]; omega),
                  Option.getD_some, Option.getD_some, Array.getElem_toList,
                  Array.getElem_toList] at hi'
                exact hi'
              rw [this]

/-- Given `mintFreshRetsWithEq`'s success (which pins each ret's own `sv` to the shape its
    declared type demands, per `mintFreshRetsWithEq_getVar_elemsLen`'s doc comment) and
    `symValMatches assignment sv v` for some concrete `v`, `v` itself has to have the matching
    shape too -- `symValMatches`'s own `.simple`/`.array` cases force `v`'s constructor to agree
    with `sv`'s, and `sv`'s constructor is forced by `mintFreshRetWithEq`'s construction to agree
    with the declared type. -/
theorem ensureCorrectType_of_mintFreshRetsWithEq_getVar {c : ZKConfig}
    (assignment : Assignment c) :
    ∀ (nextVarId : Nat) (bodySymEnv : SymEnv c) (rets : List Param)
      (nv2 : Nat) (retVars : List Var) (retBinds : List (VarID × SymValue c))
      (retEqFormula : FFFormula c),
      mintFreshRetsWithEq (c := c) nextVarId bodySymEnv rets =
        Except.ok (nv2, retVars, retBinds, retEqFormula) →
      ∀ i, (hi : i < rets.length) → ∀ sv v,
        getVar bodySymEnv (rets.getD i default).name = Except.ok sv →
        symValMatches assignment sv v →
        ensureCorrectType v (rets.getD i default).type = Except.ok () := by
  intro nextVarId bodySymEnv rets
  induction rets generalizing nextVarId with
  | nil => intro nv2 retVars retBinds retEqFormula _h i hi; simp at hi
  | cons r rs ih =>
      intro nv2 retVars retBinds retEqFormula h i hi
      simp only [mintFreshRetsWithEq] at h
      cases hmr : mintFreshRetWithEq (c := c) nextVarId bodySymEnv r with
      | error e => simp [hmr] at h
      | ok result =>
          obtain ⟨nv1, vsv, sv0, eqf⟩ := result
          simp only [hmr] at h
          cases hrest : mintFreshRetsWithEq (c := c) nv1 bodySymEnv rs with
          | error e => simp [hrest] at h
          | ok result2 =>
              obtain ⟨nv3, vs2, binds2, restf2⟩ := result2
              cases i with
              | zero =>
                  intro sv v hgv hm
                  simp only [List.getD_cons_zero] at hgv ⊢
                  cases htype : r.type with
                  | ff =>
                      simp only [mintFreshRetWithEq, htype] at hmr
                      cases hgv2 : getVar bodySymEnv r.name with
                      | error e => simp [hgv2] at hmr
                      | ok result3 =>
                          cases result3 with
                          | array arr => simp [hgv2] at hmr
                          | simple sv1 =>
                              rw [hgv2] at hgv
                              injection hgv with hgv
                              subst hgv
                              cases v with
                              | array _ => simp [symValMatches] at hm
                              | scalar _ => simp [ensureCorrectType]
                  | array n =>
                      simp only [mintFreshRetWithEq, htype] at hmr
                      cases hgv2 : getVar bodySymEnv r.name with
                      | error e => simp [hgv2] at hmr
                      | ok result3 =>
                          cases result3 with
                          | simple sv1 => simp [hgv2] at hmr
                          | array arr =>
                              by_cases hsize : arr.size == n
                              · rw [hgv2] at hgv
                                injection hgv with hgv
                                subst hgv
                                cases v with
                                | scalar _ => simp [symValMatches] at hm
                                | array varr =>
                                    simp only [symValMatches] at hm
                                    have hlen : arr.toList.length = varr.toList.length :=
                                      hm.length_eq
                                    have hasize : arr.size = n := by simpa using hsize
                                    simp only [ensureCorrectType]
                                    rw [if_pos]
                                    rw [← Array.length_toList, ← hlen, Array.length_toList, hasize]
                              · simp [hgv2, hsize] at hmr
              | succ i' =>
                  intro sv v hgv hm
                  simp only [List.getD_cons_succ] at hgv ⊢
                  exact ih nv1 nv3 vs2 binds2 restf2 hrest i' (by simpa using hi) sv v hgv hm

/-- `mintFreshRetsWithEq` only ever succeeds when `getVar` succeeds at every ret's own name
    (whatever shape it holds) -- array-general version of `mintFreshRetsWithEq_getVar_exists`,
    dropping both the FF-only hypothesis and the `.simple`-only conclusion. -/
theorem mintFreshRetsWithEq_getVar_exists_general {c : ZKConfig} :
    ∀ (nextVarId : Nat) (bodySymEnv : SymEnv c) (rets : List Param)
      (nv2 : Nat) (retVars : List Var) (retBinds : List (VarID × SymValue c))
      (retEqFormula : FFFormula c),
      mintFreshRetsWithEq (c := c) nextVarId bodySymEnv rets =
        Except.ok (nv2, retVars, retBinds, retEqFormula) →
      ∀ i, (hi : i < rets.length) →
        ∃ sv, getVar bodySymEnv (rets.getD i default).name = Except.ok sv := by
  intro nextVarId bodySymEnv rets
  induction rets generalizing nextVarId with
  | nil => intro nv2 retVars retBinds retEqFormula _h i hi; simp at hi
  | cons r rs ih =>
      intro nv2 retVars retBinds retEqFormula h i hi
      simp only [mintFreshRetsWithEq] at h
      cases hmr : mintFreshRetWithEq (c := c) nextVarId bodySymEnv r with
      | error e => simp [hmr] at h
      | ok result =>
          obtain ⟨nv1, _v, sv0', eqf⟩ := result
          simp only [hmr] at h
          cases hrest : mintFreshRetsWithEq (c := c) nv1 bodySymEnv rs with
          | error e => simp [hrest] at h
          | ok result2 =>
              obtain ⟨nv3, vs2, binds2, restf2⟩ := result2
              cases i with
              | zero =>
                  simp only [List.getD_cons_zero]
                  cases htype : r.type with
                  | ff =>
                      simp only [mintFreshRetWithEq, htype] at hmr
                      cases hg : getVar bodySymEnv r.name with
                      | error e => simp [hg] at hmr
                      | ok res => exact ⟨res, rfl⟩
                  | array n =>
                      simp only [mintFreshRetWithEq, htype] at hmr
                      cases hg : getVar bodySymEnv r.name with
                      | error e => simp [hg] at hmr
                      | ok res => exact ⟨res, rfl⟩
              | succ i' =>
                  simp only [List.getD_cons_succ]
                  exact ih nv1 nv3 vs2 binds2 restf2 hrest i' (by simpa using hi)

/-- Array-general version of `retEqFormula_sound`. -/
theorem retEqFormula_sound_general {c : ZKConfig} (gconf : GlobalConfig c) (ms : List (FFMacro c))
    (assign : Assignment c) :
    ∀ (nextVarId : Nat) (bodySymEnv : SymEnv c) (rets : List Param)
      (nv2 : Nat) (retVars : List Var) (retBinds : List (VarID × SymValue c))
      (retEqFormula : FFFormula c),
      mintFreshRetsWithEq (c := c) nextVarId bodySymEnv rets =
        Except.ok (nv2, retVars, retBinds, retEqFormula) →
      (∀ i, (hi : i < rets.length) → ∀ sv,
        getVar bodySymEnv (rets.getD i default).name = Except.ok sv →
        ∀ j, j < typeSize (rets.getD i default).type →
          evalTerm gconf assign
            (simpleSymValToTerm ((symValueElems sv).getD j default)) ms =
            Except.ok (assign.ff (nextVarId + totalParamSize (rets.take i) + j))) →
      evalFormula gconf assign retEqFormula ms = Except.ok true := by
  intro nextVarId bodySymEnv rets
  induction rets generalizing nextVarId with
  | nil =>
      intro nv2 retVars retBinds retEqFormula h _hvals
      simp only [mintFreshRetsWithEq, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.2.2.2]
      simp [evalFormula]
  | cons r rs ih =>
      intro nv2 retVars retBinds retEqFormula h hvals
      obtain ⟨sv, hgv⟩ := mintFreshRetsWithEq_getVar_exists_general nextVarId bodySymEnv
        (r :: rs) nv2 retVars retBinds retEqFormula h 0 (by simp)
      simp only [List.getD_cons_zero] at hgv
      simp only [mintFreshRetsWithEq] at h
      cases hmr : mintFreshRetWithEq (c := c) nextVarId bodySymEnv r with
      | error e => simp [hmr] at h
      | ok result =>
          obtain ⟨nv1, _v, sv0, eqf⟩ := result
          simp only [hmr] at h
          cases hrest : mintFreshRetsWithEq (c := c) nv1 bodySymEnv rs with
          | error e => simp [hrest] at h
          | ok result2 =>
              obtain ⟨nv3, vs2, binds2, restf2⟩ := result2
              simp only [hrest, Except.ok.injEq, Prod.mk.injEq] at h
              have hnv1_eq : nv1 = nextVarId + paramSize r :=
                (mintFreshRetWithEq_eq nextVarId bodySymEnv r nv1 _v sv0 eqf hmr).2
              have heqf_eval : evalFormula gconf assign eqf ms = Except.ok true := by
                apply mintFreshRetWithEq_eqf_sound gconf ms assign nextVarId bodySymEnv r nv1 _v sv0
                  eqf hmr sv hgv
                intro j hj
                have h0 := hvals 0 (by simp) sv hgv j (by simpa using hj)
                simpa using h0
              have hvals_rs : ∀ i, i < rs.length → ∀ sv', getVar bodySymEnv
                    (rs.getD i default).name = Except.ok sv' →
                  ∀ j, j < typeSize (rs.getD i default).type →
                    evalTerm gconf assign
                      (simpleSymValToTerm ((symValueElems sv').getD j default)) ms =
                      Except.ok (assign.ff (nv1 + totalParamSize (rs.take i) + j)) := by
                intro i hi sv' hgv' j hj
                have h1 := hvals (i + 1) (by simp only [List.length_cons]; omega) sv'
                  (by simpa using hgv') j (by simpa using hj)
                have hps : paramSize r = typeSize r.type := rfl
                have heq : nextVarId + totalParamSize ((r :: rs).take (i + 1)) =
                    nv1 + totalParamSize (rs.take i) := by
                  rw [List.take_succ_cons, totalParamSize_cons, hnv1_eq]
                  omega
                rw [heq] at h1
                simpa using h1
              have hih : evalFormula gconf assign restf2 ms = Except.ok true :=
                ih nv1 nv3 vs2 binds2 restf2 hrest hvals_rs
              rw [← h.2.2.2]
              simp [evalFormula, heqf_eval, hih]

/-- Array-general version of `retEqFormula_complete`: converse of `retEqFormula_sound_general`. -/
theorem retEqFormula_complete_general {c : ZKConfig} (gconf : GlobalConfig c)
    (ms : List (FFMacro c)) (assign : Assignment c) :
    ∀ (nextVarId : Nat) (bodySymEnv : SymEnv c) (rets : List Param)
      (nv2 : Nat) (retVars : List Var) (retBinds : List (VarID × SymValue c))
      (retEqFormula : FFFormula c),
      mintFreshRetsWithEq (c := c) nextVarId bodySymEnv rets =
        Except.ok (nv2, retVars, retBinds, retEqFormula) →
      evalFormula gconf assign retEqFormula ms = Except.ok true →
      ∀ i, (hi : i < rets.length) → ∀ sv,
        getVar bodySymEnv (rets.getD i default).name = Except.ok sv →
        ∀ j, j < typeSize (rets.getD i default).type →
          evalTerm gconf assign
            (simpleSymValToTerm ((symValueElems sv).getD j default)) ms =
            Except.ok (assign.ff (nextVarId + totalParamSize (rets.take i) + j)) := by
  intro nextVarId bodySymEnv rets
  induction rets generalizing nextVarId with
  | nil => intro nv2 retVars retBinds retEqFormula _h _heval i hi; simp at hi
  | cons r rs ih =>
      intro nv2 retVars retBinds retEqFormula h heval i hi sv hgv j hj
      simp only [mintFreshRetsWithEq] at h
      cases hmr : mintFreshRetWithEq (c := c) nextVarId bodySymEnv r with
      | error e => simp [hmr] at h
      | ok result =>
          obtain ⟨nv1, _v, sv0, eqf⟩ := result
          simp only [hmr] at h
          cases hrest : mintFreshRetsWithEq (c := c) nv1 bodySymEnv rs with
          | error e => simp [hrest] at h
          | ok result2 =>
              obtain ⟨nv3, vs2, binds2, restf2⟩ := result2
              simp only [hrest, Except.ok.injEq, Prod.mk.injEq] at h
              have hnv1_eq : nv1 = nextVarId + paramSize r :=
                (mintFreshRetWithEq_eq nextVarId bodySymEnv r nv1 _v sv0 eqf hmr).2
              rw [← h.2.2.2] at heval
              simp only [evalFormula] at heval
              cases heq1 : evalFormula gconf assign eqf ms with
              | error e => rw [heq1] at heval; simp at heval
              | ok b1 =>
                rw [heq1] at heval
                cases heq2 : evalFormula gconf assign restf2 ms with
                | error e => rw [heq2] at heval; simp at heval
                | ok b2 =>
                  rw [heq2] at heval
                  simp only [Except.ok.injEq] at heval
                  have hb1 : b1 = true := by by_contra hcon; simp [hcon] at heval
                  have hb2 : b2 = true := by by_contra hcon; simp [hcon] at heval
                  cases i with
                  | zero =>
                      simp only [List.getD_cons_zero] at hgv hj
                      simp only [List.take_zero, totalParamSize_nil, Nat.add_zero]
                      have heval1 : evalFormula gconf assign eqf ms = Except.ok true :=
                        heq1.trans (congrArg Except.ok hb1)
                      exact mintFreshRetWithEq_eqf_complete gconf ms assign nextVarId bodySymEnv r
                        nv1 _v sv0 eqf hmr sv hgv heval1 j hj
                  | succ i' =>
                      simp only [List.getD_cons_succ] at hgv hj
                      have heval2 : evalFormula gconf assign restf2 ms = Except.ok true :=
                        heq2.trans (congrArg Except.ok hb2)
                      have hind := ih nv1 nv3 vs2 binds2 restf2 hrest heval2 i'
                        (by simpa using hi) sv hgv j hj
                      have heq : nextVarId + totalParamSize ((r :: rs).take (i' + 1)) =
                          nv1 + totalParamSize (rs.take i') := by
                        rw [List.take_succ_cons, totalParamSize_cons, hnv1_eq]
                        have hps : paramSize r = typeSize r.type := rfl
                        omega
                      rw [← heq] at hind
                      exact hind

/-- Array-general version of `mintFreshRetsWithEq_sv_vars_sub`. -/
theorem mintFreshRetsWithEq_sv_vars_sub_general {c : ZKConfig} :
    ∀ (nextVarId : Nat) (bodySymEnv : SymEnv c) (rets : List Param)
      (nv2 : Nat) (retVars : List Var) (retBinds : List (VarID × SymValue c))
      (retEqFormula : FFFormula c),
      mintFreshRetsWithEq (c := c) nextVarId bodySymEnv rets =
        Except.ok (nv2, retVars, retBinds, retEqFormula) →
      ∀ i, (hi : i < rets.length) → ∀ sv,
        getVar bodySymEnv (rets.getD i default).name = Except.ok sv →
        ∀ w ∈ symValVars sv, w ∈ ffVarsOfFormula retEqFormula ∪ bVarsOfFormula retEqFormula := by
  intro nextVarId bodySymEnv rets
  induction rets generalizing nextVarId with
  | nil => intro nv2 retVars retBinds retEqFormula _h i hi; simp at hi
  | cons r rs ih =>
      intro nv2 retVars retBinds retEqFormula h i hi sv hgv w hw
      simp only [mintFreshRetsWithEq] at h
      cases hmr : mintFreshRetWithEq (c := c) nextVarId bodySymEnv r with
      | error e => simp [hmr] at h
      | ok result =>
          obtain ⟨nv1, _v, sv0, eqf⟩ := result
          simp only [hmr] at h
          cases hrest : mintFreshRetsWithEq (c := c) nv1 bodySymEnv rs with
          | error e => simp [hrest] at h
          | ok result2 =>
              obtain ⟨nv3, vs2, binds2, restf2⟩ := result2
              simp only [hrest, Except.ok.injEq, Prod.mk.injEq] at h
              rw [← h.2.2.2]
              simp only [ffVarsOfFormula, bVarsOfFormula]
              cases i with
              | zero =>
                  simp only [List.getD_cons_zero] at hgv
                  have hind := mintFreshRetWithEq_eqf_vars_sub nextVarId bodySymEnv r nv1 _v sv0
                    eqf hmr sv hgv w hw
                  rcases Std.TreeSet.mem_union_iff.mp hind with hind' | hind'
                  · exact Std.TreeSet.mem_union_of_left (Std.TreeSet.mem_union_of_left hind')
                  · exact Std.TreeSet.mem_union_of_right (Std.TreeSet.mem_union_of_left hind')
              | succ i' =>
                  simp only [List.getD_cons_succ] at hgv
                  have hind := ih nv1 nv3 vs2 binds2 restf2 hrest i' (by simpa using hi) sv hgv w hw
                  rcases Std.TreeSet.mem_union_iff.mp hind with hind' | hind'
                  · exact Std.TreeSet.mem_union_of_left (Std.TreeSet.mem_union_of_right hind')
                  · exact Std.TreeSet.mem_union_of_right (Std.TreeSet.mem_union_of_right hind')

/-- Array-general version of `getOutParamsValues_construct`: converse of `getOutParamsValues_shape`
    -- given `retVals` matches `rets`'s shape and `env` already holds exactly `retVals`'s values at
    each ret's name, `getOutParamsValues` succeeds with exactly `retVals`. -/
theorem getOutParamsValues_construct_general {c : ZKConfig} :
    ∀ (env : Env c) (rets : List Param) (retVals : List (Value c)),
      ValuesMatchParams retVals rets →
      (∀ j, (hj : j < rets.length) → env.get? (rets.getD j default).name =
        some (retVals.getD j default)) →
      getOutParamsValues env rets = Except.ok retVals := by
  intro env rets
  induction rets with
  | nil =>
      intro retVals hmatch _hvals
      cases hmatch
      rfl
  | cons r rs ih =>
      intro retVals hmatch hvals
      cases hmatch with
      | cons hd tl =>
          rename_i rv retVals'
          have hv0 := hvals 0 (by simp)
          simp only [List.getD_cons_zero] at hv0
          have hg : getVar env r.name = Except.ok rv := by
            simp only [Corellzk2smt.Language.Core.Semantics.Basic.getVar, hv0]
          have hih := ih retVals' tl
            (fun j hj => by
              have := hvals (j + 1) (by simpa using hj)
              simpa using this)
          simp only [getOutParamsValues, hg, hd, hih]


/-- `fetchFunc`'s success at key `fname` only ever happens at the function whose *own* name
    equals `fname` (mirrors `fetchLT`'s own case-split, extracting the equality instead of the
    length bound). -/
theorem fetchFunc_name_eq {c : ZKConfig} :
    ∀ (p : Prog c) (fname : FName) (md : FuncMD) (name : FName) (params rets : List Param)
      (body : List (ComWithMD c)) (p' : Prog c),
      fetchFunc p fname = Except.ok (FuncWithMD.mk md (Func.mk name params rets body), p') →
      name = fname := by
  intro p
  induction p with
  | nil => intro fname md name params rets body p' h; simp [fetchFunc] at h
  | cons funcWMD fs ih =>
      intro fname md name params rets body p' h
      cases funcWMD with
      | mk md' f =>
          cases f with
          | mk name' params' rets' body' =>
              simp only [fetchFunc] at h
              by_cases hname : name' = fname
              · simp only [hname, BEq.rfl, ↓reduceIte] at h
                injection h with h_inner
                injection h_inner with h_fwmd _
                injection h_fwmd with _ h_f
                injection h_f with h_name _ _ _
                exact h_name.symm
              · simp only [hname, beq_iff_eq, ↓reduceIte] at h
                exact ih fname md name params rets body p' h

/-- Everything `seFunc`'s successful output can tell us purely from unfolding its own
    definition (no correctness content, just record-field/case-split bookkeeping): the produced
    spec's `name`/`params`/`rets` fields are exactly the source function's. (`seFunc` is now
    array-capable via `mintFreshParams`/`mintFreshRetsWithEq`, so an all-`.ff` conclusion is no
    longer derivable here -- callers needing that must supply it separately, as
    `seFuncCall_correct_via_seFunc` does via its own `hff_params`/`hff_rets` hypotheses.)
    Mirrors the opening lines of `seFunc_correct`'s own proof, factored out since
    `seFuncCall_correct_via_seFunc` needs it without the rest of that theorem's conclusion. -/
theorem seFunc_eq_shape {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (name : FName) (params rets : List Param) (body : List (ComWithMD c)) (fspec : FuncSpec c)
    (h : seFunc gconf specs (Func.mk name params rets body) = Except.ok fspec) :
    fspec.name = name ∧ fspec.params = params ∧ fspec.rets = rets := by
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
                exact ⟨rfl, rfl, rfl⟩

/-- Exposes `seFunc`'s macro's own `params : List Var` field (`paramVars ++ retVars ++
    auxVarsList` internally) in a form usable from *outside* `seFunc_correct`'s proof: the params
    segment is exactly the contiguous range `[0, totalParamSize params)`, the rets segment is
    some *other* contiguous range starting at an (unexposed, existentially-hidden) offset, and
    everything else is an opaque `auxVarsList` whose ff/bool split matches `numAuxFFVars`/
    `numAuxBoolVars`. Needed to decode an arbitrary `Assignment` back into `argVals`/`retVals`/
    `auxFF`/`auxBool` at the whole-program level (`Correctness/ProgCorrectness.lean`),
    without needing to inspect `seFunc_correct`'s ~900-line proof directly. -/
theorem seFunc_f_params_split_basic {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (name : FName) (params rets : List Param) (body : List (ComWithMD c)) (fspec : FuncSpec c)
    (h : seFunc gconf specs (Func.mk name params rets body) = Except.ok fspec) :
    ∃ (retsOffset : Nat) (auxVarsList : List Var),
      fspec.f.params =
        (List.range (totalParamSize params)).map (fun i => Var.ffv i) ++
        (List.range (totalParamSize rets)).map (fun i => Var.ffv (retsOffset + i)) ++
        auxVarsList ∧
      (auxVarsList.filter isFFvVar).length = fspec.numAuxFFVars ∧
      (auxVarsList.filter (fun v => !isFFvVar v)).length = fspec.numAuxBoolVars ∧
      auxVarsList.Pairwise (fun a b => compare a b = .lt) := by
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
                set auxVarsList : List Var :=
                  ((ffVarsOfFormula bodySpec.f ∪ bVarsOfFormula bodySpec.f ∪
                      ffVarsOfFormula retEqFormula ∪ bVarsOfFormula retEqFormula) \
                    (paramVars.foldl (fun acc v => acc.insert v) emptyVarSet ∪
                      retVars.foldl (fun acc v => acc.insert v) emptyVarSet)).toList
                  with hAuxVarsList_def
                refine ⟨bodySpec.nextVarId, auxVarsList, ?_, rfl, ?_, ?_⟩
                · have hpv := (mintFreshParams_paramVars_eq 0 params _ nv1 paramVars inSymEnv
                    hmp).1
                  have hrv := (mintFreshRetsWithEq_retVars_eq bodySpec.nextVarId
                    bodySpec.outSymEnv rets nv2 retVars retBinds retEqFormula hmr).1
                  simp only [hpv, hrv, Nat.zero_add]
                · show (auxVarsList.filter (fun v => !isFFvVar v)).length =
                    auxVarsList.length - (auxVarsList.filter isFFvVar).length
                  have := length_filter_add_length_filter_not isFFvVar auxVarsList
                  omega
                · rw [hAuxVarsList_def]
                  exact varSet_toList_pairwise_lt _




-- ---------------------------------------------------------------------------
-- seFunc_correct / seFuncCall_correct_via_seFunc
-- ---------------------------------------------------------------------------

/-- Exposes `seFunc`'s macro's own `params : List Var` field
    (`paramVars ++ retVars ++ auxVarsList` internally) *plus* the two disjointness facts needed to
    build a witness assignment for `seExecProg_call_complete`: the params/rets ranges don't
    overlap (`totalParamSize params ≤ retsOffset`), and every aux variable's own index avoids
    both ranges. This is a *different* theorem from `seFunc_f_params_split_basic` (this file) --
    that one is a pure `seFunc`-unfold needing no correctness hypotheses, and gives everything
    *except* the disjointness facts, since those genuinely need `seCmds_correct`'s own `hbs_mono`
    (`nextVarId` only ever grows) to rule out the params/rets ranges overlapping -- a fact
    `seFunc`'s bare definition doesn't encode syntactically. -/
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
                { nextVarId := nv1 } body inSymEnv hinSymEnv_below
                hbody_pre bodySpec hbs
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
                { nextVarId := nv1 } body inSymEnv hinSymEnv_below
                hbody_pre bodySpec hbs
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
                  specs hspecs_wf hspecs_cover body bodySpec hbs,
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
        hspecs_rets_cover hspecs_wf fspec hseFunc_eq
      exact seFuncCall_correct gconf p (fspec :: specs) sconf fname args outs fspec hspec_eq
        hspec_retsShape H_specCorrect

end Corellzk2smt.SymExec.Correctness.FuncCorrectness
