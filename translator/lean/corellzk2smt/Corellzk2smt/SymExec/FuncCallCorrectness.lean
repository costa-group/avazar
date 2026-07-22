import Corellzk2smt.SymExec.Correctness

/- Shared machinery for `seFuncCall` correctness (array-general -- callee params/rets may be
   `.array`-typed, flattened via `flattenArgVals`/`flattenSymValuesParams`): the
   `constifyMacroCallParam`/`mintFreshRets`/`mintFreshAuxParams` families and their many
   supporting lemmas. None of this is stated in terms of `TranslatesCorrectly` itself, so it's
   reused unchanged by both the (now-removed) unconditional formalization and the current
   conditional one in `SymExec/PartialCorrectness/FuncCallCorrectness.lean` -- see that file's
   header for the actual `seFuncCall_correct` theorem (still needs a `H_specCorrect` hypothesis,
   a stand-in for what `seFunc`'s own correctness theorem discharges for real) built on top of
   this. -/

namespace Corellzk2smt.SymExec.FuncCallCorrectness

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

/-- Replace every `.var`-referencing macro-call argument with a `.const` holding whatever
    value it currently denotes under `assign` -- doesn't change what `newAssignment'` builds,
    since the `.var`/`.const` branches of its recursion produce the identical map update for
    matching values. -/
def constifyMacroCallParam {c : ZKConfig} (assign : Assignment c) (mcp : MacroCallParam c) :
    MacroCallParam c :=
  match mcp with
  | .var (Var.ffv a) => .const (Const.ffc (assign.ff a))
  | .var (Var.boolv a) => .const (Const.boolc (assign.bool a))
  | .const cv => .const cv

theorem newAssignment'_constify {c : ZKConfig} (assign : Assignment c) :
    ∀ (args : List (MacroCallParam c)) (params : List Var) (ffMap : FFVar → FF c)
      (boolMap : BoolVar → Bool),
      newAssignment' assign args params ffMap boolMap =
      newAssignment' assign (args.map (constifyMacroCallParam assign)) params ffMap boolMap := by
  intro args
  induction args with
  | nil => intro params ffMap boolMap; cases params <;> simp [newAssignment']
  | cons a args ih =>
    intro params ffMap boolMap
    cases params with
    | nil => simp [newAssignment']
    | cons p params =>
      cases p with
      | ffv p =>
        cases a with
        | var v =>
          cases v with
          | ffv a => simp only [List.map_cons, constifyMacroCallParam, newAssignment']; exact ih _ _ _
          | boolv a => simp [newAssignment', constifyMacroCallParam]
        | const cv =>
          cases cv with
          | ffc t => simp only [List.map_cons, constifyMacroCallParam, newAssignment']; exact ih _ _ _
          | boolc t => simp [newAssignment', constifyMacroCallParam]
      | boolv p =>
        cases a with
        | var v =>
          cases v with
          | ffv a => simp [newAssignment', constifyMacroCallParam]
          | boolv a => simp only [List.map_cons, constifyMacroCallParam, newAssignment']; exact ih _ _ _
        | const cv =>
          cases cv with
          | ffc t => simp [newAssignment', constifyMacroCallParam]
          | boolc t => simp only [List.map_cons, constifyMacroCallParam, newAssignment']; exact ih _ _ _

/-- A macro call evaluates the same whether its `.var`-referencing arguments are left as-is or
    replaced by `.const`s holding their current denoted values -- so a call's truth value only
    depends on the *values* its arguments carry, not on how they're phrased. -/
theorem evalFormula_call_constify {c : ZKConfig} (gconf : GlobalConfig c)
    (assign : Assignment c) (name : String) (args : List (MacroCallParam c))
    (ms : List (FFMacro c)) :
    evalFormula gconf assign (FFFormula.call name args) ms =
    evalFormula gconf assign (FFFormula.call name (args.map (constifyMacroCallParam assign)))
      ms := by
  simp only [evalFormula]
  cases fetchMacro gconf ms name with
  | error e => rfl
  | ok result =>
    obtain ⟨m, ms'⟩ := result
    simp only [newAssignment]
    rw [newAssignment'_constify assign args m.params (fun _ => 0) (fun _ => false)]

/-- Pure (`newAssignment'`-level) version of `evalFormula_call_const_args_indep`: with every
    argument a `.const`, the result never depends on the starting `assign`. -/
theorem newAssignment'_const_args_indep {c : ZKConfig} :
    ∀ (args : List (MacroCallParam c)) (params : List Var) (assign assign' : Assignment c)
      (ffMap : FFVar → FF c) (boolMap : BoolVar → Bool),
      (∀ mcp ∈ args, ∃ cv, mcp = MacroCallParam.const cv) →
      newAssignment' assign args params ffMap boolMap =
      newAssignment' assign' args params ffMap boolMap := by
  intro args
  induction args with
  | nil => intro params assign assign' ffMap boolMap _; cases params <;> simp [newAssignment']
  | cons a args ih =>
    intro params assign assign' ffMap boolMap hargs
    obtain ⟨cv, hcv⟩ := hargs a (List.mem_cons_self ..)
    subst hcv
    cases params with
    | nil => simp [newAssignment']
    | cons p params =>
      cases p with
      | ffv p =>
        cases cv with
        | ffc t =>
            simp only [newAssignment']
            exact ih params assign assign' _ boolMap
              (fun mcp hmcp => hargs mcp (List.mem_cons_of_mem _ hmcp))
        | boolc t => simp [newAssignment']
      | boolv p =>
        cases cv with
        | ffc t => simp [newAssignment']
        | boolc t =>
            simp only [newAssignment']
            exact ih params assign assign' ffMap _
              (fun mcp hmcp => hargs mcp (List.mem_cons_of_mem _ hmcp))

/-- All-`.const` macro-call arguments make the call's evaluation independent of the ambient
    assignment entirely -- `newAssignment`'s starting maps are always the zero/false default
    regardless of `assign`, and every position gets overwritten by a `.const` value, so `assign`
    is never actually read. -/
theorem evalFormula_call_const_args_indep {c : ZKConfig} (gconf : GlobalConfig c)
    (assign assign' : Assignment c) (name : String) (args : List (MacroCallParam c))
    (ms : List (FFMacro c)) (hargs : ∀ mcp ∈ args, ∃ cv, mcp = MacroCallParam.const cv) :
    evalFormula gconf assign (FFFormula.call name args) ms =
    evalFormula gconf assign' (FFFormula.call name args) ms := by
  simp only [evalFormula]
  cases fetchMacro gconf ms name with
  | error e => rfl
  | ok result =>
    obtain ⟨m, ms'⟩ := result
    simp only [newAssignment]
    rw [newAssignment'_const_args_indep args m.params assign assign' (fun _ => 0)
      (fun _ => false) hargs]

/-- Setting several fresh/matching values into a symbolic and a concrete environment
    (`setVars`/`Semantics.Basic.setVars`, position-for-position over the same id list)
    preserves `EnvMatches`, given the values being set already match pointwise. No `ids.Nodup`
    hypothesis needed: both `setVars` implementations recurse in the same left-to-right order
    (insert the head, then recurse into the tail against the *already-updated* env), so a repeat
    in `ids` gets "last write wins" resolved identically on both sides -- the inductive step below
    only ever needs facts about the *current* head and the already-established `EnvMatches` for
    whatever the tail's own processing decides, never that the head doesn't recur later. -/
theorem EnvMatches_setVars {c : ZKConfig} :
    ∀ (ids : List VarID) (svs : List (SymValue c)) (vs : List (Value c))
      (assignment : Assignment c) (symEnv : SymEnv c) (env : Env c),
      EnvMatches assignment symEnv env →
      List.Forall₂ (symValMatches assignment) svs vs →
      ∀ (symEnv' : SymEnv c), Corellzk2smt.SymExec.Basic.setVars symEnv ids svs = Except.ok symEnv' →
      ∀ (env' : Env c), Corellzk2smt.Language.Core.Semantics.Basic.setVars env ids vs = Except.ok env' →
      EnvMatches assignment symEnv' env' := by
  intro ids
  induction ids with
  | nil =>
      intro svs vs assignment symEnv env hmatch _hforall symEnv' hsym env' henv
      cases svs with
      | nil =>
          cases vs with
          | nil =>
              simp only [Corellzk2smt.SymExec.Basic.setVars, Except.ok.injEq] at hsym
              simp only [Corellzk2smt.Language.Core.Semantics.Basic.setVars,
                Except.ok.injEq] at henv
              rw [← hsym, ← henv]
              exact hmatch
          | cons v vs' => exact absurd henv (by simp [Corellzk2smt.Language.Core.Semantics.Basic.setVars])
      | cons sv svs' => exact absurd hsym (by simp [Corellzk2smt.SymExec.Basic.setVars])
  | cons id ids ih =>
      intro svs vs assignment symEnv env hmatch hforall symEnv' hsym env' henv
      cases svs with
      | nil => exact absurd hsym (by simp [Corellzk2smt.SymExec.Basic.setVars])
      | cons sv svs' =>
        cases vs with
        | nil => exact absurd henv (by simp [Corellzk2smt.Language.Core.Semantics.Basic.setVars])
        | cons v vs' =>
          obtain ⟨hsv_match, hrest_forall⟩ := List.forall₂_cons.mp hforall
          simp only [Corellzk2smt.SymExec.Basic.setVars] at hsym
          simp only [Corellzk2smt.Language.Core.Semantics.Basic.setVars] at henv
          cases hsym' :
              Corellzk2smt.SymExec.Basic.setVars
                (Corellzk2smt.SymExec.Basic.setVar symEnv id sv) ids svs' with
          | error e => rw [hsym'] at hsym; exact absurd hsym (by simp)
          | ok symEnvMid =>
              rw [hsym'] at hsym
              cases henv' :
                  Corellzk2smt.Language.Core.Semantics.Basic.setVars
                    (Corellzk2smt.Language.Core.Semantics.Basic.setVar env id v) ids vs'
                  with
              | error e => rw [henv'] at henv; exact absurd henv (by simp)
              | ok envMid =>
                  rw [henv'] at henv
                  injection hsym with hsym; injection henv with henv
                  rw [← hsym, ← henv]
                  have hmatch1 : EnvMatches assignment
                      (Corellzk2smt.SymExec.Basic.setVar symEnv id sv)
                      (Corellzk2smt.Language.Core.Semantics.Basic.setVar env id v) := by
                    constructor
                    · intro id'
                      simp only [Corellzk2smt.SymExec.Basic.setVar,
                        Corellzk2smt.Language.Core.Semantics.Basic.setVar,
                        Std.TreeMap.contains_insert]
                      by_cases heq : id' = id
                      · simp [heq]
                      · simp [hmatch.1 id']
                    · intro id' sv' hsv'
                      by_cases heq : id' = id
                      · subst heq
                        simp only [Corellzk2smt.SymExec.Basic.setVar,
                          Std.TreeMap.get?_eq_getElem?,
                          Std.TreeMap.getElem?_insert_self] at hsv'
                        injection hsv' with hsv'
                        refine ⟨v, ?_, ?_⟩
                        · simp only [Corellzk2smt.Language.Core.Semantics.Basic.setVar,
                            Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert_self]
                        · rw [← hsv']; exact hsv_match
                      · have hne : id ≠ id' := fun h => heq h.symm
                        simp only [Corellzk2smt.SymExec.Basic.setVar,
                          Std.TreeMap.get?_eq_getElem?,
                          Std.TreeMap.getElem?_insert, Std.compare_eq_iff_eq, hne, if_false] at hsv'
                        rw [← Std.TreeMap.get?_eq_getElem?] at hsv'
                        obtain ⟨v', hv', hm'⟩ := hmatch.2 id' sv' hsv'
                        refine ⟨v', ?_, hm'⟩
                        simp only [Corellzk2smt.Language.Core.Semantics.Basic.setVar,
                          Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert,
                          Std.compare_eq_iff_eq, hne, if_false]
                        rw [← Std.TreeMap.get?_eq_getElem?]
                        exact hv'
                  exact ih svs' vs' assignment (Corellzk2smt.SymExec.Basic.setVar symEnv id sv)
                    (Corellzk2smt.Language.Core.Semantics.Basic.setVar env id v) hmatch1
                    hrest_forall symEnvMid hsym' envMid henv'

/-- If `resolveSimpleExpr` resolves `s` to a scalar symbolic value, `resolveSimpleExprToSymValue`
    (the array-capable generalization used by `seFuncCall`) resolves it to the same value,
    wrapped as `.simple`. -/
theorem resolveSimpleExprToSymValue_of_resolveSimpleExpr {c : ZKConfig} (symEnv : SymEnv c)
    (s : SimpleExpr c) (sv : SimpleSymVal c) (h : resolveSimpleExpr symEnv s = Except.ok sv) :
    resolveSimpleExprToSymValue symEnv s = Except.ok (SymValue.simple sv) := by
  cases s with
  | val v =>
      simp only [resolveSimpleExpr] at h
      injection h with h
      simp only [resolveSimpleExprToSymValue, ← h]
  | var id =>
      simp only [resolveSimpleExpr] at h
      simp only [resolveSimpleExprToSymValue]
      cases hg : Corellzk2smt.SymExec.Basic.getVar symEnv id with
      | error e => rw [hg] at h; simp at h
      | ok val =>
          rw [hg] at h
          cases val with
          | simple sv' => simp only at h; injection h with h; rw [h]
          | array _ => simp at h

/-- If every element of `args` resolves (via `resolveSimpleExpr`, i.e. as a scalar) against
    `symEnv`, then `resolveSimpleExprsToSymValue` resolves the whole list, giving back exactly
    those scalar values wrapped as `.simple`, in order. -/
theorem resolveSimpleExprsToSymValue_of_forall {c : ZKConfig} (symEnv : SymEnv c) :
    ∀ (args : List (SimpleExpr c)),
      (∀ s ∈ args, ∃ sv : SimpleSymVal c, resolveSimpleExpr symEnv s = Except.ok sv) →
      ∃ svs : List (SimpleSymVal c), svs.length = args.length ∧
        List.Forall₂ (fun s sv => resolveSimpleExpr symEnv s = Except.ok sv) args svs ∧
        resolveSimpleExprsToSymValue symEnv args = Except.ok (svs.map SymValue.simple) := by
  intro args
  induction args with
  | nil => intro _; exact ⟨[], rfl, List.Forall₂.nil, rfl⟩
  | cons a args ih =>
      intro hall
      obtain ⟨sv, hsv⟩ := hall a (List.mem_cons_self ..)
      obtain ⟨svs, hlen, hforall, heq⟩ := ih (fun s hs => hall s (List.mem_cons_of_mem _ hs))
      refine ⟨sv :: svs, by simp [hlen], List.Forall₂.cons hsv hforall, ?_⟩
      have h1 := resolveSimpleExprToSymValue_of_resolveSimpleExpr symEnv a sv hsv
      simp only [resolveSimpleExprsToSymValue] at heq ⊢
      rw [List.mapM_cons, h1, heq]
      rfl

/-- Elimination for `List.Forall₂`: every element of the second list is `R`-related to some
    element of the first. -/
theorem forall2_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 → ∀ y ∈ l2, ∃ x ∈ l1, R x y := by
  intro l1 l2 h
  induction h with
  | nil => intro y hy; cases hy
  | cons hd tl ih =>
      intro y hy
      rcases List.mem_cons.mp hy with heq | hmem
      · subst heq; exact ⟨_, List.mem_cons_self .., hd⟩
      · obtain ⟨x, hx, hRxy⟩ := ih y hmem
        exact ⟨x, List.mem_cons_of_mem _ hx, hRxy⟩

/-- `Var`'s `compare` reduces to equality exactly when the underlying `Nat` ids agree (same
    constructor) -- `Var` has no registered `LawfulEqCmp` instance in `FFConstraints/Basic.lean`
    (only `OrientedCmp`/`TransCmp`, needed for `Std.TreeSet`/`Std.TreeMap`'s own structural
    invariants), so this is proved directly from `Var`'s `Ord` instance definition. -/
theorem Var_compare_eq_iff_eq {a b : Var} : compare a b = Ordering.eq ↔ a = b := by
  cases a with
  | ffv n =>
      cases b with
      | ffv m =>
          constructor
          · intro h
            have h' : compare n m = Ordering.eq := h
            rw [Nat.compare_eq_eq.mp h']
          · intro h; injection h with h; subst h; exact Nat.compare_eq_eq.mpr rfl
      | boolv _ => constructor <;> intro h <;> simp_all
  | boolv n =>
      cases b with
      | ffv _ => constructor <;> intro h <;> simp_all
      | boolv m =>
          constructor
          · intro h
            have h' : compare n m = Ordering.eq := h
            rw [Nat.compare_eq_eq.mp h']
          · intro h; injection h with h; subst h; exact Nat.compare_eq_eq.mpr rfl

/-- Does a symbolic value's own runtime shape (`.simple` vs `.array` of a given size) match a
    declared parameter type -- the symbolic-side mirror of `Semantics.Basic.ensureCorrectType`,
    stated as a `Prop` (rather than an `Except`) since it's only ever used as a hypothesis here,
    never computed with. Exactly the condition under which `flattenArgVal` succeeds. -/
def symValueMatchesType {c : ZKConfig} (v : SymValue c) (t : VarType) : Prop :=
  match t, v with
  | .ff, .simple _ => True
  | .array n, .array arr => arr.size = n
  | _, _ => False

/-- `symValVars_array_mem_below`'s unconditional cousin: a single array element's own vars are
    (unconditionally, not just "below some bound") a subset of the whole array's vars -- direct
    instance of the generic `foldl_union_mem_subset`, bridging `Array.foldl`/`List.foldl` via
    `Array.foldl_toList`. -/
theorem symValVars_array_mem_subset {c : ZKConfig} (arr : SymArray c) (sv : SimpleSymVal c)
    (hsv : sv ∈ arr.toList) : simpleValVars sv ⊆ symValVars (SymValue.array arr) := by
  simp only [symValVars]
  rw [← Array.foldl_toList]
  exact foldl_union_mem_subset simpleValVars arr.toList sv hsv emptyVarSet

/-- If `flattenArgVal` succeeds against a shape-matching value, it always gives back exactly
    that value's own `flattenSymValueParams` -- unconditional generalization of the FF-only
    special case (`flattenArgVals_ff_only`, still below, unused by the array-general theorem but
    left as-is since `flattenArgVal`'s `.ff` branch was never modified). -/
theorem flattenArgVal_eq {c : ZKConfig} (type : VarType) (v : SymValue c)
    (h : symValueMatchesType v type) :
    flattenArgVal type v = Except.ok (flattenSymValueParams v) := by
  cases type with
  | ff =>
      cases v with
      | simple sv => rfl
      | array arr => exact absurd h (by simp [symValueMatchesType])
  | array n =>
      cases v with
      | simple sv => exact absurd h (by simp [symValueMatchesType])
      | array arr =>
          simp only [symValueMatchesType] at h
          simp [flattenArgVal, h, flattenSymValueParams]

/-- `flattenArgVal_eq`, for a whole `params`/`vs` list pair (`List.Forall₂`-related pointwise by
    shape): `flattenArgVals` always succeeds, giving back exactly the concatenation of each
    value's own flattened block, i.e. `flattenSymValuesParams vs` -- the array-general
    replacement for `flattenArgVals_ff_only`. -/
theorem flattenArgVals_eq {c : ZKConfig} :
    ∀ (params : List Param) (vs : List (SymValue c)),
      List.Forall₂ (fun p v => symValueMatchesType v p.type) params vs →
      flattenArgVals params vs = Except.ok (flattenSymValuesParams vs) := by
  intro params vs h
  induction h with
  | nil => rfl
  | cons hpv hrest ih =>
      rename_i p v ps vs'
      simp only [flattenArgVals]
      rw [flattenArgVal_eq p.type v hpv, ih]
      simp [flattenSymValuesParams]

/-- Converse of `flattenArgVal_eq`: if `flattenArgVal` succeeds, the value's shape already matched
    the declared type -- `flattenArgVal`'s own cases are exactly `symValueMatchesType`'s, so this
    is definitional case-matching, no extra reasoning needed. Lets `seFuncCall_correct` read the
    shape fact straight back out of `seFuncCall`'s own success. -/
theorem flattenArgVal_defined_of_ok {c : ZKConfig} (type : VarType) (v : SymValue c)
    (ps : List (MacroCallParam c)) (h : flattenArgVal type v = Except.ok ps) :
    symValueMatchesType v type := by
  cases type with
  | ff =>
      cases v with
      | simple _ => trivial
      | array _ => simp [flattenArgVal] at h
  | array n =>
      cases v with
      | simple _ => simp [flattenArgVal] at h
      | array arr =>
          simp only [flattenArgVal] at h
          by_cases heq : arr.size = n
          · simp [symValueMatchesType, heq]
          · simp [heq] at h

/-- `flattenArgVal_defined_of_ok`, for a whole `params`/`argVals` list pair: if `flattenArgVals`
    succeeds, every value's shape already matched its declared param type, pointwise -- the
    arity fact (`params.length = argVals.length`) follows immediately from `List.Forall₂.length_eq`
    given this. -/
theorem flattenArgVals_defined_of_ok {c : ZKConfig} :
    ∀ (params : List Param) (argVals : List (SymValue c)) (ps : List (MacroCallParam c)),
      flattenArgVals params argVals = Except.ok ps →
      List.Forall₂ (fun (pm : Param) sv => symValueMatchesType sv pm.type) params argVals := by
  intro params
  induction params with
  | nil =>
      intro argVals ps h
      cases argVals with
      | nil => exact List.Forall₂.nil
      | cons v vs => simp [flattenArgVals] at h
  | cons p ps' ih =>
      intro argVals psOut h
      cases argVals with
      | nil => simp [flattenArgVals] at h
      | cons v vs =>
          simp only [flattenArgVals] at h
          cases hfv : flattenArgVal p.type v with
          | error e => rw [hfv] at h; simp at h
          | ok ps1 =>
              rw [hfv] at h
              cases hrest : flattenArgVals ps' vs with
              | error e => rw [hrest] at h; simp at h
              | ok ps2 =>
                  exact List.Forall₂.cons (flattenArgVal_defined_of_ok p.type v ps1 hfv)
                    (ih vs ps2 hrest)

/-- Elimination for `flattenSymValuesParams`: every produced macro-call param came from exactly
    one of the list's own values, via that value's own `flattenSymValueParams`. -/
theorem flattenSymValuesParams_mem_elim {c : ZKConfig} (vs : List (SymValue c))
    (mcp : MacroCallParam c) (hmcp : mcp ∈ flattenSymValuesParams vs) :
    ∃ v ∈ vs, mcp ∈ flattenSymValueParams v := by
  simp only [flattenSymValuesParams, List.mem_flatten] at hmcp
  obtain ⟨l, hl, hmcpl⟩ := hmcp
  obtain ⟨v, hv, hleq⟩ := List.mem_map.mp hl
  exact ⟨v, hv, hleq ▸ hmcpl⟩

/-- Every macro-call param a single symbolic value flattens to is either a `.const`, or a
    `.var (Var.ffv n)` with `n` one of that value's own tracked vars (`symValVars`) --
    unconditional shape/vars fact, regardless of `.simple`/`.array`. -/
theorem flattenSymValueParams_mem_vars {c : ZKConfig} (v : SymValue c) (mcp : MacroCallParam c)
    (hmcp : mcp ∈ flattenSymValueParams v) :
    (∃ cv, mcp = MacroCallParam.const cv) ∨
    ∃ n, mcp = MacroCallParam.var (Var.ffv n) ∧ Var.ffv n ∈ symValVars v := by
  cases v with
  | simple sv =>
      simp only [flattenSymValueParams, List.mem_singleton] at hmcp
      cases sv with
      | const cv => exact Or.inl ⟨Const.ffc cv, by rw [hmcp]; rfl⟩
      | ffvar vbr =>
          refine Or.inr ⟨vbr.var, by rw [hmcp]; rfl, ?_⟩
          simp only [symValVars, simpleValVars]
          exact Std.TreeSet.mem_insert.mpr (Or.inl (Var_compare_eq_iff_eq.mpr rfl))
  | array arr =>
      simp only [flattenSymValueParams] at hmcp
      obtain ⟨sv, hsv, hmcpeq⟩ := List.mem_map.mp hmcp
      cases sv with
      | const cv => exact Or.inl ⟨Const.ffc cv, by rw [← hmcpeq]; rfl⟩
      | ffvar vbr =>
          refine Or.inr ⟨vbr.var, by rw [← hmcpeq]; rfl, ?_⟩
          apply symValVars_array_mem_subset arr (SimpleSymVal.ffvar vbr) hsv
          simp only [simpleValVars]
          exact Std.TreeSet.mem_insert.mpr (Or.inl (Var_compare_eq_iff_eq.mpr rfl))

/-- List-level combination of `flattenSymValuesParams_mem_elim`/`flattenSymValueParams_mem_vars`
    -- the membership/vars fact `hfresh`/`hbelowProof`-style reasoning needs about the flattened
    argument segment of a macro call, generalizing what `List.mem_map` over `svs.map
    simpleSymValToMacroCallParam` gave directly in the FF-only case. -/
theorem flattenSymValuesParams_mem_vars {c : ZKConfig} (vs : List (SymValue c))
    (mcp : MacroCallParam c) (hmcp : mcp ∈ flattenSymValuesParams vs) :
    (∃ cv, mcp = MacroCallParam.const cv) ∨
    ∃ n, mcp = MacroCallParam.var (Var.ffv n) ∧ ∃ v ∈ vs, Var.ffv n ∈ symValVars v := by
  obtain ⟨v, hv, hmcpv⟩ := flattenSymValuesParams_mem_elim vs mcp hmcp
  rcases flattenSymValueParams_mem_vars v mcp hmcpv with hconst | ⟨n, hmcpeq, hnmem⟩
  · exact Or.inl hconst
  · exact Or.inr ⟨n, hmcpeq, v, hv, hnmem⟩

/-- If every parameter is `.ff`-typed and every argument value is `.simple` (never `.array`,
    guaranteed by the FF-only restriction), `flattenArgVals` always succeeds, giving back
    exactly one `MacroCallParam` per argument (via `simpleSymValToMacroCallParam`), in order. -/
theorem flattenArgVals_ff_only {c : ZKConfig} :
    ∀ (params : List Param) (svs : List (SimpleSymVal c)),
      params.length = svs.length →
      (∀ pm ∈ params, pm.type = VarType.ff) →
      flattenArgVals params (svs.map SymValue.simple) =
        Except.ok (svs.map simpleSymValToMacroCallParam) := by
  intro params
  induction params with
  | nil =>
      intro svs hlen _hff
      cases svs with
      | nil => rfl
      | cons _ _ => simp at hlen
  | cons p params ih =>
      intro svs hlen hff
      cases svs with
      | nil => simp at hlen
      | cons sv svs =>
          have hpff : p.type = VarType.ff := hff p (List.mem_cons_self ..)
          simp only [List.map_cons, flattenArgVals, hpff, flattenArgVal]
          rw [ih svs (by simpa using hlen) (fun pm hpm => hff pm (List.mem_cons_of_mem _ hpm))]
          rfl

/-- `mintFreshRets` produces exactly one output value per return parameter -- regardless of
    its type (an array-typed ret still contributes a single `SymValue.array` entry), so this
    holds unconditionally, not just in the FF-only case. -/
theorem mintFreshRets_outVals_length {c : ZKConfig} :
    ∀ (nextVarId : Nat) (rets : List Param),
      (mintFreshRets (c := c) nextVarId rets).2.2.length = rets.length := by
  intro nextVarId rets
  induction rets generalizing nextVarId with
  | nil => rfl
  | cons r rest ih =>
      simp only [mintFreshRets]
      obtain ⟨nv1, params1, val1⟩ := mintFreshRetParam (c := c) nextVarId r.type
      simp only [List.length_cons, ih nv1]

/-- If `symEnv` maps `id` to `sv`, every variable `sv` mentions is already accounted for by
    `symEnvVars symEnv` -- i.e. a value obtained via `getVar`/`.get?` never introduces a variable
    beyond what the whole environment already tracks. -/
theorem getVar_mem_symEnvVars {c : ZKConfig} (symEnv : SymEnv c) (id : VarID) (sv : SymValue c)
    (h : symEnv.get? id = some sv) : symValVars sv ⊆ symEnvVars symEnv := by
  have hmem : (id, sv) ∈ symEnv.toList :=
    Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr (Std.TreeMap.get?_eq_getElem? ▸ h)
  simp only [symEnvVars]
  rw [Std.TreeMap.foldl_eq_foldl_toList]
  exact foldl_union_mem_subset (fun p => symValVars p.2) symEnv.toList (id, sv) hmem emptyVarSet

/-- `Corellzk2smt.SymExec.Basic.setVars` always succeeds when the id list and value list have
    matching lengths (mirrors the concrete `Semantics.Basic.setVars`'s own such fact, needed
    separately). -/
theorem setVars_defined_of_length_eq {c : ZKConfig} :
    ∀ (ids : List VarID) (vs : List (SymValue c)) (env : SymEnv c),
      ids.length = vs.length →
      ∃ env', Corellzk2smt.SymExec.Basic.setVars env ids vs = Except.ok env' := by
  intro ids
  induction ids with
  | nil =>
      intro vs env hlen
      cases vs with
      | nil => exact ⟨env, rfl⟩
      | cons _ _ => simp at hlen
  | cons id ids ih =>
      intro vs env hlen
      cases vs with
      | nil => simp at hlen
      | cons v vs =>
          obtain ⟨env', hEnv'⟩ := ih vs (Corellzk2smt.SymExec.Basic.setVar env id v)
            (by simpa using hlen)
          exact ⟨env', by simp only [Corellzk2smt.SymExec.Basic.setVars, hEnv']⟩

/-- Converse of `setVars_defined_of_length_eq`: `setVars` only ever succeeds when the id list and
    value list have matching lengths -- its own definition falls to the mismatched-lengths error
    case otherwise. -/
theorem setVars_length_of_ok {c : ZKConfig} :
    ∀ (ids : List VarID) (vs : List (SymValue c)) (env env' : SymEnv c),
      Corellzk2smt.SymExec.Basic.setVars env ids vs = Except.ok env' → ids.length = vs.length := by
  intro ids
  induction ids with
  | nil =>
      intro vs env env' h
      cases vs with
      | nil => rfl
      | cons v vs => simp [Corellzk2smt.SymExec.Basic.setVars] at h
  | cons id ids ih =>
      intro vs env env' h
      cases vs with
      | nil => simp [Corellzk2smt.SymExec.Basic.setVars] at h
      | cons v vs =>
          simp only [Corellzk2smt.SymExec.Basic.setVars] at h
          cases hrec : Corellzk2smt.SymExec.Basic.setVars
              (Corellzk2smt.SymExec.Basic.setVar env id v) ids vs with
          | error e => rw [hrec] at h; simp at h
          | ok env'' =>
              simp only [List.length_cons]
              exact congrArg (· + 1) (ih vs (Corellzk2smt.SymExec.Basic.setVar env id v) env'' hrec)

/-- Concrete-side mirror of `setVars_defined_of_length_eq`. -/
theorem setVars_defined_of_length_eq_concrete {c : ZKConfig} :
    ∀ (ids : List VarID) (vs : List (Value c)) (env : Env c),
      ids.length = vs.length →
      ∃ env', Corellzk2smt.Language.Core.Semantics.Basic.setVars env ids vs = Except.ok env' := by
  intro ids
  induction ids with
  | nil =>
      intro vs env hlen
      cases vs with
      | nil => exact ⟨env, rfl⟩
      | cons _ _ => simp at hlen
  | cons id ids ih =>
      intro vs env hlen
      cases vs with
      | nil => simp at hlen
      | cons v vs =>
          obtain ⟨env', hEnv'⟩ := ih vs (Corellzk2smt.Language.Core.Semantics.Basic.setVar env id v)
            (by simpa using hlen)
          exact ⟨env', by
            simp only [Corellzk2smt.Language.Core.Semantics.Basic.setVars, hEnv']⟩

/-- `omega`-safe reading of a `List.range`-built list at an in-range position: mapping
    `f` over `range n` and reading position `i < n` back gives exactly `f i`. Used to relate
    the range-based `retVals`/`auxFF`/`auxBool` constructions (built by reading an assignment
    at consecutive fresh positions) back to that same assignment, position-for-position. -/
theorem range_map_getD {α : Type} (n : Nat) (f : Nat → α) (i : Nat) (hi : i < n) (d : α) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  simp

/-- `mintFreshRetParam` mints exactly `typeSize type` consecutive fresh macro-call params/one
    fresh symbolic value, in closed form, unconditionally (mirrors `mintFreshParam_eq` in
    `FuncCorrectness.lean` -- same computation, packaged as a plain tuple instead of `Except`
    since `mintFreshRetParam` never fails). -/
theorem mintFreshRetParam_eq {c : ZKConfig} (nextVarId : Nat) (type : VarType) :
    (mintFreshRetParam (c := c) nextVarId type).1 = nextVarId + typeSize type ∧
    (mintFreshRetParam (c := c) nextVarId type).2.1 =
      (List.range (typeSize type)).map (fun i => MacroCallParam.var (Var.ffv (nextVarId + i))) ∧
    (mintFreshRetParam (c := c) nextVarId type).2.2 = freshRetSymValue nextVarId type := by
  cases type with
  | ff => simp [mintFreshRetParam, typeSize, freshRetSymValue]
  | array size =>
      refine ⟨rfl, ?_, ?_⟩
      · simp only [mintFreshRetParam, typeSize, List.map_map]
        rfl
      · simp only [mintFreshRetParam, freshRetSymValue, List.map_map, Function.comp_def]

/-- `mintFreshRets` mints one fresh block of `paramSize r` consecutive macro-call params per
    ret, flattened in program order -- generalizes the old FF-only `mintFreshRets_ff_only_nv_eq`
    (and its params-list companion, formerly `mintFreshRets_ff_only_params_mem`'s closed-form
    content) unconditionally, via `totalParamSize` instead of `.length`. Mirrors
    `mintFreshParams_paramVars_eq`'s proof shape exactly (same recursion, no `Except` unwrapping
    needed since `mintFreshRetParam`/`mintFreshRets` never fail). -/
theorem mintFreshRets_cons {c : ZKConfig} (nextVarId : Nat) (r : Param) (rs : List Param) :
    mintFreshRets (c := c) nextVarId (r :: rs) =
      ((mintFreshRets (c := c) (mintFreshRetParam (c := c) nextVarId r.type).1 rs).1,
       (mintFreshRetParam (c := c) nextVarId r.type).2.1 ++
         (mintFreshRets (c := c) (mintFreshRetParam (c := c) nextVarId r.type).1 rs).2.1,
       (mintFreshRetParam (c := c) nextVarId r.type).2.2 ::
         (mintFreshRets (c := c) (mintFreshRetParam (c := c) nextVarId r.type).1 rs).2.2) := by
  simp only [mintFreshRets]

theorem mintFreshRets_eq {c : ZKConfig} :
    ∀ (nextVarId : Nat) (rets : List Param),
      (mintFreshRets (c := c) nextVarId rets).1 = nextVarId + totalParamSize rets ∧
      (mintFreshRets (c := c) nextVarId rets).2.1 =
        (List.range (totalParamSize rets)).map
          (fun i => MacroCallParam.var (Var.ffv (nextVarId + i))) := by
  intro nextVarId rets
  induction rets generalizing nextVarId with
  | nil => simp [mintFreshRets]
  | cons r rs ih =>
      obtain ⟨hnv1_eq, hps1_eq, _⟩ := mintFreshRetParam_eq (c := c) nextVarId r.type
      obtain ⟨hnv2_eq, hps2_eq⟩ := ih (mintFreshRetParam (c := c) nextVarId r.type).1
      have hps : paramSize r = typeSize r.type := rfl
      refine ⟨?_, ?_⟩
      · rw [mintFreshRets_cons]; rw [hnv2_eq, hnv1_eq, totalParamSize_cons, hps]; omega
      · rw [mintFreshRets_cons]
        simp only
        rw [hps1_eq, hps2_eq, hnv1_eq, totalParamSize_cons]
        rw [List.range_add, List.map_append, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        simp only [Function.comp, Var.ffv.injEq]
        rw [hps, Nat.add_assoc]

/-- `mintFreshRets`'s output-value list, read back at a specific in-range ret position `j`, is
    exactly the fresh symbolic value `mintFreshRetParam` mints for that ret's own type, starting
    at the cumulative offset of every earlier ret's own block (`totalParamSize (rets.take j)`) --
    the position-indexed characterization needed since (unlike `paramVars`/the macro-call param
    list) `mintFreshRets`'s value list is one entry *per ret*, not flattened to one per slot. -/
theorem mintFreshRets_outVals_getD {c : ZKConfig} :
    ∀ (rets : List Param) (nextVarId : Nat) (j : Nat), j < rets.length →
      (mintFreshRets (c := c) nextVarId rets).2.2.getD j (SymValue.simple (SimpleSymVal.const 0)) =
        freshRetSymValue (nextVarId + totalParamSize (rets.take j))
          (rets.getD j { name := "", type := VarType.ff }).type := by
  intro rets
  induction rets with
  | nil => intro nextVarId j hj; simp at hj
  | cons r rs ih =>
      intro nextVarId j hj
      rw [mintFreshRets_cons]
      obtain ⟨hnv1_eq, _, hsv_eq⟩ := mintFreshRetParam_eq (c := c) nextVarId r.type
      cases j with
      | zero => simpa using hsv_eq
      | succ j' =>
          have hj' : j' < rs.length := by simpa using hj
          have := ih (mintFreshRetParam (c := c) nextVarId r.type).1 j' hj'
          simp only [List.getD_cons_succ, List.take_succ_cons, totalParamSize_cons]
          rw [this, hnv1_eq]
          have hps : paramSize r = typeSize r.type := rfl
          rw [hps, Nat.add_assoc]

/-- `mintFreshRets` only ever grows the variable-id counter. -/
theorem mintFreshRets_mono {c : ZKConfig} :
    ∀ (nextVarId : Nat) (rets : List Param),
      nextVarId ≤ (mintFreshRets (c := c) nextVarId rets).1 := by
  intro nextVarId rets
  induction rets generalizing nextVarId with
  | nil => exact le_refl _
  | cons r rest ih =>
      have hparam : nextVarId ≤ (mintFreshRetParam (c := c) nextVarId r.type).1 := by
        cases r.type with
        | ff => simp [mintFreshRetParam]
        | array size => simp [mintFreshRetParam]
      have heq : (mintFreshRets (c := c) nextVarId (r :: rest)).1 =
          (mintFreshRets (c := c) (mintFreshRetParam (c := c) nextVarId r.type).1 rest).1 := rfl
      rw [heq]
      exact hparam.trans (ih _)

/-- `mintFreshAuxParams` only ever grows the variable-id counter. -/
theorem mintFreshAuxParams_mono {c : ZKConfig} (nextVarId numFF numBool : Nat) :
    nextVarId ≤ (mintFreshAuxParams (c := c) nextVarId numFF numBool).1 := by
  simp only [mintFreshAuxParams]
  omega

/-- Every macro-call param `mintFreshRets` mints is a fresh `Var.ffv` strictly within
    `[nextVarId, (mintFreshRets nextVarId rets).1)` -- generalizes the old FF-only
    `mintFreshRets_ff_only_params_mem` unconditionally, as a direct corollary of the closed form
    `mintFreshRets_eq` now gives for `.2.1`. -/
theorem mintFreshRets_params_mem {c : ZKConfig} (rets : List Param) (nextVarId : Nat) :
    ∀ mcp ∈ (mintFreshRets (c := c) nextVarId rets).2.1,
      ∃ n, mcp = MacroCallParam.var (Var.ffv n) ∧
        nextVarId ≤ n ∧ n < (mintFreshRets (c := c) nextVarId rets).1 := by
  intro mcp hmcp
  obtain ⟨hnv_eq, hps_eq⟩ := mintFreshRets_eq (c := c) nextVarId rets
  rw [hps_eq] at hmcp
  obtain ⟨i, hi_mem, hi_eq⟩ := List.mem_map.mp hmcp
  have hi_range := List.mem_range.mp hi_mem
  exact ⟨nextVarId + i, hi_eq.symm, Nat.le_add_right _ _, hnv_eq ▸ Nat.add_lt_add_left hi_range _⟩

/-- Converse of `mintFreshRets_params_mem`: every in-range flattened position actually has a
    corresponding macro-call param present. -/
theorem mintFreshRets_params_mem_of_index {c : ZKConfig} (rets : List Param) (nextVarId : Nat) :
    ∀ i, i < totalParamSize rets →
      MacroCallParam.var (Var.ffv (nextVarId + i)) ∈ (mintFreshRets (c := c) nextVarId rets).2.1 := by
  intro i hi
  obtain ⟨_, hps_eq⟩ := mintFreshRets_eq (c := c) nextVarId rets
  rw [hps_eq]
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

/-- Every output value `mintFreshRets` mints for an all-`.ff` `rets` list is a fresh
    `.ffvar` strictly within `[nextVarId, (mintFreshRets nextVarId rets).1)` -- the
    value-level mirror of `mintFreshRets_ff_only_params_mem`. -/
theorem mintFreshRets_ff_only_outVals_mem {c : ZKConfig} :
    ∀ (rets : List Param) (nextVarId : Nat), (∀ pm ∈ rets, pm.type = VarType.ff) →
      ∀ sv ∈ (mintFreshRets (c := c) nextVarId rets).2.2,
        ∃ n, sv = SymValue.simple (SimpleSymVal.ffvar { var := n, bits := none }) ∧
          nextVarId ≤ n ∧ n < (mintFreshRets (c := c) nextVarId rets).1 := by
  intro rets
  induction rets with
  | nil => intro nextVarId _hff sv hsv; simp [mintFreshRets] at hsv
  | cons r rest ih =>
      intro nextVarId hff sv hsv
      have hrff : r.type = VarType.ff := hff r (List.mem_cons_self ..)
      have heq1 : mintFreshRetParam (c := c) nextVarId r.type =
          (nextVarId + 1, [MacroCallParam.var (Var.ffv nextVarId)],
            SymValue.simple (SimpleSymVal.ffvar { var := nextVarId, bits := none })) := by
        rw [hrff]; rfl
      have hstep : (mintFreshRets (c := c) nextVarId (r :: rest)).2.2 =
          [SymValue.simple (SimpleSymVal.ffvar { var := nextVarId, bits := none })] ++
            (mintFreshRets (c := c) (nextVarId + 1) rest).2.2 := by
        simp only [mintFreshRets, heq1, List.singleton_append]
      have heqOuter : (mintFreshRets (c := c) nextVarId (r :: rest)).1 =
          (mintFreshRets (c := c) (nextVarId + 1) rest).1 := by
        simp only [mintFreshRets, heq1]
      rw [hstep] at hsv
      rcases List.mem_append.mp hsv with hsv1 | hsv2
      · simp only [List.mem_singleton] at hsv1
        refine ⟨nextVarId, hsv1, le_refl _, ?_⟩
        rw [heqOuter]
        have hmono := mintFreshRets_mono (c := c) (nextVarId + 1) rest
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hmono
      · obtain ⟨n, hsveq, hn1, hn2⟩ :=
          ih (nextVarId + 1) (fun pm hpm => hff pm (List.mem_cons_of_mem _ hpm)) sv hsv2
        exact ⟨n, hsveq, by omega, heqOuter ▸ hn2⟩

/-- Every macro-call param `mintFreshAuxParams` mints is a fresh `Var.ffv`/`Var.boolv` strictly
    within `[nextVarId, (mintFreshAuxParams nextVarId numFF numBool).1)`, split at `numFF`. -/
theorem mintFreshAuxParams_params_mem {c : ZKConfig} (nextVarId numFF numBool : Nat) :
    ∀ mcp ∈ (mintFreshAuxParams (c := c) nextVarId numFF numBool).2,
      (∃ n, mcp = MacroCallParam.var (Var.ffv n) ∧ nextVarId ≤ n ∧ n < nextVarId + numFF) ∨
      (∃ n, mcp = MacroCallParam.var (Var.boolv n) ∧ nextVarId + numFF ≤ n ∧
        n < (mintFreshAuxParams (c := c) nextVarId numFF numBool).1) := by
  intro mcp hmcp
  simp only [mintFreshAuxParams] at hmcp
  rcases List.mem_append.mp hmcp with h1 | h2
  · obtain ⟨v, hv, heq⟩ := List.mem_map.mp h1
    obtain ⟨i, hi, hveq⟩ := List.mem_map.mp hv
    have hir := List.mem_range.mp hi
    left
    refine ⟨v, heq.symm, ?_, ?_⟩
    · rw [← hveq]; exact Nat.le_add_right nextVarId i
    · rw [← hveq]; exact Nat.add_lt_add_left hir nextVarId
  · obtain ⟨v, hv, heq⟩ := List.mem_map.mp h2
    obtain ⟨i, hi, hveq⟩ := List.mem_map.mp hv
    have hir := List.mem_range.mp hi
    right
    refine ⟨v, heq.symm, ?_, ?_⟩
    · rw [← hveq]; exact Nat.le_add_right (nextVarId + numFF) i
    · simp only [mintFreshAuxParams]
      rw [← hveq]; exact Nat.add_lt_add_left hir (nextVarId + numFF)

/-- `omega` can't see hypotheses/goals stated over `FFVar`/`BoolVar` (reducible `abbrev`s for
    `ℕ`) as linear-arithmetic facts -- it reports "no usable constraints found" even when the
    underlying values are plain naturals. This is a small `Nat`-only (never `FFVar`-typed)
    helper: `n - a < b` given `a ≤ n < a + b`, proved with `omega` here (where the params are
    genuinely declared `Nat`) and then applied at `FFVar`-typed call sites via defeq. -/
theorem nat_sub_lt_of_range {a b n : Nat} (h1 : a ≤ n) (h2 : n < a + b) : n - a < b := by omega

/-- Generic elimination for a union-fold: if `v` is in the final result, either it was already
    in the accumulator we started from, or some list element's own contribution puts it there. -/
theorem foldl_union_mem_elim {α : Type} (f : α → VarSet) :
    ∀ (l : List α) (init : VarSet) (v : Var),
      v ∈ l.foldl (fun acc x => acc ∪ f x) init → v ∈ init ∨ ∃ x ∈ l, v ∈ f x := by
  intro l
  induction l with
  | nil => intro init v hv; exact Or.inl hv
  | cons x xs ih =>
      intro init v hv
      simp only [List.foldl_cons] at hv
      rcases ih (init ∪ f x) v hv with h1 | h2
      · rcases Std.TreeSet.mem_union_iff.mp h1 with h1a | h1b
        · exact Or.inl h1a
        · exact Or.inr ⟨x, List.mem_cons_self .., h1b⟩
      · obtain ⟨y, hy, hvy⟩ := h2
        exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, hvy⟩

/-- Elimination for an "insert-if-matches" fold (the shape `ffVarsOfFormula`/`bVarsOfFormula`'s
    `.call` case uses): if `v` ends up in the result, either it was already in the accumulator we
    started from, or some list element's extracted var (via `g`) was exactly `v`. -/
theorem foldl_insert_mem_elim {β : Type} (g : β → Option Var) :
    ∀ (l : List β) (init : VarSet) (v : Var),
      v ∈ l.foldl (fun acc p => match g p with | some x => acc.insert x | none => acc) init →
      v ∈ init ∨ ∃ x ∈ l, g x = some v := by
  intro l
  induction l with
  | nil => intro init v hv; exact Or.inl hv
  | cons p ps ih =>
      intro init v hv
      simp only [List.foldl_cons] at hv
      cases hg : g p with
      | none =>
          rw [hg] at hv
          rcases ih init v hv with h1 | h2
          · exact Or.inl h1
          · obtain ⟨x, hx, hgx⟩ := h2; exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, hgx⟩
      | some x =>
          rw [hg] at hv
          rcases ih (init.insert x) v hv with h1 | h2
          · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
            · exact Or.inr ⟨p, List.mem_cons_self .., by
                rw [← Var_compare_eq_iff_eq.mp heq]; exact hg⟩
            · exact Or.inl hmem
          · obtain ⟨y, hy, hgy⟩ := h2; exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, hgy⟩

/-- Elimination directly specialized to `ffVarsOfFormula`'s `.call` fold shape (no `Option`
    indirection, avoiding higher-order-unification friction when applying the generic
    `foldl_insert_mem_elim` at that exact syntactic shape). -/
theorem ffVars_call_mem_elim {c : ZKConfig} :
    ∀ (l : List (MacroCallParam c)) (init : VarSet) (v : Var),
      v ∈ l.foldl (fun acc p => match p with
        | MacroCallParam.var (Var.ffv n) => acc.insert (Var.ffv n) | _ => acc) init →
      v ∈ init ∨ ∃ n, MacroCallParam.var (Var.ffv n) ∈ l ∧ v = Var.ffv n := by
  intro l
  induction l with
  | nil => intro init v hv; exact Or.inl hv
  | cons p ps ih =>
      intro init v hv
      simp only [List.foldl_cons] at hv
      cases p with
      | var vv =>
          cases vv with
          | ffv n =>
              rcases ih (init.insert (Var.ffv n)) v hv with h1 | h2
              · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
                · exact Or.inr ⟨n, List.mem_cons_self .., (Var_compare_eq_iff_eq.mp heq).symm⟩
                · exact Or.inl hmem
              · obtain ⟨m, hm, hveq⟩ := h2
                exact Or.inr ⟨m, List.mem_cons_of_mem _ hm, hveq⟩
          | boolv _n =>
              rcases ih init v hv with h1 | h2
              · exact Or.inl h1
              · obtain ⟨m, hm, hveq⟩ := h2; exact Or.inr ⟨m, List.mem_cons_of_mem _ hm, hveq⟩
      | const _ =>
          rcases ih init v hv with h1 | h2
          · exact Or.inl h1
          · obtain ⟨m, hm, hveq⟩ := h2; exact Or.inr ⟨m, List.mem_cons_of_mem _ hm, hveq⟩

/-- Elimination directly specialized to `bVarsOfFormula`'s `.call` fold shape. -/
theorem bVars_call_mem_elim {c : ZKConfig} :
    ∀ (l : List (MacroCallParam c)) (init : VarSet) (v : Var),
      v ∈ l.foldl (fun acc p => match p with
        | MacroCallParam.var (Var.boolv n) => acc.insert (Var.boolv n) | _ => acc) init →
      v ∈ init ∨ ∃ n, MacroCallParam.var (Var.boolv n) ∈ l ∧ v = Var.boolv n := by
  intro l
  induction l with
  | nil => intro init v hv; exact Or.inl hv
  | cons p ps ih =>
      intro init v hv
      simp only [List.foldl_cons] at hv
      cases p with
      | var vv =>
          cases vv with
          | boolv n =>
              rcases ih (init.insert (Var.boolv n)) v hv with h1 | h2
              · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
                · exact Or.inr ⟨n, List.mem_cons_self .., (Var_compare_eq_iff_eq.mp heq).symm⟩
                · exact Or.inl hmem
              · obtain ⟨m, hm, hveq⟩ := h2
                exact Or.inr ⟨m, List.mem_cons_of_mem _ hm, hveq⟩
          | ffv _n =>
              rcases ih init v hv with h1 | h2
              · exact Or.inl h1
              · obtain ⟨m, hm, hveq⟩ := h2; exact Or.inr ⟨m, List.mem_cons_of_mem _ hm, hveq⟩
      | const _ =>
          rcases ih init v hv with h1 | h2
          · exact Or.inl h1
          · obtain ⟨m, hm, hveq⟩ := h2; exact Or.inr ⟨m, List.mem_cons_of_mem _ hm, hveq⟩

/-- Every variable a value obtained via `.get?` mentions is already accounted for by
    `symEnvVars`. -/
theorem symEnvVars_mem_elim {c : ZKConfig} (env : SymEnv c) (v : Var) (hv : v ∈ symEnvVars env) :
    ∃ id sv, env.get? id = some sv ∧ v ∈ symValVars sv := by
  simp only [symEnvVars] at hv
  rw [Std.TreeMap.foldl_eq_foldl_toList] at hv
  rcases foldl_union_mem_elim (fun p => symValVars p.2) env.toList emptyVarSet v hv with h1 | h2
  · exact absurd h1 Std.TreeSet.not_mem_emptyc
  · obtain ⟨p, hp, hvp⟩ := h2
    refine ⟨p.1, p.2, ?_, hvp⟩
    rw [Std.TreeMap.get?_eq_getElem?]
    exact Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hp

/-- A single `setVar` update only ever introduces the new value's own vars on top of what
    `symEnvVars` already tracked -- never anything else, since a `Std.TreeMap.insert` either
    replaces one entry or adds a new one, and every other entry survives unchanged. -/
theorem symEnvVars_setVar_subset {c : ZKConfig} (env : SymEnv c) (id : VarID) (sv0 : SymValue c)
    (v : Var) (hv : v ∈ symEnvVars (Corellzk2smt.SymExec.Basic.setVar env id sv0)) :
    v ∈ symEnvVars env ∨ v ∈ symValVars sv0 := by
  obtain ⟨id', sv', hget, hv'⟩ := symEnvVars_mem_elim _ v hv
  simp only [Corellzk2smt.SymExec.Basic.setVar, Std.TreeMap.get?_eq_getElem?,
    Std.TreeMap.getElem?_insert] at hget
  by_cases heq : compare id id' = Ordering.eq
  · rw [if_pos heq] at hget
    injection hget with hget
    exact Or.inr (hget ▸ hv')
  · rw [if_neg heq] at hget
    rw [← Std.TreeMap.get?_eq_getElem?] at hget
    exact Or.inl (getVar_mem_symEnvVars env id' sv' hget v hv')

/-- Lifting `symEnvVars_setVar_subset` across `setVars`: every variable in the result either
    comes from the original environment, or from one of the freshly-set values. -/
theorem symEnvVars_setVars_subset {c : ZKConfig} :
    ∀ (ids : List VarID) (vs : List (SymValue c)) (env : SymEnv c) (env' : SymEnv c),
      Corellzk2smt.SymExec.Basic.setVars env ids vs = Except.ok env' →
      ∀ v ∈ symEnvVars env', v ∈ symEnvVars env ∨ ∃ sv ∈ vs, v ∈ symValVars sv := by
  intro ids
  induction ids with
  | nil =>
      intro vs env env' hsv v hv
      cases vs with
      | nil =>
          simp only [Corellzk2smt.SymExec.Basic.setVars, Except.ok.injEq] at hsv
          rw [← hsv] at hv; exact Or.inl hv
      | cons _ _ => exact absurd hsv (by simp [Corellzk2smt.SymExec.Basic.setVars])
  | cons id ids ih =>
      intro vs env env' hsv v hv
      cases vs with
      | nil => exact absurd hsv (by simp [Corellzk2smt.SymExec.Basic.setVars])
      | cons sv0 vs =>
          simp only [Corellzk2smt.SymExec.Basic.setVars] at hsv
          cases hmid : Corellzk2smt.SymExec.Basic.setVars
              (Corellzk2smt.SymExec.Basic.setVar env id sv0) ids vs with
          | error e => rw [hmid] at hsv; simp at hsv
          | ok envMid =>
              rw [hmid] at hsv
              injection hsv with hsv
              rw [← hsv] at hv
              rcases ih vs (Corellzk2smt.SymExec.Basic.setVar env id sv0) envMid hmid v hv
                with h1 | h2
              · rcases symEnvVars_setVar_subset env id sv0 v h1 with h1a | h1b
                · exact Or.inl h1a
                · exact Or.inr ⟨sv0, List.mem_cons_self .., h1b⟩
              · obtain ⟨sv', hsv', hv'⟩ := h2
                exact Or.inr ⟨sv', List.mem_cons_of_mem _ hsv', hv'⟩

/-- If `resolveSimpleExpr` resolves `s` to `sv`, every var `sv` mentions is already tracked by
    `symEnv` -- constants mention none, and a resolved variable reference must have come from
    `symEnv` itself. -/
theorem resolveSimpleExpr_vars_subset {c : ZKConfig} (symEnv : SymEnv c) (s : SimpleExpr c)
    (sv : SimpleSymVal c) (h : resolveSimpleExpr symEnv s = Except.ok sv) :
    simpleValVars sv ⊆ symEnvVars symEnv := by
  cases s with
  | val v =>
      simp only [resolveSimpleExpr] at h
      injection h with h
      rw [← h]
      intro v' hv'
      simp only [simpleValVars] at hv'
      exact absurd hv' Std.TreeSet.not_mem_emptyc
  | var id =>
      simp only [resolveSimpleExpr] at h
      cases hg : Corellzk2smt.SymExec.Basic.getVar symEnv id with
      | error e => rw [hg] at h; simp at h
      | ok val =>
          rw [hg] at h
          cases val with
          | simple sv' =>
              simp only at h
              injection h with h
              rw [← h]
              have hget : symEnv.get? id = some (SymValue.simple sv') := by
                simp only [Corellzk2smt.SymExec.Basic.getVar] at hg
                cases hgv : symEnv.get? id with
                | none => rw [hgv] at hg; simp at hg
                | some v => rw [hgv] at hg; injection hg with hg; rw [hg]
              intro v' hv'
              exact getVar_mem_symEnvVars symEnv id (SymValue.simple sv') hget v'
                (by simpa [symValVars] using hv')
          | array _ => simp at h

/-- Lifting `resolveSimpleExpr_vars_subset` across a `List.Forall₂` of per-element resolutions
    (as produced by `resolveSimpleExprsToSymValue_of_forall`): every resolved argument's vars
    are already tracked by `symEnv`. -/
theorem resolveSimpleExprsToSymValue_vars_subset {c : ZKConfig} (symEnv : SymEnv c)
    (args : List (SimpleExpr c)) (svs : List (SimpleSymVal c))
    (hforall : List.Forall₂ (fun s sv => resolveSimpleExpr symEnv s = Except.ok sv) args svs) :
    ∀ sv ∈ svs, simpleValVars sv ⊆ symEnvVars symEnv := by
  intro sv hsv
  obtain ⟨s, _hs, hres⟩ := forall2_mem_right hforall sv hsv
  exact resolveSimpleExpr_vars_subset symEnv s sv hres

/-- If `evalSimpleExprToFFValue` resolves `s` to `v`, `evalSimpleExprToValue` (the array-capable
    generalization `evalFuncCallCmd`/`evalSimpleExprsToValue` actually use) resolves it to the
    same value, wrapped as `.scalar`. -/
theorem evalSimpleExprToValue_of_evalSimpleExprToFFValue {c : ZKConfig} (env : Env c)
    (s : SimpleExpr c) (v : FF c) (h : evalSimpleExprToFFValue env s = Except.ok v) :
    evalSimpleExprToValue env s = Except.ok (Value.scalar v) := by
  cases s with
  | val v' =>
      simp only [evalSimpleExprToFFValue] at h
      injection h with h
      simp only [evalSimpleExprToValue, h]
  | var id =>
      simp only [evalSimpleExprToFFValue] at h
      cases hg : Corellzk2smt.Language.Core.Semantics.Basic.getVar env id with
      | error e => rw [hg] at h; simp at h
      | ok val =>
          rw [hg] at h
          cases val with
          | scalar v' =>
              simp only at h
              injection h with h
              simp only [evalSimpleExprToValue, hg, h]
          | array _ => simp at h

/-- Lifting `resolveSimpleExpr_correct` across a `List.Forall₂` of per-element resolutions: if
    every `s ∈ args` resolves (symbolically) to the matching `sv ∈ svs`, and `EnvMatches` holds,
    then `evalSimpleExprsToValue` succeeds on the concrete side too, with a list of `FF`
    values `simpleValMatches`-related to `svs` pointwise. -/
theorem list_resolveSimpleExpr_correct {c : ZKConfig} (symEnv : SymEnv c) (env : Env c)
    (assignment : Assignment c) (hmatch : EnvMatches assignment symEnv env) :
    ∀ (args : List (SimpleExpr c)) (svs : List (SimpleSymVal c)),
      List.Forall₂ (fun s sv => resolveSimpleExpr symEnv s = Except.ok sv) args svs →
      ∃ vs : List (FF c), evalSimpleExprsToValue env args = Except.ok (vs.map Value.scalar) ∧
        List.Forall₂ (simpleValMatches assignment) svs vs := by
  intro args
  induction args with
  | nil =>
      intro svs hforall
      cases hforall
      exact ⟨[], rfl, List.Forall₂.nil⟩
  | cons a args ih =>
      intro svs hforall
      cases svs with
      | nil => cases hforall
      | cons sv0 svsTail =>
          obtain ⟨hd, tl⟩ := List.forall₂_cons.mp hforall
          obtain ⟨v0, hv0, hmatch0⟩ := resolveSimpleExpr_correct symEnv a env assignment sv0
            hmatch hd
          obtain ⟨vs, heq, hforallrest⟩ := ih svsTail tl
          refine ⟨v0 :: vs, ?_, List.Forall₂.cons hmatch0 hforallrest⟩
          have h1 := evalSimpleExprToValue_of_evalSimpleExprToFFValue env a v0 hv0
          simp only [evalSimpleExprsToValue] at heq ⊢
          rw [List.mapM_cons, h1, heq]
          rfl

/-- Constifying the flattened input-argument params under an assignment that agrees with the
    matching one on `symEnv`'s own vars recovers exactly the value list `svs` matches against --
    the "input segment" building block for relating `cf` (mixed const/var args) to the all-const
    form `H_specCorrect` is phrased over. -/
theorem constify_input_params_eq {c : ZKConfig} (symEnv : SymEnv c)
    (assignment assignment' : Assignment c)
    (hagree : ∀ n, Var.ffv n ∈ symEnvVars symEnv → assignment'.ff n = assignment.ff n) :
    ∀ (svs : List (SimpleSymVal c)) (vs : List (FF c)),
      (∀ sv ∈ svs, simpleValVars sv ⊆ symEnvVars symEnv) →
      List.Forall₂ (simpleValMatches assignment) svs vs →
      (svs.map simpleSymValToMacroCallParam).map (constifyMacroCallParam assignment') =
        vs.map (fun v => MacroCallParam.const (Const.ffc v)) := by
  intro svs
  induction svs with
  | nil => intro vs _ hforall; cases hforall; rfl
  | cons sv svs ih =>
      intro vs hvars hforall
      cases vs with
      | nil => cases hforall
      | cons v vs =>
          obtain ⟨hd, tl⟩ := List.forall₂_cons.mp hforall
          have hsvvars : simpleValVars sv ⊆ symEnvVars symEnv := hvars sv (List.mem_cons_self ..)
          have hrest : ∀ sv' ∈ svs, simpleValVars sv' ⊆ symEnvVars symEnv :=
            fun sv' hsv' => hvars sv' (List.mem_cons_of_mem _ hsv')
          simp only [List.map_cons]
          rw [ih vs hrest tl]
          congr 1
          cases sv with
          | const v' =>
              simp only [simpleValMatches] at hd
              simp only [simpleSymValToMacroCallParam, constifyMacroCallParam, hd]
          | ffvar vbr =>
              simp only [simpleValMatches] at hd
              simp only [simpleSymValToMacroCallParam, constifyMacroCallParam]
              have hmem : Var.ffv vbr.var ∈ symEnvVars symEnv :=
                hsvvars (Var.ffv vbr.var) (by simp [simpleValVars])
              rw [hagree vbr.var hmem, hd]

/-- Constifying the fresh output params `mintFreshRets` mints (all-`.ff`) under an assignment
    that agrees with `retVals` position-for-position on that range recovers exactly
    `retVals` -- the "output segment" building block. -/
theorem mintFreshRets_ff_only_constify_eq {c : ZKConfig} (assignment' : Assignment c) :
    ∀ (rets : List Param) (nextVarId : Nat), (∀ pm ∈ rets, pm.type = VarType.ff) →
      ∀ (retVals : List (FF c)), retVals.length = rets.length →
      (∀ i, i < rets.length → assignment'.ff (nextVarId + i) = retVals.getD i 0) →
      ((mintFreshRets (c := c) nextVarId rets).2.1).map (constifyMacroCallParam assignment') =
        retVals.map (fun v => MacroCallParam.const (Const.ffc v)) := by
  intro rets
  induction rets with
  | nil =>
      intro nextVarId _hff retVals hlen _hassign
      cases retVals with
      | nil => simp [mintFreshRets]
      | cons _ _ => simp at hlen
  | cons r rest ih =>
      intro nextVarId hff retVals hlen hassign
      cases retVals with
      | nil => simp at hlen
      | cons rv retVals =>
          have hrff : r.type = VarType.ff := hff r (List.mem_cons_self ..)
          have heq1 : mintFreshRetParam (c := c) nextVarId r.type =
              (nextVarId + 1, [MacroCallParam.var (Var.ffv nextVarId)],
                SymValue.simple (SimpleSymVal.ffvar { var := nextVarId, bits := none })) := by
            rw [hrff]; rfl
          have hstep : (mintFreshRets (c := c) nextVarId (r :: rest)).2.1 =
              [MacroCallParam.var (Var.ffv nextVarId)] ++
                (mintFreshRets (c := c) (nextVarId + 1) rest).2.1 := by
            simp only [mintFreshRets, heq1]
          rw [hstep]
          have hhead : assignment'.ff nextVarId = rv := by
            have h0 := hassign 0 (by simp)
            simpa using h0
          simp only [List.map_append, List.map_cons, List.map_nil, List.singleton_append,
            constifyMacroCallParam, hhead]
          congr 1
          apply ih (nextVarId + 1) (fun pm hpm => hff pm (List.mem_cons_of_mem _ hpm)) retVals
            (by simpa using hlen)
          intro i hi
          have hstepAssign := hassign (i + 1) (by simpa using hi)
          have : nextVarId + (i + 1) = nextVarId + 1 + i := by omega
          rw [this] at hstepAssign
          simpa using hstepAssign

/-- If a function `f`, applied at `nextVarId + i` for each in-range `i`, matches `g` applied to
    the corresponding entry of `vals` (a length-`n` list), then mapping `f` over the "range of
    fresh ids starting at `nextVarId`" gives exactly `vals.map g`. General-purpose bridge between
    `List.range`-indexed fresh-variable ranges and an explicit value list at the same positions. -/
theorem range_map_eq_of_pointwise {α β : Type} (n nextVarId : Nat) (vals : List α)
    (hlen : vals.length = n) (f : Nat → β) (g : α → β) (default : α)
    (hassign : ∀ i, i < n → f (nextVarId + i) = g (vals.getD i default)) :
    (List.range n).map (fun i => f (nextVarId + i)) = vals.map g := by
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_map]
  by_cases hi : i < n
  · rw [List.getElem?_range hi]
    have hvi : vals[i]? = some (vals.getD i default) := by
      rw [List.getD_eq_getElem?_getD]
      cases h : vals[i]? with
      | none => simp at h; omega
      | some x => simp [h]
    rw [hvi]
    simp only [Option.map_some]
    congr 1
    exact hassign i hi
  · have h1 : (List.range n)[i]? = none := by
      rw [List.getElem?_eq_none_iff]; simp; omega
    have h2 : vals[i]? = none := by
      rw [List.getElem?_eq_none_iff]; omega
    rw [h1, h2]
    simp

/-- Constifying the fresh aux params `mintFreshAuxParams` mints under an assignment that
    agrees with `auxFF ++ auxBool` (in the ff-then-bool positional layout the minting uses)
    recovers exactly that split value list -- the "aux segment" building block. -/
theorem mintFreshAuxParams_constify_eq {c : ZKConfig} (assignment' : Assignment c)
    (nextVarId numFF numBool : Nat) (auxFF : List (FF c)) (auxBool : List Bool)
    (hFFlen : auxFF.length = numFF) (hBoollen : auxBool.length = numBool)
    (hassignFF : ∀ i, i < numFF → assignment'.ff (nextVarId + i) = auxFF.getD i 0)
    (hassignBool : ∀ i, i < numBool → assignment'.bool (nextVarId + numFF + i) = auxBool.getD i false) :
    ((mintFreshAuxParams (c := c) nextVarId numFF numBool).2).map (constifyMacroCallParam assignment') =
      auxFF.map (fun v => MacroCallParam.const (Const.ffc v)) ++
        auxBool.map (fun v => MacroCallParam.const (Const.boolc v)) := by
  simp only [mintFreshAuxParams, List.map_append, List.map_map]
  congr 1
  · apply range_map_eq_of_pointwise numFF nextVarId auxFF hFFlen
      (fun v => constifyMacroCallParam assignment' (MacroCallParam.var (Var.ffv v)))
      (fun v => MacroCallParam.const (Const.ffc v)) 0
    intro i hi
    simp only [constifyMacroCallParam, hassignFF i hi]
  · apply range_map_eq_of_pointwise numBool (nextVarId + numFF) auxBool hBoollen
      (fun v => constifyMacroCallParam assignment' (MacroCallParam.var (Var.boolv v)))
      (fun v => MacroCallParam.const (Const.boolc v)) false
    intro i hi
    simp only [constifyMacroCallParam, hassignBool i hi]

/-- Converse of `mintFreshRets_ff_only_params_mem`: every index in range actually has a
    corresponding macro-call param present, not just "some var". -/
theorem mintFreshRets_ff_only_params_mem_of_index {c : ZKConfig} :
    ∀ (rets : List Param) (nextVarId : Nat), (∀ pm ∈ rets, pm.type = VarType.ff) →
      ∀ i, i < rets.length →
        MacroCallParam.var (Var.ffv (nextVarId + i)) ∈
          (mintFreshRets (c := c) nextVarId rets).2.1 := by
  intro rets
  induction rets with
  | nil => intro nextVarId _hff i hi; simp at hi
  | cons r rest ih =>
      intro nextVarId hff i hi
      have hrff : r.type = VarType.ff := hff r (List.mem_cons_self ..)
      have heq1 : mintFreshRetParam (c := c) nextVarId r.type =
          (nextVarId + 1, [MacroCallParam.var (Var.ffv nextVarId)],
            SymValue.simple (SimpleSymVal.ffvar { var := nextVarId, bits := none })) := by
        rw [hrff]; rfl
      have hstep : (mintFreshRets (c := c) nextVarId (r :: rest)).2.1 =
          [MacroCallParam.var (Var.ffv nextVarId)] ++
            (mintFreshRets (c := c) (nextVarId + 1) rest).2.1 := by
        simp only [mintFreshRets, heq1]
      rw [hstep]
      cases i with
      | zero => simp
      | succ j =>
          apply List.mem_append_right
          have hj := ih (nextVarId + 1) (fun pm hpm => hff pm (List.mem_cons_of_mem _ hpm)) j
            (by simpa using hi)
          have heqIdx : nextVarId + 1 + j = nextVarId + (j + 1) := by omega
          rwa [heqIdx] at hj

/-- Converse of `mintFreshAuxParams_params_mem`: every index in range (ff or bool) actually has
    a corresponding macro-call param present. -/
theorem mintFreshAuxParams_params_mem_of_index {c : ZKConfig} (nextVarId numFF numBool : Nat) :
    (∀ i, i < numFF → MacroCallParam.var (Var.ffv (nextVarId + i)) ∈
      (mintFreshAuxParams (c := c) nextVarId numFF numBool).2) ∧
    (∀ i, i < numBool → MacroCallParam.var (Var.boolv (nextVarId + numFF + i)) ∈
      (mintFreshAuxParams (c := c) nextVarId numFF numBool).2) := by
  constructor
  · intro i hi
    simp only [mintFreshAuxParams]
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨nextVarId + i, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, rfl⟩
  · intro i hi
    simp only [mintFreshAuxParams]
    apply List.mem_append_right
    exact List.mem_map.mpr
      ⟨nextVarId + numFF + i, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, rfl⟩

/-- Folding the `ffVarsOfFormula`-`.call`-shaped accumulator never loses a var already in the
    starting accumulator. -/
theorem ffVars_call_mem_preserve {c : ZKConfig} :
    ∀ (l : List (MacroCallParam c)) (init : VarSet) (v : Var), v ∈ init →
      v ∈ l.foldl (fun acc p => match p with
        | MacroCallParam.var (Var.ffv n) => acc.insert (Var.ffv n) | _ => acc) init := by
  intro l
  induction l with
  | nil => intro init v hv; exact hv
  | cons p ps ih =>
      intro init v hv
      simp only [List.foldl_cons]
      cases p with
      | var vv =>
          cases vv with
          | ffv n => exact ih (init.insert (Var.ffv n)) v (Std.TreeSet.mem_insert.mpr (Or.inr hv))
          | boolv _ => exact ih init v hv
      | const _ => exact ih init v hv

/-- If `MacroCallParam.var (Var.ffv k)` is among the params `ffVarsOfFormula`'s `.call` case
    folds over, `Var.ffv k` ends up in the result. -/
theorem mem_ffVars_call_of_mem {c : ZKConfig} :
    ∀ (l : List (MacroCallParam c)) (init : VarSet) (k : FFVar),
      MacroCallParam.var (Var.ffv k) ∈ l →
      Var.ffv k ∈ l.foldl (fun acc p => match p with
        | MacroCallParam.var (Var.ffv n) => acc.insert (Var.ffv n) | _ => acc) init := by
  intro l
  induction l with
  | nil => intro init k h; cases h
  | cons p ps ih =>
      intro init k h
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp h with heq | hmem
      · rw [← heq]
        exact ffVars_call_mem_preserve ps (init.insert (Var.ffv k)) (Var.ffv k)
          (Std.TreeSet.mem_insert.mpr (Or.inl (Var_compare_eq_iff_eq.mpr rfl)))
      · cases p with
        | var vv =>
            cases vv with
            | ffv n => exact ih (init.insert (Var.ffv n)) k hmem
            | boolv _ => exact ih init k hmem
        | const _ => exact ih init k hmem

/-- Folding the `bVarsOfFormula`-`.call`-shaped accumulator never loses a var already in the
    starting accumulator. -/
theorem bVars_call_mem_preserve {c : ZKConfig} :
    ∀ (l : List (MacroCallParam c)) (init : VarSet) (v : Var), v ∈ init →
      v ∈ l.foldl (fun acc p => match p with
        | MacroCallParam.var (Var.boolv n) => acc.insert (Var.boolv n) | _ => acc) init := by
  intro l
  induction l with
  | nil => intro init v hv; exact hv
  | cons p ps ih =>
      intro init v hv
      simp only [List.foldl_cons]
      cases p with
      | var vv =>
          cases vv with
          | boolv n => exact ih (init.insert (Var.boolv n)) v (Std.TreeSet.mem_insert.mpr (Or.inr hv))
          | ffv _ => exact ih init v hv
      | const _ => exact ih init v hv

/-- If `MacroCallParam.var (Var.boolv k)` is among the params `bVarsOfFormula`'s `.call` case
    folds over, `Var.boolv k` ends up in the result. -/
theorem mem_bVars_call_of_mem {c : ZKConfig} :
    ∀ (l : List (MacroCallParam c)) (init : VarSet) (k : BoolVar),
      MacroCallParam.var (Var.boolv k) ∈ l →
      Var.boolv k ∈ l.foldl (fun acc p => match p with
        | MacroCallParam.var (Var.boolv n) => acc.insert (Var.boolv n) | _ => acc) init := by
  intro l
  induction l with
  | nil => intro init k h; cases h
  | cons p ps ih =>
      intro init k h
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp h with heq | hmem
      · rw [← heq]
        exact bVars_call_mem_preserve ps (init.insert (Var.boolv k)) (Var.boolv k)
          (Std.TreeSet.mem_insert.mpr (Or.inl (Var_compare_eq_iff_eq.mpr rfl)))
      · cases p with
        | var vv =>
            cases vv with
            | boolv n => exact ih (init.insert (Var.boolv n)) k hmem
            | ffv _ => exact ih init k hmem
        | const _ => exact ih init k hmem

/-- The output values `mintFreshRets` mints (all-`.ff`), read back under an assignment that
    agrees with `retVals` position-for-position, `symValMatches`-match `retVals` (as scalars)
    pointwise -- the `Forall₂` companion of `mintFreshRets_ff_only_constify_eq`, used to show
    `outVals` (bound into the caller's `outs`) decode to exactly `retVals`. -/
theorem mintFreshRets_ff_only_outVals_symValMatches {c : ZKConfig} (assignment' : Assignment c) :
    ∀ (rets : List Param) (nextVarId : Nat), (∀ pm ∈ rets, pm.type = VarType.ff) →
      ∀ (retVals : List (FF c)), retVals.length = rets.length →
      (∀ i, i < rets.length → assignment'.ff (nextVarId + i) = retVals.getD i 0) →
      List.Forall₂ (symValMatches assignment')
        (mintFreshRets (c := c) nextVarId rets).2.2 (retVals.map Value.scalar) := by
  intro rets
  induction rets with
  | nil =>
      intro nextVarId _hff retVals hlen _hassign
      cases retVals with
      | nil => simp [mintFreshRets]
      | cons _ _ => simp at hlen
  | cons r rest ih =>
      intro nextVarId hff retVals hlen hassign
      cases retVals with
      | nil => simp at hlen
      | cons rv retVals =>
          have hrff : r.type = VarType.ff := hff r (List.mem_cons_self ..)
          have heq1 : mintFreshRetParam (c := c) nextVarId r.type =
              (nextVarId + 1, [MacroCallParam.var (Var.ffv nextVarId)],
                SymValue.simple (SimpleSymVal.ffvar { var := nextVarId, bits := none })) := by
            rw [hrff]; rfl
          have hstep : (mintFreshRets (c := c) nextVarId (r :: rest)).2.2 =
              SymValue.simple (SimpleSymVal.ffvar { var := nextVarId, bits := none }) ::
                (mintFreshRets (c := c) (nextVarId + 1) rest).2.2 := by
            simp only [mintFreshRets, heq1]
          rw [hstep]
          have hhead : assignment'.ff nextVarId = rv := by
            have h0 := hassign 0 (by simp)
            simpa using h0
          simp only [List.map_cons]
          refine List.Forall₂.cons ?_ ?_
          · simp only [symValMatches, simpleValMatches, hhead]
          · apply ih (nextVarId + 1) (fun pm hpm => hff pm (List.mem_cons_of_mem _ hpm)) retVals
              (by simpa using hlen)
            intro i hi
            have hstepAssign := hassign (i + 1) (by simpa using hi)
            have heqIdx : nextVarId + (i + 1) = nextVarId + 1 + i := by omega
            rw [heqIdx] at hstepAssign
            simpa using hstepAssign

/-- Array-capable mirror of `resolveSimpleExpr_defined_of_evalSimpleExprToFFValue`: if
    `evalSimpleExprToValue` succeeds on a concrete environment matching `symEnv`,
    `resolveSimpleExprToSymValue` succeeds on `symEnv` itself. Simpler than the scalar-only
    original -- no need to rule out an array-shaped result, since `resolveSimpleExprToSymValue`
    (unlike `resolveSimpleExpr`) accepts either shape. -/
theorem resolveSimpleExprToSymValue_defined_of_evalSimpleExprToValue {c : ZKConfig}
    (symEnv : SymEnv c) (s : SimpleExpr c) (env : Env c) (assignment : Assignment c)
    (hmatch : EnvMatches assignment symEnv env) (v : Value c)
    (heval : evalSimpleExprToValue env s = Except.ok v) :
    ∃ sv, resolveSimpleExprToSymValue symEnv s = Except.ok sv := by
  cases s with
  | val v' => exact ⟨SymValue.simple (.const v'), rfl⟩
  | var id =>
      simp only [evalSimpleExprToValue] at heval
      have hcontains : env.contains id :=
        contains_iff_get?_isSome env id |>.mpr ⟨v, (getVarEnv_eq_ok_iff env id v).mp heval⟩
      have hsymcontains : symEnv.contains id := (hmatch.1 id).mpr hcontains
      obtain ⟨sv, hsv⟩ := contains_iff_get?_isSome symEnv id |>.mp hsymcontains
      refine ⟨sv, ?_⟩
      simp only [resolveSimpleExprToSymValue, (getVar_eq_ok_iff symEnv id sv).mpr hsv]

/-- Array-capable mirror of `resolveSimpleExpr_vars_subset`: whatever `resolveSimpleExprToSymValue`
    resolves an expression to, its vars are already tracked by `symEnv` -- direct reuse of
    `getVar_mem_symEnvVars`, which already handles both `.simple`/`.array` shapes. -/
theorem resolveSimpleExprToSymValue_vars_subset {c : ZKConfig} (symEnv : SymEnv c)
    (s : SimpleExpr c) (sv : SymValue c) (h : resolveSimpleExprToSymValue symEnv s = Except.ok sv) :
    symValVars sv ⊆ symEnvVars symEnv := by
  cases s with
  | val v =>
      simp only [resolveSimpleExprToSymValue] at h
      injection h with h
      simp only [← h, symValVars, simpleValVars]
      exact fun v hv => absurd hv Std.TreeSet.not_mem_emptyc
  | var id =>
      simp only [resolveSimpleExprToSymValue, Corellzk2smt.SymExec.Basic.getVar] at h
      cases hget : symEnv.get? id with
      | none => rw [hget] at h; simp at h
      | some sv' =>
          rw [hget] at h
          injection h with h
          rw [← h]
          exact getVar_mem_symEnvVars symEnv id sv' hget

/-- Array-capable mirror of `resolveSimpleExpr_correct`: if `resolveSimpleExprToSymValue`
    resolves `s` under a matching `symEnv`, `evalSimpleExprToValue` succeeds on the matching
    concrete `env` with a `symValMatches`-related result. Simpler than the scalar-only original
    -- `symValMatches`/`EnvMatches`'s own per-key condition are already uniform across
    `.simple`/`.array`, so no shape case-split is needed. -/
theorem resolveSimpleExprToSymValue_correct {c : ZKConfig}
    (symEnv : SymEnv c) (s : SimpleExpr c) (env : Env c) (assignment : Assignment c)
    (sv : SymValue c) (hmatch : EnvMatches assignment symEnv env)
    (heval : resolveSimpleExprToSymValue symEnv s = Except.ok sv) :
    ∃ v, evalSimpleExprToValue env s = Except.ok v ∧ symValMatches assignment sv v := by
  cases s with
  | val v' =>
      simp only [resolveSimpleExprToSymValue] at heval
      injection heval with hv
      exact ⟨Value.scalar v', rfl, by simp [← hv, symValMatches, simpleValMatches]⟩
  | var id =>
      simp only [resolveSimpleExprToSymValue, Corellzk2smt.SymExec.Basic.getVar] at heval
      cases hget : symEnv.get? id with
      | none => rw [hget] at heval; simp at heval
      | some rest =>
          rw [hget] at heval
          simp only at heval
          injection heval with hsv
          obtain ⟨_hdom, hpoint⟩ := hmatch
          obtain ⟨vv, henv, hvv⟩ := hpoint id rest hget
          refine ⟨vv, ?_, ?_⟩
          · simp only [evalSimpleExprToValue,
              Corellzk2smt.Language.Core.Semantics.Basic.getVar, henv]
          · rw [← hsv]; exact hvv

/-- Array-capable, existence-only mirror of `resolveSimpleExprsToSymValue_of_forall`: if every
    element of `args` resolves symbolically (as either shape), `resolveSimpleExprsToSymValue`
    resolves the whole list, keeping each element's own resolved value as-is (no forced
    `.simple`-wrapping, unlike the scalar-only original). -/
theorem resolveSimpleExprsToSymValue_of_forall_general {c : ZKConfig} (symEnv : SymEnv c) :
    ∀ (args : List (SimpleExpr c)),
      (∀ s ∈ args, ∃ sv : SymValue c, resolveSimpleExprToSymValue symEnv s = Except.ok sv) →
      ∃ argSymVals : List (SymValue c), argSymVals.length = args.length ∧
        List.Forall₂ (fun s sv => resolveSimpleExprToSymValue symEnv s = Except.ok sv)
          args argSymVals ∧
        resolveSimpleExprsToSymValue symEnv args = Except.ok argSymVals := by
  intro args
  induction args with
  | nil => intro _; exact ⟨[], rfl, List.Forall₂.nil, rfl⟩
  | cons a args ih =>
      intro hall
      obtain ⟨sv, hsv⟩ := hall a (List.mem_cons_self ..)
      obtain ⟨svs, hlen, hforall, heq⟩ := ih (fun s hs => hall s (List.mem_cons_of_mem _ hs))
      refine ⟨sv :: svs, by simp [hlen], List.Forall₂.cons hsv hforall, ?_⟩
      simp only [resolveSimpleExprsToSymValue] at heq ⊢
      rw [List.mapM_cons, hsv, heq]
      rfl

/-- Converse of `resolveSimpleExprsToSymValue_of_forall_general`: if `resolveSimpleExprsToSymValue`
    (i.e. `args.mapM (resolveSimpleExprToSymValue symEnv)`) succeeds, every element resolved
    individually to the corresponding output -- lets `seFuncCall_correct` read the per-element
    resolution facts (and hence arity/shape) straight back out of `seFuncCall`'s own success,
    instead of needing them supplied as a separate hypothesis. -/
theorem resolveSimpleExprsToSymValue_forall_of_ok {c : ZKConfig} (symEnv : SymEnv c) :
    ∀ (args : List (SimpleExpr c)) (argSymVals : List (SymValue c)),
      resolveSimpleExprsToSymValue symEnv args = Except.ok argSymVals →
      List.Forall₂ (fun s sv => resolveSimpleExprToSymValue symEnv s = Except.ok sv)
        args argSymVals := by
  intro args
  induction args with
  | nil =>
      intro argSymVals heq
      simp only [resolveSimpleExprsToSymValue, List.mapM_nil, pure, Except.pure,
        Except.ok.injEq] at heq
      rw [← heq]
      exact List.Forall₂.nil
  | cons a args ih =>
      intro argSymVals heq
      simp only [resolveSimpleExprsToSymValue] at heq
      rw [List.mapM_cons] at heq
      cases hsv : resolveSimpleExprToSymValue symEnv a with
      | error e => rw [hsv] at heq; simp [Bind.bind, Except.bind] at heq
      | ok sv =>
          rw [hsv] at heq
          simp only [Bind.bind, Except.bind] at heq
          cases hrest : List.mapM (resolveSimpleExprToSymValue symEnv) args with
          | error e => rw [hrest] at heq; simp at heq
          | ok svs =>
              rw [hrest] at heq
              simp only [pure, Except.pure, Except.ok.injEq] at heq
              rw [← heq]
              exact List.Forall₂.cons hsv (ih svs hrest)

/-- Array-capable, list-level mirror of `list_resolveSimpleExpr_correct`. -/
theorem list_resolveSimpleExprToSymValue_correct {c : ZKConfig} (symEnv : SymEnv c) (env : Env c)
    (assignment : Assignment c) (hmatch : EnvMatches assignment symEnv env) :
    ∀ (args : List (SimpleExpr c)) (argSymVals : List (SymValue c)),
      List.Forall₂ (fun s sv => resolveSimpleExprToSymValue symEnv s = Except.ok sv)
        args argSymVals →
      ∃ vs : List (Value c), evalSimpleExprsToValue env args = Except.ok vs ∧
        List.Forall₂ (symValMatches assignment) argSymVals vs := by
  intro args argSymVals h
  induction h with
  | nil => exact ⟨[], rfl, List.Forall₂.nil⟩
  | cons hd tl ih =>
      obtain ⟨v, hv, hvm⟩ := resolveSimpleExprToSymValue_correct symEnv _ env assignment _
        hmatch hd
      obtain ⟨vs, hvs_eq, hvs_forall⟩ := ih
      refine ⟨v :: vs, ?_, List.Forall₂.cons hvm hvs_forall⟩
      simp only [evalSimpleExprsToValue] at hvs_eq ⊢
      rw [List.mapM_cons, hv, hvs_eq]
      rfl

/-- If a concrete value's shape matches a declared type (`ensureCorrectType`) and it
    `symValMatches` a symbolic value, that symbolic value's own shape matches the same declared
    type (`symValueMatchesType`) -- bridges the concrete-side "well-typed" hypotheses
    (`ValuesMatchParams`) to the symbolic-side shape condition `flattenArgVals_eq` needs. -/
theorem symValueMatchesType_of_symValMatches {c : ZKConfig} (assignment : Assignment c)
    (sv : SymValue c) (v : Value c) (hm : symValMatches assignment sv v)
    (t : VarType) (ht : ensureCorrectType v t = Except.ok ()) :
    symValueMatchesType sv t := by
  cases t with
  | ff =>
      cases v with
      | array _ => simp [ensureCorrectType] at ht
      | scalar _ =>
          cases sv with
          | array _ => simp only [symValMatches] at hm
          | simple _ => trivial
  | array n =>
      cases v with
      | scalar _ => simp [ensureCorrectType] at ht
      | array varr =>
          cases sv with
          | simple _ => simp only [symValMatches] at hm
          | array arr =>
              simp only [ensureCorrectType] at ht
              by_cases hsize : varr.size = n
              · simp only [symValueMatchesType]
                simp only [symValMatches] at hm
                have hlen := hm.length_eq
                rw [Array.length_toList, Array.length_toList] at hlen
                omega
              · simp [hsize] at ht

/-- Generic `List.Forall₂` "chain through a shared middle list" combinator: given `R`-related
    `la`/`lb` and `S`-related `lb`/`lc`, produce a `T`-related `la`/`lc` fact from any pointwise
    combining rule -- used to chain `ValuesMatchParams` (params ~ concrete vs) through
    `symValMatches` (argSymVals ~ vs) to get the symbolic-side shape-match `flattenArgVals_eq`
    needs (params ~ argSymVals). -/
theorem forall2_chain {α β γ : Type} {R : α → β → Prop} {S : β → γ → Prop} {T : α → γ → Prop}
    (hcombine : ∀ a b g, R a b → S b g → T a g) :
    ∀ {la : List α} {lb : List β} {lc : List γ},
      List.Forall₂ R la lb → List.Forall₂ S lb lc → List.Forall₂ T la lc := by
  intro la lb lc h1
  induction h1 generalizing lc with
  | nil => intro h2; cases h2; exact List.Forall₂.nil
  | cons hab htl ih =>
      intro h2
      cases h2 with
      | cons hbc htl2 => exact List.Forall₂.cons (hcombine _ _ _ hab hbc) (ih htl2)

/-- Generic `List.Forall₂` flip: relatedness is symmetric under swapping which relation's
    argument order is used. Needed since `forall2_chain`'s natural output order
    (`argSymVals ~ fspec.params`) is the reverse of what `flattenArgVals_eq` wants
    (`fspec.params ~ argSymVals`). -/
theorem forall2_flip {α β : Type} {R : α → β → Prop} :
    ∀ {la : List α} {lb : List β}, List.Forall₂ R la lb → List.Forall₂ (fun b a => R a b) lb la := by
  intro la lb h
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hd tl ih => exact List.Forall₂.cons hd ih

/-- If `evalSimpleExprsToValue` (the whole-list `mapM`) succeeds, each individual element's own
    `evalSimpleExprToValue` succeeds too -- needed because the new `hargs_defined`'s natural
    shape is whole-list, but `resolveSimpleExprsToSymValue_of_forall_general` needs per-element
    existence. -/
theorem evalSimpleExprToValue_of_evalSimpleExprsToValue {c : ZKConfig} (env : Env c) :
    ∀ (args : List (SimpleExpr c)) (vs : List (Value c)),
      evalSimpleExprsToValue env args = Except.ok vs →
      ∀ s ∈ args, ∃ v, evalSimpleExprToValue env s = Except.ok v := by
  intro args
  induction args with
  | nil => intro vs _h s hs; simp at hs
  | cons a rest ih =>
      intro vs h s hs
      simp only [evalSimpleExprsToValue, List.mapM_cons] at h
      cases ha : evalSimpleExprToValue env a with
      | error e =>
          rw [ha] at h
          simp only [Bind.bind, Except.bind] at h
          exact absurd h (by simp)
      | ok va =>
          rw [ha] at h
          cases hrest : rest.mapM (evalSimpleExprToValue env) with
          | error e =>
              rw [hrest] at h
              simp only [Bind.bind, Except.bind] at h
              exact absurd h (by simp)
          | ok vrest =>
              rcases List.mem_cons.mp hs with heq | hmem
              · exact ⟨va, heq ▸ ha⟩
              · exact ih vrest hrest s hmem

/-- The number of raw `FF c` elements `flattenValueToFF` produces for a value matches its
    declared type's `typeSize` -- length companion to `flattenValueParams`/`flattenValueToFF`'s
    shape, needed to know a block's own local index range. -/
theorem flattenValueToFF_length {c : ZKConfig} (v : Value c) (t : VarType)
    (ht : ensureCorrectType v t = Except.ok ()) :
    (flattenValueToFF v).length = typeSize t := by
  cases t with
  | ff =>
      cases v with
      | scalar x => rfl
      | array _ => simp [ensureCorrectType] at ht
  | array n =>
      cases v with
      | scalar _ => simp [ensureCorrectType] at ht
      | array arr =>
          have hsize : arr.size = n := by
            simp only [ensureCorrectType] at ht
            by_contra hne
            simp [hne] at ht
          simp only [flattenValueToFF, typeSize, Array.length_toList, hsize]

/-- Reading `flattenValuesToFF (v :: vs)` at a position within `v`'s own block agrees with
    reading `v`'s own `flattenValueToFF` directly there. -/
theorem flattenValuesToFF_getD_head {c : ZKConfig} (v : Value c) (vs : List (Value c)) (i : Nat)
    (hi : i < (flattenValueToFF v).length) :
    (flattenValuesToFF (v :: vs)).getD i 0 = (flattenValueToFF v).getD i 0 := by
  simp only [flattenValuesToFF, List.map_cons, List.flatten_cons]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

/-- Reading `flattenValuesToFF (v :: vs)` at a position past `v`'s own block agrees with reading
    `vs`'s own `flattenValuesToFF` at the shifted-back position. -/
theorem flattenValuesToFF_getD_tail {c : ZKConfig} (v : Value c) (vs : List (Value c)) (i : Nat)
    (hi : (flattenValueToFF v).length ≤ i) :
    (flattenValuesToFF (v :: vs)).getD i 0 =
      (flattenValuesToFF vs).getD (i - (flattenValueToFF v).length) 0 := by
  simp only [flattenValuesToFF, List.map_cons, List.flatten_cons]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

/-- `flattenValuesParams` (the `MacroCallParam`-wrapped view) is exactly `flattenValuesToFF`
    (the raw-`FF c` view) with every element wrapped as a `.const` -- bridges `H_specCorrect`'s
    formula-construction view of `retVals` to the assignment-construction view. -/
theorem flattenValuesParams_eq_map {c : ZKConfig} :
    ∀ (vs : List (Value c)),
      flattenValuesParams vs =
        (flattenValuesToFF vs).map (fun x => MacroCallParam.const (Const.ffc x)) := by
  intro vs
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      have hstep1 : flattenValuesParams (v :: vs) = flattenValueParams v ++ flattenValuesParams vs := by
        simp only [flattenValuesParams, List.map_cons, List.flatten_cons]
      have hstep2 : flattenValuesToFF (v :: vs) = flattenValueToFF v ++ flattenValuesToFF vs := by
        simp only [flattenValuesToFF, List.map_cons, List.flatten_cons]
      rw [hstep1, hstep2, List.map_append, ih]
      congr 1
      cases v with
      | scalar x => rfl
      | array arr => simp [flattenValueParams, flattenValueToFF]

/-- Generic "pointwise-related same-length lists are `Forall₂`-related" combinator. -/
theorem forall2_of_getD_pointwise {α β : Type} (R : α → β → Prop) (da : α) (db : β) :
    ∀ (la : List α) (lb : List β), la.length = lb.length →
      (∀ i, i < la.length → R (la.getD i da) (lb.getD i db)) →
      List.Forall₂ R la lb := by
  intro la
  induction la with
  | nil =>
      intro lb hlen _
      cases lb with
      | nil => exact List.Forall₂.nil
      | cons _ _ => simp at hlen
  | cons a la ih =>
      intro lb hlen hpt
      cases lb with
      | nil => simp at hlen
      | cons b lb =>
          refine List.Forall₂.cons ?_ (ih lb (by simpa using hlen) ?_)
          · have h0 := hpt 0 (by simp)
            simpa using h0
          · intro i hi
            have hs := hpt (i + 1) (by simp only [List.length_cons]; omega)
            simpa using hs

/-- A single fresh ret's symbolic value (`freshRetSymValue`) `symValMatches` a concrete value of
    the matching shape, given the assignment reads back exactly that value's own flattened `FF`
    elements over its block. -/
theorem freshRetSymValue_symValMatches {c : ZKConfig} (assignment' : Assignment c)
    (offset : Nat) (type : VarType) (v : Value c) (ht : ensureCorrectType v type = Except.ok ())
    (hrange : ∀ i, i < typeSize type → assignment'.ff (offset + i) =
      (flattenValueToFF v).getD i 0) :
    symValMatches assignment' (freshRetSymValue (c := c) offset type) v := by
  cases type with
  | ff =>
      cases v with
      | array _ => simp [ensureCorrectType] at ht
      | scalar x =>
          simp only [freshRetSymValue, symValMatches, simpleValMatches]
          have h0 := hrange 0 (by simp [typeSize])
          simpa [flattenValueToFF] using h0
  | array n =>
      cases v with
      | scalar _ => simp [ensureCorrectType] at ht
      | array arr =>
          have hsize : arr.size = n := by
            simp only [ensureCorrectType] at ht
            by_contra hne
            simp [hne] at ht
          simp only [freshRetSymValue, symValMatches]
          rw [List.toList_toArray]
          apply forall2_of_getD_pointwise (simpleValMatches assignment')
            (SimpleSymVal.const 0) 0
          · simp only [List.length_map, List.length_range]
            rw [← hsize, Array.length_toList]
          · intro i hi
            simp only [List.length_map, List.length_range] at hi
            rw [range_map_getD _ _ i hi (SimpleSymVal.const 0)]
            simp only [simpleValMatches]
            have h1 := hrange i (by simp only [typeSize]; exact hi)
            simpa [flattenValueToFF] using h1

/-- Constifying a single fresh ret's macro-call params (`mintFreshRetParam`) under an assignment
    that reads back a matching value's own flattened `FF` elements recovers exactly that value's
    `flattenValueParams`. -/
theorem mintFreshRetParam_constify_eq {c : ZKConfig} (assignment' : Assignment c)
    (nextVarId : Nat) (type : VarType) (v : Value c) (ht : ensureCorrectType v type = Except.ok ())
    (hrange : ∀ i, i < typeSize type → assignment'.ff (nextVarId + i) =
      (flattenValueToFF v).getD i 0) :
    (mintFreshRetParam (c := c) nextVarId type).2.1.map (constifyMacroCallParam assignment') =
      flattenValueParams v := by
  obtain ⟨_, hps_eq, _⟩ := mintFreshRetParam_eq (c := c) nextVarId type
  rw [hps_eq]
  cases type with
  | ff =>
      cases v with
      | array _ => simp [ensureCorrectType] at ht
      | scalar x =>
          have h0 := hrange 0 (by simp [typeSize])
          simp only [Nat.add_zero, flattenValueToFF, List.getD_cons_zero] at h0
          simp only [typeSize, List.range_one, List.map_cons, List.map_nil, constifyMacroCallParam,
            flattenValueParams, Nat.add_zero]
          rw [h0]
  | array n =>
      cases v with
      | scalar _ => simp [ensureCorrectType] at ht
      | array arr =>
          have hsize : arr.size = n := by
            simp only [ensureCorrectType] at ht
            by_contra hne
            simp [hne] at ht
          simp only [typeSize, List.map_map, Function.comp_def]
          rw [range_map_eq_of_pointwise n nextVarId arr.toList
            (by rw [Array.length_toList]; exact hsize)
            (fun k => constifyMacroCallParam assignment' (MacroCallParam.var (Var.ffv k)))
            (fun x => MacroCallParam.const (Const.ffc x)) 0
            (fun i hi => by
              simp only [constifyMacroCallParam]
              have h1 := hrange i (by simp only [typeSize]; exact hi)
              simpa [flattenValueToFF] using h1)]
          simp [flattenValueParams]

/-- List-level generalization of `mintFreshRets_ff_only_constify_eq`: constifying
    `mintFreshRets`'s macro-call params under an assignment that reads back `retVals`'s own
    flattened `FF` elements over the whole ret list's block recovers exactly `retVals`'s
    `flattenValuesParams`. -/
theorem mintFreshRets_constify_eq {c : ZKConfig} (assignment' : Assignment c) :
    ∀ (rets : List Param) (nextVarId : Nat) (retVals : List (Value c)),
      ValuesMatchParams retVals rets →
      (∀ i, i < totalParamSize rets → assignment'.ff (nextVarId + i) =
        (flattenValuesToFF retVals).getD i 0) →
      ((mintFreshRets (c := c) nextVarId rets).2.1).map (constifyMacroCallParam assignment') =
        flattenValuesParams retVals := by
  intro rets
  induction rets with
  | nil =>
      intro nextVarId retVals hmatch _hrange
      cases hmatch
      rfl
  | cons r rs ih =>
      intro nextVarId retVals hmatch hrange
      cases hmatch with
      | cons hd tl =>
          rename_i rv retVals'
          have ht : ensureCorrectType rv r.type = Except.ok () := hd
          have hlen_rv : (flattenValueToFF rv).length = typeSize r.type :=
            flattenValueToFF_length rv r.type ht
          have hps : paramSize r = typeSize r.type := rfl
          have hrv_range : ∀ i, i < typeSize r.type →
              assignment'.ff (nextVarId + i) = (flattenValueToFF rv).getD i 0 := by
            intro i hi
            have h1 := hrange i (by rw [totalParamSize_cons]; omega)
            rw [h1, flattenValuesToFF_getD_head rv retVals' i (by omega)]
          have hrest_range : ∀ i, i < totalParamSize rs →
              assignment'.ff ((mintFreshRetParam (c := c) nextVarId r.type).1 + i) =
                (flattenValuesToFF retVals').getD i 0 := by
            intro i hi
            obtain ⟨hnv1_eq, _, _⟩ := mintFreshRetParam_eq (c := c) nextVarId r.type
            have heqidx : (mintFreshRetParam (c := c) nextVarId r.type).1 + i =
                nextVarId + (typeSize r.type + i) := by rw [hnv1_eq]; omega
            rw [heqidx]
            have h1 := hrange (typeSize r.type + i) (by rw [totalParamSize_cons]; omega)
            rw [h1, flattenValuesToFF_getD_tail rv retVals' (typeSize r.type + i) (by omega)]
            congr 1
            omega
          rw [mintFreshRets_cons]
          simp only [List.map_append]
          rw [mintFreshRetParam_constify_eq assignment' nextVarId r.type rv ht hrv_range,
            ih (mintFreshRetParam (c := c) nextVarId r.type).1 retVals' tl hrest_range]
          simp [flattenValuesParams]

/-- List-level generalization of `mintFreshRets_ff_only_outVals_symValMatches`: `mintFreshRets`'s
    output values `symValMatches` `retVals` pointwise, given the assignment reads back
    `retVals`'s own flattened `FF` elements over the whole ret list's block. -/
theorem mintFreshRets_outVals_symValMatches {c : ZKConfig} (assignment' : Assignment c) :
    ∀ (rets : List Param) (nextVarId : Nat) (retVals : List (Value c)),
      ValuesMatchParams retVals rets →
      (∀ i, i < totalParamSize rets → assignment'.ff (nextVarId + i) =
        (flattenValuesToFF retVals).getD i 0) →
      List.Forall₂ (symValMatches assignment')
        (mintFreshRets (c := c) nextVarId rets).2.2 retVals := by
  intro rets
  induction rets with
  | nil =>
      intro nextVarId retVals hmatch _hrange
      cases hmatch
      exact List.Forall₂.nil
  | cons r rs ih =>
      intro nextVarId retVals hmatch hrange
      cases hmatch with
      | cons hd tl =>
          rename_i rv retVals'
          have ht : ensureCorrectType rv r.type = Except.ok () := hd
          have hlen_rv : (flattenValueToFF rv).length = typeSize r.type :=
            flattenValueToFF_length rv r.type ht
          have hps : paramSize r = typeSize r.type := rfl
          have hrv_range : ∀ i, i < typeSize r.type →
              assignment'.ff (nextVarId + i) = (flattenValueToFF rv).getD i 0 := by
            intro i hi
            have h1 := hrange i (by rw [totalParamSize_cons]; omega)
            rw [h1, flattenValuesToFF_getD_head rv retVals' i (by omega)]
          have hrest_range : ∀ i, i < totalParamSize rs →
              assignment'.ff ((mintFreshRetParam (c := c) nextVarId r.type).1 + i) =
                (flattenValuesToFF retVals').getD i 0 := by
            intro i hi
            obtain ⟨hnv1_eq, _, _⟩ := mintFreshRetParam_eq (c := c) nextVarId r.type
            have heqidx : (mintFreshRetParam (c := c) nextVarId r.type).1 + i =
                nextVarId + (typeSize r.type + i) := by rw [hnv1_eq]; omega
            rw [heqidx]
            have h1 := hrange (typeSize r.type + i) (by rw [totalParamSize_cons]; omega)
            rw [h1, flattenValuesToFF_getD_tail rv retVals' (typeSize r.type + i) (by omega)]
            congr 1
            omega
          rw [mintFreshRets_cons]
          simp only
          refine List.Forall₂.cons ?_ (ih (mintFreshRetParam (c := c) nextVarId r.type).1
            retVals' tl hrest_range)
          obtain ⟨_, _, hsv_eq⟩ := mintFreshRetParam_eq (c := c) nextVarId r.type
          rw [hsv_eq]
          exact freshRetSymValue_symValMatches assignment' nextVarId r.type rv ht hrv_range

/-- Array-capable generalization of `constify_input_params_eq`: constifying the flattened
    argument segment (`flattenSymValuesParams argSymVals`) under an assignment that agrees with
    `symEnv` on `symEnv`'s own tracked vars recovers exactly the concrete `vs`'s own
    `flattenValuesParams`, given `argSymVals` `symValMatches` `vs` pointwise. Reuses
    `constify_input_params_eq` itself for the `.array` case's element-wise reasoning (an array's
    own elements are still plain `SimpleSymVal`/`FF` pairs). -/
theorem constify_input_symvalues_eq {c : ZKConfig} (symEnv : SymEnv c)
    (assignment assignment' : Assignment c)
    (hagree : ∀ n, Var.ffv n ∈ symEnvVars symEnv → assignment'.ff n = assignment.ff n) :
    ∀ (argSymVals : List (SymValue c)) (vs : List (Value c)),
      (∀ sv ∈ argSymVals, symValVars sv ⊆ symEnvVars symEnv) →
      List.Forall₂ (symValMatches assignment) argSymVals vs →
      (flattenSymValuesParams argSymVals).map (constifyMacroCallParam assignment') =
        flattenValuesParams vs := by
  intro argSymVals
  induction argSymVals with
  | nil => intro vs _ hforall; cases hforall; rfl
  | cons sv svs ih =>
      intro vs hvars hforall
      cases vs with
      | nil => cases hforall
      | cons v vs =>
          obtain ⟨hd, tl⟩ := List.forall₂_cons.mp hforall
          have hsvvars : symValVars sv ⊆ symEnvVars symEnv := hvars sv (List.mem_cons_self ..)
          have hrest : ∀ sv' ∈ svs, symValVars sv' ⊆ symEnvVars symEnv :=
            fun sv' hsv' => hvars sv' (List.mem_cons_of_mem _ hsv')
          have hstep1 : flattenSymValuesParams (sv :: svs) =
              flattenSymValueParams sv ++ flattenSymValuesParams svs := by
            simp only [flattenSymValuesParams, List.map_cons, List.flatten_cons]
          have hstep2 : flattenValuesParams (v :: vs) =
              flattenValueParams v ++ flattenValuesParams vs := by
            simp only [flattenValuesParams, List.map_cons, List.flatten_cons]
          rw [hstep1, hstep2, List.map_append, ih vs hrest tl]
          congr 1
          cases sv with
          | simple sv' =>
              cases v with
              | array _ => simp only [symValMatches] at hd
              | scalar v' =>
                  cases sv' with
                  | const cv =>
                      simp only [symValMatches, simpleValMatches] at hd
                      simp [flattenSymValueParams, simpleSymValToMacroCallParam,
                        constifyMacroCallParam, flattenValueParams, hd]
                  | ffvar vbr =>
                      simp only [symValMatches, simpleValMatches] at hd
                      have hmem : Var.ffv vbr.var ∈ symEnvVars symEnv :=
                        hsvvars (Var.ffv vbr.var) (by simp [symValVars, simpleValVars])
                      simp [flattenSymValueParams, simpleSymValToMacroCallParam,
                        constifyMacroCallParam, flattenValueParams, hagree vbr.var hmem, hd]
          | array arr =>
              cases v with
              | scalar _ => simp only [symValMatches] at hd
              | array varr =>
                  simp only [symValMatches] at hd
                  have harrvars : ∀ sv' ∈ arr.toList, simpleValVars sv' ⊆ symEnvVars symEnv := by
                    intro sv' hsv'
                    have hsub := symValVars_array_mem_subset arr sv' hsv'
                    exact fun x hx => hsvvars x (hsub x hx)
                  have hres := constify_input_params_eq symEnv assignment assignment' hagree
                    arr.toList varr.toList harrvars hd
                  simp only [flattenSymValueParams, flattenValueParams]
                  exact hres

/-- Converse of `symValueMatchesType_of_symValMatches`: if a symbolic value's shape matches a
    declared type and it `symValMatches` a concrete value, that concrete value's own shape
    matches the same declared type -- needed to transfer the symbolic-side shape fact
    (`hshape`, from `hargs_defined`) onto the concrete `vs`/`retVals` `hspec_retsShape`/
    `H_specCorrect` actually need. -/
theorem ensureCorrectType_of_symValueMatchesType_symValMatches {c : ZKConfig}
    (assignment : Assignment c) (sv : SymValue c) (v : Value c) (type : VarType)
    (hshape : symValueMatchesType sv type) (hm : symValMatches assignment sv v) :
    ensureCorrectType v type = Except.ok () := by
  cases type with
  | ff =>
      cases sv with
      | array _ => simp only [symValueMatchesType] at hshape
      | simple _ =>
          cases v with
          | array _ => simp only [symValMatches] at hm
          | scalar _ => rfl
  | array n =>
      cases sv with
      | simple _ => simp only [symValueMatchesType] at hshape
      | array arr =>
          simp only [symValueMatchesType] at hshape
          cases v with
          | scalar _ => simp only [symValMatches] at hm
          | array varr =>
              simp only [symValMatches] at hm
              have hlen := hm.length_eq
              rw [Array.length_toList, Array.length_toList] at hlen
              simp only [ensureCorrectType]
              rw [if_pos (by omega)]

/-- Every macro-call param `flattenValuesParams` produces is a `.const` -- unconditionally, by
    construction (regardless of the underlying value's `.scalar`/`.array` shape). -/
theorem flattenValuesParams_all_const {c : ZKConfig} (vs : List (Value c)) :
    ∀ mcp ∈ flattenValuesParams vs, ∃ cv, mcp = MacroCallParam.const cv := by
  intro mcp hmcp
  simp only [flattenValuesParams, List.mem_flatten] at hmcp
  obtain ⟨l, hl, hmcpl⟩ := hmcp
  obtain ⟨v, hv, hleq⟩ := List.mem_map.mp hl
  rw [← hleq] at hmcpl
  cases v with
  | scalar x =>
      simp only [flattenValueParams, List.mem_singleton] at hmcpl
      exact ⟨Const.ffc x, hmcpl⟩
  | array arr =>
      simp only [flattenValueParams] at hmcpl
      obtain ⟨x, _, hxeq⟩ := List.mem_map.mp hmcpl
      exact ⟨Const.ffc x, hxeq.symm⟩

/-- Reconstruct a single concrete value of a given declared shape by reading `f`'s raw `FF`
    output starting at `offset` -- the inverse direction of `flattenValueToFF`, used in
    `hcomplete` to build a witness `retVals : List (Value c)` from a bare assignment. -/
def reconstructValue {c : ZKConfig} (f : Nat → FF c) (offset : Nat) (type : VarType) : Value c :=
  match type with
  | .ff => Value.scalar (f offset)
  | .array n => Value.array ((List.range n).map (fun i => f (offset + i))).toArray

/-- `reconstructValue`, for a whole `rets` list -- one value per ret, laid out contiguously in
    program order (mirroring every other "flattened blocks" abstraction this file uses). -/
def reconstructValues {c : ZKConfig} (f : Nat → FF c) : List Param → Nat → List (Value c)
  | [], _ => []
  | r :: rs, offset => reconstructValue f offset r.type :: reconstructValues f rs (offset + paramSize r)

theorem reconstructValue_matches {c : ZKConfig} (f : Nat → FF c) (offset : Nat) (type : VarType) :
    ensureCorrectType (reconstructValue f offset type) type = Except.ok () := by
  cases type with
  | ff => rfl
  | array n => simp [reconstructValue, ensureCorrectType]

theorem reconstructValues_matches {c : ZKConfig} (f : Nat → FF c) :
    ∀ (rets : List Param) (offset : Nat),
      ValuesMatchParams (reconstructValues f rets offset) rets := by
  intro rets
  induction rets with
  | nil => intro offset; exact List.Forall₂.nil
  | cons r rs ih =>
      intro offset
      exact List.Forall₂.cons (reconstructValue_matches f offset r.type) (ih (offset + paramSize r))

theorem reconstructValues_length {c : ZKConfig} (f : Nat → FF c) :
    ∀ (rets : List Param) (offset : Nat), (reconstructValues f rets offset).length = rets.length := by
  intro rets
  induction rets with
  | nil => intro offset; rfl
  | cons r rs ih => intro offset; simp only [reconstructValues, List.length_cons, ih]

theorem reconstructValue_flattenToFF {c : ZKConfig} (f : Nat → FF c) (offset : Nat) (type : VarType) :
    flattenValueToFF (reconstructValue f offset type) =
      (List.range (typeSize type)).map (fun i => f (offset + i)) := by
  cases type with
  | ff => simp [reconstructValue, flattenValueToFF, typeSize]
  | array n => simp [reconstructValue, flattenValueToFF, typeSize, List.toList_toArray]

theorem reconstructValues_flattenToFF {c : ZKConfig} (f : Nat → FF c) :
    ∀ (rets : List Param) (offset : Nat),
      flattenValuesToFF (reconstructValues f rets offset) =
        (List.range (totalParamSize rets)).map (fun i => f (offset + i)) := by
  intro rets
  induction rets with
  | nil => intro offset; rfl
  | cons r rs ih =>
      intro offset
      have hstep : flattenValuesToFF (reconstructValues f (r :: rs) offset) =
          flattenValueToFF (reconstructValue f offset r.type) ++
            flattenValuesToFF (reconstructValues f rs (offset + paramSize r)) := by
        simp only [reconstructValues, flattenValuesToFF, List.map_cons, List.flatten_cons]
      have hps : paramSize r = typeSize r.type := rfl
      rw [hstep, reconstructValue_flattenToFF, ih (offset + paramSize r), totalParamSize_cons,
        List.range_add, List.map_append, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp]
      congr 1
      omega

/-- Converse of `reconstructValue_flattenToFF`: if `f`'s raw output at `offset`'s own block
    already reads back `v`'s own flattened elements, reconstructing from `f` reproduces `v`
    itself exactly -- the roundtrip fact tying a *constructed* assignment (`buildAssign`) back to
    the concrete value it was built from, needed since `seExecProg_call_complete` has to show its
    witness assignment's own readout matches the `argVals`/`retVals` it started from. -/
theorem reconstructValue_eq_of_matches {c : ZKConfig} (f : Nat → FF c) (v : Value c) (offset : Nat)
    (type : VarType) (ht : ensureCorrectType v type = Except.ok ())
    (hf : ∀ i, i < typeSize type → f (offset + i) = (flattenValueToFF v).getD i 0) :
    reconstructValue f offset type = v := by
  cases type with
  | ff =>
      cases v with
      | scalar x =>
          have h0 := hf 0 (by simp [typeSize])
          simp only [flattenValueToFF, List.getD_cons_zero, Nat.add_zero] at h0
          simp only [reconstructValue, h0]
      | array _ => simp [ensureCorrectType] at ht
  | array n =>
      cases v with
      | scalar _ => simp [ensureCorrectType] at ht
      | array arr =>
          have hsize : arr.size = n := by
            simp only [ensureCorrectType] at ht
            by_contra hne
            simp [hne] at ht
          have hlist : (List.range n).map (fun i => f (offset + i)) = arr.toList := by
            apply List.ext_getElem
            · simp [hsize]
            · intro i h1 h2
              simp only [List.getElem_map, List.getElem_range]
              have hi_n : i < n := by simpa using h1
              rw [hf i (by simpa [typeSize] using hi_n)]
              simp only [flattenValueToFF]
              exact (List.getElem_eq_getD _).symm
          simp only [reconstructValue, hlist, Array.toArray_toList]

/-- `reconstructValues`, plural version of `reconstructValue_eq_of_matches`. -/
theorem reconstructValues_eq_of_matches {c : ZKConfig} (f : Nat → FF c) :
    ∀ (vs : List (Value c)) (params : List Param) (offset : Nat),
      ValuesMatchParams vs params →
      (∀ i, i < totalParamSize params → f (offset + i) = (flattenValuesToFF vs).getD i 0) →
      reconstructValues f params offset = vs := by
  intro vs params offset hmatch
  induction hmatch generalizing offset with
  | nil => intro _; rfl
  | cons hd tl ih =>
      rename_i v p vs' params'
      intro hf
      have hd_len : (flattenValueToFF v).length = typeSize p.type :=
        flattenValueToFF_length v p.type hd
      have hps : paramSize p = typeSize p.type := rfl
      have hv : reconstructValue f offset p.type = v := by
        apply reconstructValue_eq_of_matches f v offset p.type hd
        intro i hi
        have hi_total : i < totalParamSize (p :: params') := by
          rw [totalParamSize_cons]; omega
        rw [hf i hi_total, flattenValuesToFF_getD_head v vs' i (by rw [hd_len]; exact hi)]
      have hrest : reconstructValues f params' (offset + paramSize p) = vs' := by
        apply ih
        intro i hi
        have hi_total : paramSize p + i < totalParamSize (p :: params') := by
          rw [totalParamSize_cons]; omega
        have heq := hf (paramSize p + i) hi_total
        rw [show offset + (paramSize p + i) = offset + paramSize p + i from by omega] at heq
        rw [heq]
        have hps : paramSize p = (flattenValueToFF v).length := hd_len.symm
        rw [flattenValuesToFF_getD_tail v vs' (paramSize p + i) (by rw [← hps]; omega)]
        congr 1
        omega
      simp only [reconstructValues, hv, hrest]

/-- Every var mentioned by a single fresh ret's symbolic value (`freshRetSymValue`) is a fresh
    `.ffv` strictly within `[start, start + typeSize type)` -- generalizes "the fresh value IS a
    specific `.ffv`" (only true for `.ff`) to "every var it *mentions* is in range" (true
    regardless of shape, since an `.array`-shaped fresh value mentions several vars, not one). -/
theorem symValVars_freshRetSymValue_below {c : ZKConfig} (start : Nat) (type : VarType) :
    ∀ v ∈ symValVars (freshRetSymValue (c := c) start type),
      ∃ n, v = Var.ffv n ∧ start ≤ n ∧ n < start + typeSize type := by
  cases type with
  | ff =>
      intro v hv
      simp only [freshRetSymValue, symValVars, simpleValVars] at hv
      rcases Std.TreeSet.mem_insert.mp hv with heq | hmem
      · have hn_eq : v = Var.ffv start := (Var_compare_eq_iff_eq.mp heq).symm
        have hlt : start < start + typeSize VarType.ff := by simp only [typeSize]; omega
        exact ⟨start, hn_eq, le_refl _, hlt⟩
      · exact absurd hmem Std.TreeSet.not_mem_emptyc
  | array size =>
      intro v hv
      simp only [freshRetSymValue, symValVars] at hv
      rw [← Array.foldl_toList, List.toList_toArray] at hv
      rcases foldl_union_mem_elim simpleValVars _ emptyVarSet v hv with hcon | ⟨x, hxmem, hvx⟩
      · exact absurd hcon Std.TreeSet.not_mem_emptyc
      · obtain ⟨i, hirange, hxeq⟩ := List.mem_map.mp hxmem
        rw [← hxeq] at hvx
        simp only [simpleValVars] at hvx
        rcases Std.TreeSet.mem_insert.mp hvx with heq | hmem
        · have hi := List.mem_range.mp hirange
          have hn_eq : v = Var.ffv (start + i) := (Var_compare_eq_iff_eq.mp heq).symm
          have hle : start ≤ start + i := by omega
          have hlt : start + i < start + typeSize (VarType.array size) := by
            simp only [typeSize]; omega
          exact ⟨start + i, hn_eq, hle, hlt⟩
        · exact absurd hmem Std.TreeSet.not_mem_emptyc

/-- Every var mentioned by any of `mintFreshRets`'s output values is a fresh `.ffv` strictly
    within `[nextVarId, (mintFreshRets nextVarId rets).1)` -- generalizes the old FF-only
    `mintFreshRets_ff_only_outVals_mem` (which characterized each output value itself as being a
    specific `.ffv`) unconditionally, via `symValVars_freshRetSymValue_below` + a per-cons
    induction mirroring `mintFreshRets_eq`'s own recursion. -/
theorem mintFreshRets_outVals_vars_below {c : ZKConfig} :
    ∀ (rets : List Param) (nextVarId : Nat),
      ∀ sv ∈ (mintFreshRets (c := c) nextVarId rets).2.2, ∀ v ∈ symValVars sv,
        ∃ n, v = Var.ffv n ∧ nextVarId ≤ n ∧ n < (mintFreshRets (c := c) nextVarId rets).1 := by
  intro rets
  induction rets with
  | nil => intro nextVarId sv hsv; simp [mintFreshRets] at hsv
  | cons r rs ih =>
      intro nextVarId sv hsv v hv
      rw [mintFreshRets_cons] at hsv
      simp only [List.mem_cons] at hsv
      obtain ⟨hnv1_eq, _, hsv_eq⟩ := mintFreshRetParam_eq (c := c) nextVarId r.type
      have hmono := mintFreshRets_mono (c := c) (mintFreshRetParam (c := c) nextVarId r.type).1 rs
      have hps : paramSize r = typeSize r.type := rfl
      rcases hsv with heq | hmem
      · subst heq
        rw [hsv_eq] at hv
        obtain ⟨n, hveq, hn1, hn2⟩ := symValVars_freshRetSymValue_below nextVarId r.type v hv
        have hn2' : n < (mintFreshRetParam (c := c) nextVarId r.type).1 := by
          rw [hnv1_eq]; exact hn2
        have hn2'' : n < (mintFreshRets (c := c) (mintFreshRetParam (c := c) nextVarId r.type).1
            rs).1 := Nat.lt_of_lt_of_le hn2' hmono
        have hfinal : n < (mintFreshRets (c := c) nextVarId (r :: rs)).1 := by
          rw [mintFreshRets_cons]; exact hn2''
        exact ⟨n, hveq, hn1, hfinal⟩
      · obtain ⟨n, hveq, hn1, hn2⟩ := ih (mintFreshRetParam (c := c) nextVarId r.type).1 sv hmem v hv
        have hle1 : nextVarId ≤ (mintFreshRetParam (c := c) nextVarId r.type).1 := by
          rw [hnv1_eq]; omega
        have hle : nextVarId ≤ n := hle1.trans hn1
        have hfinal : n < (mintFreshRets (c := c) nextVarId (r :: rs)).1 := by
          rw [mintFreshRets_cons]; exact hn2
        exact ⟨n, hveq, hle, hfinal⟩
