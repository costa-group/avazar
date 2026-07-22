import Corellzk2smt.Basic
import Corellzk2smt.Language.Core.Semantics.Basic
import Corellzk2smt.Language.Core.Semantics.BigStep
import Corellzk2smt.SymExec.Basic
import Corellzk2smt.SymExec.BigStep
import Corellzk2smt.FFConstraints.Basic
import Corellzk2smt.FFConstraints.Satisfiability
import Corellzk2smt.FFConstraints.Satisfiability_th
import Corellzk2smt.Language.Core.Analysis.DefinedVars


namespace Corellzk2smt.SymExec.Lemmas

open Corellzk2smt.Config (GlobalConfig)
open Corellzk2smt.Language.Core.Syntax.AST
open Corellzk2smt.Language.Core.Semantics.Basic
open Corellzk2smt.Language.Core.Semantics.BigStep
open Corellzk2smt.SymExec.Basic
open Corellzk2smt.SymExec.BigStep
open Corellzk2smt.FFConstraints.Basic
open Corellzk2smt.FFConstraints.Satisfiability
open Corellzk2smt.FFConstraints.Satisfiability_th
open Corellzk2smt.Language.Core.Analysis.DefinedVars

-- ---------------------------------------------------------------------------
-- Environment / assignment correspondence
-- ---------------------------------------------------------------------------

/-- A simple symbolic value matches a concrete FF value under an assignment: a constant
    matches iff it equals the value exactly; a symbolic variable matches iff the assignment
    gives it exactly that value. The cached binary expansion (`FFVarWithBinRep.bits`) is
    deliberately ignored here -- whether those bits actually decompose the value is a separate
    concern, to be layered on later as its own side-condition rather than folded into what
    "the right value" means. -/
def simpleValMatches {c : ZKConfig} (assignment : Assignment c) (sv : SimpleSymVal c)
    (v : FF c) : Prop :=
  match sv with
  | .const v'  => v' = v
  | .ffvar vbr => assignment.ff vbr.var = v

/-- A symbolic value matches a concrete value: scalars via `simpleValMatches`; arrays
    pointwise, which also forces them to have the same size (`List.Forall₂`). -/
def symValMatches {c : ZKConfig} (assignment : Assignment c) (sv : SymValue c)
    (v : Value c) : Prop :=
  match sv, v with
  | .simple s,  .scalar v  => simpleValMatches assignment s v
  | .array arr, .array varr => List.Forall₂ (simpleValMatches assignment) arr.toList varr.toList
  | .simple _,  .array _   => False
  | .array _,   .scalar _  => False

/-- A concrete environment matches a symbolic environment under an assignment: same
    domain (as sets of keys), and `symValMatches` holds pointwise on every key. -/
def EnvMatches {c : ZKConfig} (assignment : Assignment c) (symEnv : SymEnv c)
    (env : Env c) : Prop :=
  (∀ id, symEnv.contains id ↔ env.contains id) ∧
  ∀ id sv, symEnv.get? id = some sv → ∃ v, env.get? id = some v ∧ symValMatches assignment sv v

-- ---------------------------------------------------------------------------
-- Decode existence: every `SymEnv`/`Assignment` pair has a matching concrete `Env`
-- ---------------------------------------------------------------------------

/-- Generic (works for any `Std.TreeMap VarID _`, so both `Env`/`SymEnv`) characterization of
    `.contains` after a single insert. -/
theorem contains_insert_iff {β : Type} (env : Std.TreeMap VarID β) (id0 id : VarID) (v : β) :
    (env.insert id0 v).contains id ↔ (id = id0 ∨ env.contains id) := by
  simp only [Std.TreeMap.contains_insert]
  by_cases h : id = id0
  · subst h; simp
  · have hne : id0 ≠ id := Ne.symm h
    simp [h, hne]

/-- `setVars`'s output has exactly `ids ++ (env's own domain)` as its domain -- every id it
    processes gets set exactly once (via `setVar`/`.insert`), and nothing else changes. Needed to
    characterize `seFuncCall`'s domain effect (its `outs` list only ever adds those specific
    names, on top of whatever `symEnv` already had). -/
theorem setVars_contains_iff {c : ZKConfig} :
    ∀ (env : SymEnv c) (ids : List VarID) (vs : List (SymValue c)) (env' : SymEnv c),
      Corellzk2smt.SymExec.Basic.setVars env ids vs = Except.ok env' →
      ∀ id, env'.contains id ↔ (id ∈ ids ∨ env.contains id) := by
  intro env ids
  induction ids generalizing env with
  | nil =>
      intro vs env' heq id
      cases vs with
      | nil =>
          simp only [Corellzk2smt.SymExec.Basic.setVars, Except.ok.injEq] at heq
          rw [← heq]; simp
      | cons _ _ => simp [Corellzk2smt.SymExec.Basic.setVars] at heq
  | cons id0 rest ih =>
      intro vs env' heq id
      cases vs with
      | nil => simp [Corellzk2smt.SymExec.Basic.setVars] at heq
      | cons v vs' =>
          cases hrec : Corellzk2smt.SymExec.Basic.setVars (Corellzk2smt.SymExec.Basic.setVar env id0 v) rest vs' with
          | error e =>
              simp only [Corellzk2smt.SymExec.Basic.setVars, hrec] at heq
              exact absurd heq (by simp)
          | ok env'' =>
              simp only [Corellzk2smt.SymExec.Basic.setVars, hrec, Except.ok.injEq] at heq
              rw [← heq, ih (Corellzk2smt.SymExec.Basic.setVar env id0 v) vs' env'' hrec id]
              simp only [Corellzk2smt.SymExec.Basic.setVar, contains_insert_iff, List.mem_cons]
              tauto

/-- The concrete value a simple symbolic value denotes under a given assignment: a constant
    decodes to itself; a symbolic variable decodes to whatever the assignment gives it. This is
    the "obvious" inverse of `simpleValMatches` -- `simpleValMatches a sv (decodeSimpleVal a sv)`
    holds unconditionally, by construction (see `decodeSimpleVal_matches`). -/
def decodeSimpleVal {c : ZKConfig} (a : Assignment c) (sv : SimpleSymVal c) : FF c :=
  match sv with
  | .const v   => v
  | .ffvar vbr => a.ff vbr.var

/-- The concrete value a symbolic value denotes under a given assignment, pointwise for
    arrays. -/
def decodeSymValue {c : ZKConfig} (a : Assignment c) (sv : SymValue c) : Value c :=
  match sv with
  | .simple s   => .scalar (decodeSimpleVal a s)
  | .array arr  => .array (arr.map (decodeSimpleVal a))

theorem decodeSimpleVal_matches {c : ZKConfig} (a : Assignment c) (sv : SimpleSymVal c) :
    simpleValMatches a sv (decodeSimpleVal a sv) := by
  cases sv <;> simp [simpleValMatches, decodeSimpleVal]

theorem decodeSymValue_matches {c : ZKConfig} (a : Assignment c) (sv : SymValue c) :
    symValMatches a sv (decodeSymValue a sv) := by
  cases sv with
  | simple s => simp only [symValMatches, decodeSymValue]; exact decodeSimpleVal_matches a s
  | array arr =>
      simp only [symValMatches, decodeSymValue, Array.toList_map]
      induction arr.toList with
      | nil => exact List.Forall₂.nil
      | cons hd tl ih => exact List.Forall₂.cons (decodeSimpleVal_matches a hd) ih

/-- `decodeSymEnv` builds a concrete `Env` from a `SymEnv` by decoding every entry under a
    fixed assignment. Built via a plain `List.foldl` over `env.toList` (rather than
    `Std.TreeMap.foldl` directly) so its `.get?`/`.contains` behavior can be established by
    ordinary list induction, mirroring `mergeSymEnvKeys_domain`'s style. -/
def decodeSymEnv {c : ZKConfig} (a : Assignment c) (env : SymEnv c) : Env c :=
  env.toList.foldl
    (fun acc p => Corellzk2smt.Language.Core.Semantics.Basic.setVar acc p.1 (decodeSymValue a p.2))
    (emptyEnv c)

theorem decodeSymEnv_domain_list {c : ZKConfig} (a : Assignment c) :
    ∀ (l : List (VarID × SymValue c)) (init : Env c) (id : VarID),
      (l.foldl (fun acc p =>
          Corellzk2smt.Language.Core.Semantics.Basic.setVar acc p.1 (decodeSymValue a p.2))
          init).contains id
        ↔ (id ∈ l.map Prod.fst ∨ init.contains id) := by
  intro l
  induction l with
  | nil => intro init id; simp
  | cons p rest ih =>
      intro init id
      simp only [List.foldl_cons, List.map_cons, List.mem_cons]
      rw [ih (Corellzk2smt.Language.Core.Semantics.Basic.setVar init p.1
        (decodeSymValue a p.2)) id]
      simp only [Corellzk2smt.Language.Core.Semantics.Basic.setVar, contains_insert_iff]
      tauto

/-- Folding over a list that never mentions `id` never disturbs `id`'s value in the
    accumulator. -/
theorem decodeSymEnv_get?_frame_list {c : ZKConfig} (a : Assignment c) :
    ∀ (l : List (VarID × SymValue c)) (id : VarID), id ∉ l.map Prod.fst →
      ∀ (init : Env c),
        (l.foldl (fun acc p =>
            Corellzk2smt.Language.Core.Semantics.Basic.setVar acc p.1 (decodeSymValue a p.2))
            init).get? id
          = init.get? id := by
  intro l
  induction l with
  | nil => intro id _ init; rfl
  | cons p rest ih =>
      intro id hid init
      simp only [List.foldl_cons]
      have hne : id ≠ p.1 := fun h => hid (h ▸ List.mem_map_of_mem (List.mem_cons_self ..))
      rw [ih id (fun h => hid (List.mem_cons_of_mem _ h))
        (Corellzk2smt.Language.Core.Semantics.Basic.setVar init p.1 (decodeSymValue a p.2))]
      simp only [Corellzk2smt.Language.Core.Semantics.Basic.setVar, Std.TreeMap.get?_eq_getElem?,
        Std.TreeMap.getElem?_insert]
      rw [if_neg (by simp [hne, Ne.symm hne])]

theorem decodeSymEnv_get?_list {c : ZKConfig} (a : Assignment c) :
    ∀ (l : List (VarID × SymValue c)), (l.map Prod.fst).Nodup →
      ∀ (init : Env c) (id : VarID) (sv : SymValue c), (id, sv) ∈ l →
        (l.foldl (fun acc p =>
            Corellzk2smt.Language.Core.Semantics.Basic.setVar acc p.1 (decodeSymValue a p.2))
            init).get? id
          = some (decodeSymValue a sv) := by
  intro l
  induction l with
  | nil => intro _ init id sv h; cases h
  | cons p rest ih =>
      intro hnodup init id sv hmem
      obtain ⟨hpNotMemRest, hrestNodup⟩ := List.nodup_cons.mp hnodup
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hmem with heq | hmem'
      · obtain ⟨heq1, heq2⟩ := (Prod.mk.injEq ..).mp heq.symm
        rw [decodeSymEnv_get?_frame_list a rest id (heq1 ▸ hpNotMemRest)
          (Corellzk2smt.Language.Core.Semantics.Basic.setVar init p.1 (decodeSymValue a p.2))]
        rw [heq1, heq2]
        simp only [Corellzk2smt.Language.Core.Semantics.Basic.setVar,
          Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert_self]
      · have hne : id ≠ p.1 := fun h =>
          hpNotMemRest (h ▸ List.mem_map_of_mem hmem' (f := Prod.fst))
        exact ih hrestNodup
          (Corellzk2smt.Language.Core.Semantics.Basic.setVar init p.1 (decodeSymValue a p.2))
          id sv hmem'

/-- `decodeSymEnv` matches the `SymEnv` it was decoded from, under the same assignment --
    every symbolic value gets EXACTLY its decoded concrete counterpart, so `EnvMatches` holds
    with witness value `decodeSymValue a sv` (via `decodeSymValue_matches`). -/
theorem EnvMatches_decodeSymEnv {c : ZKConfig} (a : Assignment c) (env : SymEnv c) :
    EnvMatches a env (decodeSymEnv a env) := by
  constructor
  · intro id
    rw [show env.contains id ↔ id ∈ env.keys from (Std.TreeMap.mem_keys (k := id)).symm,
      show env.keys = env.toList.map Prod.fst from Std.TreeMap.map_fst_toList_eq_keys.symm]
    simp only [decodeSymEnv]
    rw [decodeSymEnv_domain_list a env.toList (emptyEnv c) id]
    have hempty : (emptyEnv c).contains id = false := rfl
    simp [hempty]
  · intro id sv hget
    refine ⟨decodeSymValue a sv, ?_, decodeSymValue_matches a sv⟩
    have hnodup : (env.toList.map Prod.fst).Nodup := by
      rw [Std.TreeMap.map_fst_toList_eq_keys]; exact Std.TreeMap.nodup_keys
    exact decodeSymEnv_get?_list a env.toList hnodup (emptyEnv c) id sv
      (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr (Std.TreeMap.get?_eq_getElem? ▸ hget))

/-- **Decode existence**: for any symbolic environment and any assignment, a matching
    concrete environment always exists -- `decodeSymEnv` builds one explicitly. This is exactly
    the fact `seqComposition`'s (and `mergeIfBranches`'s) *completeness* direction needs: a
    satisfying assignment for the produced formula always has SOME concrete execution behind
    it, not just a symbolic shadow. -/
theorem decode_exists {c : ZKConfig} (env : SymEnv c) (a : Assignment c) :
    ∃ e : Env c, EnvMatches a env e :=
  ⟨decodeSymEnv a env, EnvMatches_decodeSymEnv a env⟩

-- ---------------------------------------------------------------------------
-- Variables mentioned by a symbolic environment
-- ---------------------------------------------------------------------------

/-- The constraint variable a simple symbolic value denotes, if any (constants denote
    none). Ignores the cached binary expansion, for the same reason as `simpleValMatches`. -/
def simpleValVars {c : ZKConfig} (sv : SimpleSymVal c) : VarSet :=
  match sv with
  | .const _   => emptyVarSet
  | .ffvar vbr => emptyVarSet.insert (Var.ffv vbr.var)

def symValVars {c : ZKConfig} (sv : SymValue c) : VarSet :=
  match sv with
  | .simple s   => simpleValVars s
  | .array arr => arr.foldl (fun acc s => acc ∪ simpleValVars s) emptyVarSet

/-- All constraint variables referenced anywhere in a symbolic environment -- always
    `Var.ffv`s in practice, since program variables are FF-valued or FF-arrays
    (`Language/Core/Syntax/AST.lean`'s `VarType`), never directly bool-valued. -/
def symEnvVars {c : ZKConfig} (env : SymEnv c) : VarSet :=
  env.foldl (fun acc _id sv => acc ∪ symValVars sv) emptyVarSet

/-- A property preserved by every step of a `List.foldl` (starting true of `init`) holds of
    the final result. Generic helper used to transport "only `Var.ffv`s" through
    `Array.foldl`/`Std.TreeMap.foldl` via their `_eq_foldl_toList` lemmas. -/
private theorem list_foldl_preserves {α β : Type} (P : β → Prop) (f : β → α → β)
    (l : List α) (init : β) (hinit : P init)
    (hstep : ∀ acc a, P acc → P (f acc a)) :
    P (l.foldl f init) := by
  induction l generalizing init with
  | nil => simpa using hinit
  | cons a l ih => simpa using ih (f init a) (hstep init a hinit)

/-- `simpleValVars` only ever produces `Var.ffv` members (stated via `compare`, since `Var`'s
    order has no registered `LawfulEqCmp` instance connecting `compare = .eq` to literal
    equality -- not needed here anyway, see `agreesOnBool_symEnvVars`). -/
theorem simpleValVars_isFF {c : ZKConfig} (sv : SimpleSymVal c) :
    ∀ v ∈ simpleValVars sv, ∃ n, compare (Var.ffv n) v = .eq := by
  cases sv with
  | const _ =>
      intro v hv
      simp only [simpleValVars] at hv
      exact absurd hv Std.TreeSet.not_mem_emptyc
  | ffvar vbr =>
      intro v hv
      simp only [simpleValVars] at hv
      rcases Std.TreeSet.mem_insert.mp hv with heq | hmem
      · exact ⟨vbr.var, heq⟩
      · exact absurd hmem Std.TreeSet.not_mem_emptyc

/-- `symValVars` only ever produces `Var.ffv` members. -/
theorem symValVars_isFF {c : ZKConfig} (sv : SymValue c) :
    ∀ v ∈ symValVars sv, ∃ n, compare (Var.ffv n) v = .eq := by
  cases sv with
  | simple s => exact simpleValVars_isFF s
  | array arr =>
      simp only [symValVars]
      rw [← Array.foldl_toList]
      apply list_foldl_preserves (fun vs => ∀ v ∈ vs, ∃ n, compare (Var.ffv n) v = .eq)
      · intro v hv; exact absurd hv Std.TreeSet.not_mem_emptyc
      · intro acc s hacc v hv
        rcases Std.TreeSet.mem_union_iff.mp hv with hv1 | hv2
        · exact hacc v hv1
        · exact simpleValVars_isFF s v hv2

/-- `symEnvVars` only ever produces `Var.ffv` members -- i.e. never a `Var.boolv`, so
    `agreesOnBool (symEnvVars _)` holds of any two assignments unconditionally. -/
theorem symEnvVars_isFF {c : ZKConfig} (env : SymEnv c) :
    ∀ v ∈ symEnvVars env, ∃ n, compare (Var.ffv n) v = .eq := by
  simp only [symEnvVars]
  rw [Std.TreeMap.foldl_eq_foldl_toList]
  apply list_foldl_preserves (fun vs => ∀ v ∈ vs, ∃ n, compare (Var.ffv n) v = .eq)
  · intro v hv; exact absurd hv Std.TreeSet.not_mem_emptyc
  · intro acc ab hacc v hv
    rcases Std.TreeSet.mem_union_iff.mp hv with hv1 | hv2
    · exact hacc v hv1
    · exact symValVars_isFF ab.2 v hv2

/-- `agreesOnBool` on a `symEnvVars`-shaped set is unconditional, since such a set never
    contains a `Var.boolv`: `compare (Var.ffv _) (Var.boolv _)` always reduces to `.lt`,
    never `.eq`. -/
theorem agreesOnBool_symEnvVars {c : ZKConfig} (env : SymEnv c) (a b : Assignment c) :
    agreesOnBool (symEnvVars env) a b := by
  intro n hn
  obtain ⟨m, hm⟩ := symEnvVars_isFF env (Var.boolv n) hn
  rw [show compare (Var.ffv m) (Var.boolv n) = Ordering.lt from rfl] at hm
  exact absurd hm (by decide)

-- ---------------------------------------------------------------------------
-- Freshness w.r.t. a variable-id counter
-- ---------------------------------------------------------------------------

/-- The raw index underlying a constraint variable, regardless of kind. `SymExecConfig`/
    `CmdsSpec`/`FuncSpec` all mint fresh variables from a single shared `Nat` counter
    (`nextVarId`, used for both FF and bool vars), so "freshness" is naturally one linear
    order over this index rather than two separate ones. -/
def varIndex (v : Var) : Nat :=
  match v with
  | .ffv n   => n
  | .boolv n => n

/-- Every variable in `vs` has an index strictly below `n` -- i.e. `vs` only contains
    variables that were already fresh/allocated before the counter reached `n`. (Plain prefix
    name rather than `VarSet.below`: `VarSet` is just an `abbrev` for `Std.TreeSet Var compare`,
    so dot-notation on a `VarSet` value would resolve against `Std.TreeSet`, not this def.) -/
def varSetBelow (vs : VarSet) (n : Nat) : Prop :=
  ∀ v ∈ vs, varIndex v < n

-- ---------------------------------------------------------------------------
-- The correctness notion relating a piece of symbolic execution to its concrete counterpart
-- ---------------------------------------------------------------------------

/-- The variables a spec's formula `f` may mention, as a `VarSet`: shorthand used throughout
    `TranslatesCorrectly` and its consequences. -/
def specVars {c : ZKConfig} (spec : CmdsSpec c) : VarSet :=
  ffVarsOfFormula spec.f ∪ bVarsOfFormula spec.f


-- ---------------------------------------------------------------------------
-- Correctness of the constant-folding helpers
-- ---------------------------------------------------------------------------

/-- If `tryEvalSimpleExprToFFValue` resolves `s` to a concrete value under a matching
    `symEnv`, `evalSimpleExprToFFValue` resolves `s` to that same value on the matching
    concrete `env`. -/
theorem tryEvalSimpleExprToFFValue_correct {c : ZKConfig}
    (symEnv : SymEnv c) (s : SimpleExpr c) (env : Env c) (assignment : Assignment c) (v : FF c)
    (hmatch : EnvMatches assignment symEnv env)
    (heval : tryEvalSimpleExprToFFValue symEnv s = Except.ok v) :
    evalSimpleExprToFFValue env s = Except.ok v := by
  cases s with
  | val v' =>
      simp only [tryEvalSimpleExprToFFValue] at heval
      simp only [evalSimpleExprToFFValue, heval]
  | var id =>
      simp only [tryEvalSimpleExprToFFValue, Corellzk2smt.SymExec.Basic.getVar] at heval
      cases hget : symEnv.get? id with
      | none =>
          rw [hget] at heval
          simp at heval
      | some rest =>
          rw [hget] at heval
          cases rest with
          | simple sv =>
              cases sv with
              | const v' =>
                  simp only at heval
                  injection heval with hv'
                  obtain ⟨_hdom, hpoint⟩ := hmatch
                  obtain ⟨vv, henv, hvv⟩ := hpoint id (.simple (.const v')) hget
                  cases vv with
                  | scalar vv' =>
                      simp only [symValMatches, simpleValMatches] at hvv
                      simp only [evalSimpleExprToFFValue,
                        Corellzk2smt.Language.Core.Semantics.Basic.getVar, henv]
                      rw [← hv', hvv]
                  | array varr =>
                      simp only [symValMatches] at hvv
              | ffvar _ => simp at heval
          | array _ => simp at heval

/-- If `tryEvalCondToConcreteValue` resolves `cond` to a concrete boolean under a matching
    `symEnv`, `evalCond` resolves `cond` to that same boolean on the matching concrete `env`. -/
theorem tryEvalCondToConcreteValue_correct {c : ZKConfig}
    (gconf : GlobalConfig c) (sconf : SymExecConfig c)
    (symEnv : SymEnv c) (md : CmdMD) (cond : Cond c)
    (env : Env c) (assignment : Assignment c) (b : Bool)
    (hmatch : EnvMatches assignment symEnv env)
    (heval : tryEvalCondToConcreteValue gconf sconf symEnv md cond = Except.ok b) :
    evalCond env cond = Except.ok b := by
  cases cond with
  | eq s1 s2 =>
      simp only [tryEvalCondToConcreteValue] at heval
      cases heval1 : tryEvalSimpleExprToFFValue symEnv s1 with
      | error e => rw [heval1] at heval; simp at heval
      | ok val1 =>
          rw [heval1] at heval
          cases heval2 : tryEvalSimpleExprToFFValue symEnv s2 with
          | error e => rw [heval2] at heval; simp at heval
          | ok val2 =>
              rw [heval2] at heval
              have hv1 := tryEvalSimpleExprToFFValue_correct symEnv s1 env assignment val1
                hmatch heval1
              have hv2 := tryEvalSimpleExprToFFValue_correct symEnv s2 env assignment val2
                hmatch heval2
              simp only [evalCond, hv1, hv2]
              exact heval

/-- If `resolveSimpleExpr` resolves `s` to a symbolic value (constant or constraint variable)
    under a matching `symEnv`, `evalSimpleExprToFFValue` succeeds on the matching concrete
    `env`, and the two results match. Unlike `tryEvalSimpleExprToFFValue_correct`, this always
    applies (no need for `s` to be constant-foldable). -/
theorem resolveSimpleExpr_correct {c : ZKConfig}
    (symEnv : SymEnv c) (s : SimpleExpr c) (env : Env c) (assignment : Assignment c)
    (sv : SimpleSymVal c)
    (hmatch : EnvMatches assignment symEnv env)
    (heval : resolveSimpleExpr symEnv s = Except.ok sv) :
    ∃ v, evalSimpleExprToFFValue env s = Except.ok v ∧ simpleValMatches assignment sv v := by
  cases s with
  | val v' =>
      simp only [resolveSimpleExpr] at heval
      injection heval with hv
      refine ⟨v', ?_, ?_⟩
      · simp only [evalSimpleExprToFFValue]
      · simp only [← hv, simpleValMatches]
  | var id =>
      simp only [resolveSimpleExpr, Corellzk2smt.SymExec.Basic.getVar] at heval
      cases hget : symEnv.get? id with
      | none =>
          rw [hget] at heval
          simp at heval
      | some rest =>
          rw [hget] at heval
          cases rest with
          | simple sv' =>
              simp only at heval
              injection heval with hsv
              obtain ⟨_hdom, hpoint⟩ := hmatch
              obtain ⟨vv, henv, hvv⟩ := hpoint id (.simple sv') hget
              cases vv with
              | scalar vv' =>
                  refine ⟨vv', ?_, ?_⟩
                  · simp only [evalSimpleExprToFFValue,
                      Corellzk2smt.Language.Core.Semantics.Basic.getVar, henv]
                  · simp only [symValMatches] at hvv
                    rw [← hsv]
                    exact hvv
              | array varr =>
                  simp only [symValMatches] at hvv
          | array _ => simp at heval

/-- The term `simpleSymValToTerm sv` evaluates to whatever concrete value `sv` matches. -/
theorem evalTerm_simpleSymValToTerm {c : ZKConfig} (gconf : GlobalConfig c)
    (assignment : Assignment c) (sv : SimpleSymVal c) (v : FF c) (ms : List (FFMacro c))
    (h : simpleValMatches assignment sv v) :
    evalTerm gconf assignment (simpleSymValToTerm sv) ms = Except.ok v := by
  cases sv with
  | const v' =>
      simp only [simpleValMatches] at h
      simp only [simpleSymValToTerm, evalTerm, h]
  | ffvar vbr =>
      simp only [simpleValMatches] at h
      simp only [simpleSymValToTerm, evalTerm, h]

/-- If `encodeCond` produces `g` from a `symEnv` matching a given `env`/`assignment`,
    evaluating `g` under `assignment` gives the same boolean as `evalCond` gives under
    `env` -- the guard formula faithfully tracks the concrete condition. -/
theorem encodeCond_sound {c : ZKConfig}
    (gconf : GlobalConfig c) (ms : List (FFMacro c))
    (symEnv : SymEnv c) (cond : Cond c) (g : FFFormula c)
    (heq : encodeCond symEnv cond = Except.ok g)
    (env : Env c) (assignment : Assignment c) (hmatch : EnvMatches assignment symEnv env)
    (b : Bool) (hcond : evalCond env cond = Except.ok b) :
    evalFormula gconf assignment g ms = Except.ok b := by
  cases cond with
  | eq s1 s2 =>
      simp only [encodeCond] at heq
      cases heq1 : resolveSimpleExpr symEnv s1 with
      | error e => rw [heq1] at heq; simp at heq
      | ok sv1 =>
          rw [heq1] at heq
          cases heq2 : resolveSimpleExpr symEnv s2 with
          | error e => rw [heq2] at heq; simp at heq
          | ok sv2 =>
              rw [heq2] at heq
              simp only at heq
              injection heq with hg
              obtain ⟨v1, hv1, hm1⟩ :=
                resolveSimpleExpr_correct symEnv s1 env assignment sv1 hmatch heq1
              obtain ⟨v2, hv2, hm2⟩ :=
                resolveSimpleExpr_correct symEnv s2 env assignment sv2 hmatch heq2
              simp only [evalCond, hv1, hv2] at hcond
              have ht1 := evalTerm_simpleSymValToTerm gconf assignment sv1 v1 ms hm1
              have ht2 := evalTerm_simpleSymValToTerm gconf assignment sv2 v2 ms hm2
              rw [← hg]
              simp only [evalFormula, ht1, ht2]
              split at hcond <;> simp_all

/-- Converse of `encodeCond_sound`: if `g`'s evaluation under a matching assignment gives some
    boolean, `evalCond` gives that same boolean on the matching concrete `env`. Unlike
    `encodeCond_sound`, this doesn't need `evalCond env cond` to be known to succeed up front --
    it's derived, since both sides ultimately compute the same equality of concrete values. -/
theorem encodeCond_complete {c : ZKConfig}
    (gconf : GlobalConfig c) (ms : List (FFMacro c))
    (symEnv : SymEnv c) (cond : Cond c) (g : FFFormula c)
    (heq : encodeCond symEnv cond = Except.ok g)
    (env : Env c) (assignment : Assignment c) (hmatch : EnvMatches assignment symEnv env)
    (b : Bool) (hb : evalFormula gconf assignment g ms = Except.ok b) :
    evalCond env cond = Except.ok b := by
  cases cond with
  | eq s1 s2 =>
      simp only [encodeCond] at heq
      cases heq1 : resolveSimpleExpr symEnv s1 with
      | error e => rw [heq1] at heq; simp at heq
      | ok sv1 =>
          rw [heq1] at heq
          cases heq2 : resolveSimpleExpr symEnv s2 with
          | error e => rw [heq2] at heq; simp at heq
          | ok sv2 =>
              rw [heq2] at heq
              simp only at heq
              injection heq with hg
              obtain ⟨v1, hv1, hm1⟩ :=
                resolveSimpleExpr_correct symEnv s1 env assignment sv1 hmatch heq1
              obtain ⟨v2, hv2, hm2⟩ :=
                resolveSimpleExpr_correct symEnv s2 env assignment sv2 hmatch heq2
              have ht1 := evalTerm_simpleSymValToTerm gconf assignment sv1 v1 ms hm1
              have ht2 := evalTerm_simpleSymValToTerm gconf assignment sv2 v2 ms hm2
              rw [← hg] at hb
              simp only [evalFormula, ht1, ht2] at hb
              have hbeq : (if v1 = v2 then (Except.ok true : Except String Bool)
                  else Except.ok false) = Except.ok (v1 == v2) := by
                by_cases hv : v1 = v2 <;> simp [hv]
              simp only [evalCond, hv1, hv2, hbeq]
              exact hb

-- ---------------------------------------------------------------------------
-- Small helpers for `.and`-formulas
-- ---------------------------------------------------------------------------

theorem evalFormula_and_elim {c : ZKConfig} (gconf : GlobalConfig c) (assign : Assignment c)
    (f1 f2 : FFFormula c) (ms : List (FFMacro c))
    (h : evalFormula gconf assign (.and f1 f2) ms = Except.ok true) :
    evalFormula gconf assign f1 ms = Except.ok true ∧
    evalFormula gconf assign f2 ms = Except.ok true := by
  simp only [evalFormula] at h
  cases h1 : evalFormula gconf assign f1 ms with
  | error e => rw [h1] at h; simp at h
  | ok va =>
      rw [h1] at h
      cases h2 : evalFormula gconf assign f2 ms with
      | error e => rw [h2] at h; simp at h
      | ok vb =>
          rw [h2] at h
          simp only [Except.ok.injEq, Bool.and_eq_true_iff] at h
          exact ⟨by rw [h.1], by rw [h.2]⟩

theorem evalFormula_and_intro {c : ZKConfig} (gconf : GlobalConfig c) (assign : Assignment c)
    (f1 f2 : FFFormula c) (ms : List (FFMacro c))
    (h1 : evalFormula gconf assign f1 ms = Except.ok true)
    (h2 : evalFormula gconf assign f2 ms = Except.ok true) :
    evalFormula gconf assign (.and f1 f2) ms = Except.ok true := by
  simp [evalFormula, h1, h2]

/-- `.anno` is transparent to `evalFormula` -- it carries no semantic weight, purely a
    description string. -/
theorem evalFormula_anno {c : ZKConfig} (gconf : GlobalConfig c) (assign : Assignment c)
    (f : FFFormula c) (s : String) (ms : List (FFMacro c)) :
    evalFormula gconf assign (.anno f s) ms = evalFormula gconf assign f ms := by
  simp only [evalFormula]

/-- `.ite` short-circuits under `evalFormula`: once the guard is known true, the "then" branch
    alone decides the result -- the "else" branch is never evaluated, so no fact about it is
    needed. -/
theorem evalFormula_ite_intro_true {c : ZKConfig} (gconf : GlobalConfig c) (assign : Assignment c)
    (cf t e : FFFormula c) (ms : List (FFMacro c))
    (hc : evalFormula gconf assign cf ms = Except.ok true)
    (ht : evalFormula gconf assign t ms = Except.ok true) :
    evalFormula gconf assign (.ite cf t e) ms = Except.ok true := by
  simp [evalFormula, hc, ht]

/-- Mirror of `evalFormula_ite_intro_true`, for a false guard. -/
theorem evalFormula_ite_intro_false {c : ZKConfig} (gconf : GlobalConfig c) (assign : Assignment c)
    (cf t e : FFFormula c) (ms : List (FFMacro c))
    (hc : evalFormula gconf assign cf ms = Except.ok false)
    (he : evalFormula gconf assign e ms = Except.ok true) :
    evalFormula gconf assign (.ite cf t e) ms = Except.ok true := by
  simp [evalFormula, hc, he]

/-- Converse of `evalFormula_ite_intro_true`/`_false`: a satisfied `.ite` came from exactly one
    of the two branches being satisfied under the guard's actual value. -/
theorem evalFormula_ite_elim {c : ZKConfig} (gconf : GlobalConfig c) (assign : Assignment c)
    (cf t e : FFFormula c) (ms : List (FFMacro c))
    (h : evalFormula gconf assign (.ite cf t e) ms = Except.ok true) :
    (evalFormula gconf assign cf ms = Except.ok true ∧
      evalFormula gconf assign t ms = Except.ok true) ∨
    (evalFormula gconf assign cf ms = Except.ok false ∧
      evalFormula gconf assign e ms = Except.ok true) := by
  simp only [evalFormula] at h
  cases hc : evalFormula gconf assign cf ms with
  | error e' => rw [hc] at h; simp at h
  | ok b =>
      rw [hc] at h
      cases b with
      | true => exact Or.inl ⟨rfl, by simpa using h⟩
      | false => exact Or.inr ⟨rfl, by simpa using h⟩

-- ---------------------------------------------------------------------------
-- Correctness of the `mergeIfBranches` scalar-merge primitive
-- ---------------------------------------------------------------------------

/-- If two simple symbolic values agree (same constant, or the same constraint variable), they
    match exactly the same concrete values -- needed because `mergeSimpleSymVal`'s "agree" case
    always reports `svTb` as the merged value, even when asked about `svEb`'s side. -/
theorem simpleValMatches_agree_iff {c : ZKConfig} (a : Assignment c) (s1 s2 : SimpleSymVal c)
    (hagree : simpleSymValAgree s1 s2 = true) (v : FF c) :
    simpleValMatches a s1 v ↔ simpleValMatches a s2 v := by
  cases s1 with
  | const v1 =>
      cases s2 with
      | const v2 =>
          simp only [simpleSymValAgree, beq_iff_eq] at hagree
          simp only [simpleValMatches, hagree]
      | ffvar _ => exact absurd hagree (by simp [simpleSymValAgree])
  | ffvar vbr1 =>
      cases s2 with
      | const _ => exact absurd hagree (by simp [simpleSymValAgree])
      | ffvar vbr2 =>
          simp only [simpleSymValAgree, Bool.and_eq_true, beq_iff_eq] at hagree
          simp only [simpleValMatches, hagree.1]

/-- If an assignment already matches `svTb`'s value and satisfies `tbExtra` (whose own vars
    are all below `nextVarId`, i.e. `tbExtra` hasn't touched anything from `nextVarId` on --
    same for `svTb` itself), it extends -- changing at most the single variable index
    `nextVarId` -- to one that matches the *merged* value and satisfies the updated
    `tbExtra'` that `mergeSimpleSymVal` produces. (The `eb`-side statement is symmetric, just
    swapping which of `svTb`/`svEb` and `tbExtra`/`ebExtra` plays which role.) -/
theorem mergeSimpleSymVal_extend_tb {c : ZKConfig}
    (gconf : GlobalConfig c) (ms : List (FFMacro c))
    (nextVarId : Nat) (tbExtra ebExtra : FFFormula c) (svTb svEb : SimpleSymVal c)
    (hfresh : varSetBelow (ffVarsOfFormula tbExtra ∪ bVarsOfFormula tbExtra) nextVarId)
    (hsvTbFresh : varSetBelow (simpleValVars svTb) nextVarId)
    (a : Assignment c) (vTb : FF c) (hmTb : simpleValMatches a svTb vTb)
    (htbExtra : evalFormula gconf a tbExtra ms = Except.ok true) :
    ∃ a', (∀ n, n ≠ nextVarId → a'.ff n = a.ff n) ∧ (∀ n, a'.bool n = a.bool n) ∧
      (∀ n, Var.ffv n ∉
          (ffVarsOfFormula (mergeSimpleSymVal nextVarId tbExtra ebExtra svTb svEb).2.2.1 ∪
           bVarsOfFormula (mergeSimpleSymVal nextVarId tbExtra ebExtra svTb svEb).2.2.1) →
        a'.ff n = a.ff n) ∧
      simpleValMatches a' (mergeSimpleSymVal nextVarId tbExtra ebExtra svTb svEb).1 vTb ∧
      evalFormula gconf a' (mergeSimpleSymVal nextVarId tbExtra ebExtra svTb svEb).2.2.1 ms
        = Except.ok true := by
  simp only [mergeSimpleSymVal]
  split
  · exact ⟨a, fun n _ => rfl, fun n => rfl, fun n _ => rfl, hmTb, htbExtra⟩
  · set a' : Assignment c := { a with ff := fun n => if n = nextVarId then vTb else a.ff n }
      with ha'def
    have hffagree : ∀ n, n ≠ nextVarId → a'.ff n = a.ff n := by
      intro n hn
      simp only [ha'def, if_neg hn]
    have hboolagree : ∀ n, a'.bool n = a.bool n := fun _ => rfl
    have hframe : ∀ n, Var.ffv n ∉
        (ffVarsOfFormula (.and tbExtra (.eq (FFTerm.var nextVarId) (simpleSymValToTerm svTb))) ∪
         bVarsOfFormula (.and tbExtra (.eq (FFTerm.var nextVarId) (simpleSymValToTerm svTb)))) →
        a'.ff n = a.ff n := by
      intro n hn
      apply hffagree
      intro heq
      apply hn
      rw [heq]
      have heqf : Var.ffv nextVarId ∈
          ffVarsOfFormula (.eq (FFTerm.var nextVarId) (simpleSymValToTerm svTb)) := by
        simp only [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_union_iff]
        exact Or.inl (Std.TreeSet.mem_insert_self ..)
      exact Std.TreeSet.mem_union_of_left (Std.TreeSet.mem_union_of_right heqf)
    refine ⟨a', hffagree, hboolagree, hframe, ?_, ?_⟩
    · simp [simpleValMatches, ha'def]
    · have htbAgree : evalFormula gconf a tbExtra ms = evalFormula gconf a' tbExtra ms := by
        apply evalFormula_congr
        · intro n hn
          exact (hffagree n (Nat.ne_of_lt
            (hfresh (Var.ffv n) (Std.TreeSet.mem_union_of_left hn)))).symm
        · intro n _hn
          exact (hboolagree n).symm
      have htermAgree : evalTerm gconf a (simpleSymValToTerm svTb) ms
          = evalTerm gconf a' (simpleSymValToTerm svTb) ms := by
        cases svTb with
        | const v' => simp only [simpleSymValToTerm, evalTerm]
        | ffvar vbr =>
            have hlt : vbr.var < nextVarId :=
              hsvTbFresh (Var.ffv vbr.var) (by simp [simpleValVars])
            simp only [simpleSymValToTerm, evalTerm]
            rw [hffagree vbr.var (Nat.ne_of_lt hlt)]
      have heqterm : evalFormula gconf a' (.eq (FFTerm.var nextVarId) (simpleSymValToTerm svTb)) ms
          = Except.ok true := by
        have hval : a'.ff nextVarId = vTb := by simp [ha'def]
        have hsvTb := evalTerm_simpleSymValToTerm gconf a svTb vTb ms hmTb
        simp [evalFormula, evalTerm, hval, ← htermAgree, hsvTb]
      exact evalFormula_and_intro gconf a' tbExtra
        (.eq (FFTerm.var nextVarId) (simpleSymValToTerm svTb)) ms
        (htbAgree ▸ htbExtra) heqterm

/-- Mirror of `mergeSimpleSymVal_extend_tb`, for the `eb` side. -/
theorem mergeSimpleSymVal_extend_eb {c : ZKConfig}
    (gconf : GlobalConfig c) (ms : List (FFMacro c))
    (nextVarId : Nat) (tbExtra ebExtra : FFFormula c) (svTb svEb : SimpleSymVal c)
    (hfresh : varSetBelow (ffVarsOfFormula ebExtra ∪ bVarsOfFormula ebExtra) nextVarId)
    (hsvEbFresh : varSetBelow (simpleValVars svEb) nextVarId)
    (a : Assignment c) (vEb : FF c) (hmEb : simpleValMatches a svEb vEb)
    (hebExtra : evalFormula gconf a ebExtra ms = Except.ok true) :
    ∃ a', (∀ n, n ≠ nextVarId → a'.ff n = a.ff n) ∧ (∀ n, a'.bool n = a.bool n) ∧
      (∀ n, Var.ffv n ∉
          (ffVarsOfFormula (mergeSimpleSymVal nextVarId tbExtra ebExtra svTb svEb).2.2.2 ∪
           bVarsOfFormula (mergeSimpleSymVal nextVarId tbExtra ebExtra svTb svEb).2.2.2) →
        a'.ff n = a.ff n) ∧
      simpleValMatches a' (mergeSimpleSymVal nextVarId tbExtra ebExtra svTb svEb).1 vEb ∧
      evalFormula gconf a' (mergeSimpleSymVal nextVarId tbExtra ebExtra svTb svEb).2.2.2 ms
        = Except.ok true := by
  simp only [mergeSimpleSymVal]
  split
  · rename_i hagree
    exact ⟨a, fun n _ => rfl, fun n => rfl, fun n _ => rfl,
      (simpleValMatches_agree_iff a svTb svEb hagree vEb).mpr hmEb, hebExtra⟩
  · set a' : Assignment c := { a with ff := fun n => if n = nextVarId then vEb else a.ff n }
      with ha'def
    have hffagree : ∀ n, n ≠ nextVarId → a'.ff n = a.ff n := by
      intro n hn
      simp only [ha'def, if_neg hn]
    have hboolagree : ∀ n, a'.bool n = a.bool n := fun _ => rfl
    have hframe : ∀ n, Var.ffv n ∉
        (ffVarsOfFormula (.and ebExtra (.eq (FFTerm.var nextVarId) (simpleSymValToTerm svEb))) ∪
         bVarsOfFormula (.and ebExtra (.eq (FFTerm.var nextVarId) (simpleSymValToTerm svEb)))) →
        a'.ff n = a.ff n := by
      intro n hn
      apply hffagree
      intro heq
      apply hn
      rw [heq]
      have heqf : Var.ffv nextVarId ∈
          ffVarsOfFormula (.eq (FFTerm.var nextVarId) (simpleSymValToTerm svEb)) := by
        simp only [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_union_iff]
        exact Or.inl (Std.TreeSet.mem_insert_self ..)
      exact Std.TreeSet.mem_union_of_left (Std.TreeSet.mem_union_of_right heqf)
    refine ⟨a', hffagree, hboolagree, hframe, ?_, ?_⟩
    · simp [simpleValMatches, ha'def]
    · have hebAgree : evalFormula gconf a ebExtra ms = evalFormula gconf a' ebExtra ms := by
        apply evalFormula_congr
        · intro n hn
          exact (hffagree n (Nat.ne_of_lt
            (hfresh (Var.ffv n) (Std.TreeSet.mem_union_of_left hn)))).symm
        · intro n _hn
          exact (hboolagree n).symm
      have htermAgree : evalTerm gconf a (simpleSymValToTerm svEb) ms
          = evalTerm gconf a' (simpleSymValToTerm svEb) ms := by
        cases svEb with
        | const v' => simp only [simpleSymValToTerm, evalTerm]
        | ffvar vbr =>
            have hlt : vbr.var < nextVarId :=
              hsvEbFresh (Var.ffv vbr.var) (by simp [simpleValVars])
            simp only [simpleSymValToTerm, evalTerm]
            rw [hffagree vbr.var (Nat.ne_of_lt hlt)]
      have heqterm : evalFormula gconf a' (.eq (FFTerm.var nextVarId) (simpleSymValToTerm svEb)) ms
          = Except.ok true := by
        have hval : a'.ff nextVarId = vEb := by simp [ha'def]
        have hsvEb := evalTerm_simpleSymValToTerm gconf a svEb vEb ms hmEb
        simp [evalFormula, evalTerm, hval, ← htermAgree, hsvEb]
      exact evalFormula_and_intro gconf a' ebExtra
        (.eq (FFTerm.var nextVarId) (simpleSymValToTerm svEb)) ms
        (hebAgree ▸ hebExtra) heqterm

-- ---------------------------------------------------------------------------
-- Completeness ("match transfer") of the `mergeIfBranches` scalar-merge primitive
-- ---------------------------------------------------------------------------

/-- **Completeness** half of `mergeSimpleSymVal`, `tb` side: if a fixed assignment already
    matches `svTb` with some concrete value, and the merge-introduced equation (if any) holds
    under that same assignment, then it also matches the merged result. Unlike
    `mergeSimpleSymVal_extend_tb`, nothing is constructed -- `assignment'` is already given and
    fixed throughout, so this is a plain case split rather than an extension argument. -/
theorem mergeSimpleSymVal_match_of_tb {c : ZKConfig} (gconf : GlobalConfig c) (ms : List (FFMacro c))
    (assignment' : Assignment c) (nextVarId : Nat) (tbExtra ebExtra : FFFormula c)
    (svTb svEb : SimpleSymVal c) (v : FF c)
    (hmTb : simpleValMatches assignment' svTb v)
    (htbExtra' : evalFormula gconf assignment'
        (mergeSimpleSymVal nextVarId tbExtra ebExtra svTb svEb).2.2.1 ms = Except.ok true) :
    simpleValMatches assignment' (mergeSimpleSymVal nextVarId tbExtra ebExtra svTb svEb).1 v := by
  rcases Bool.eq_false_or_eq_true (simpleSymValAgree svTb svEb) with hagree | hagree
  · simp only [mergeSimpleSymVal, hagree, if_true] at htbExtra' ⊢
    exact hmTb
  · simp only [mergeSimpleSymVal, hagree, Bool.false_eq_true, if_false] at htbExtra' ⊢
    simp only [simpleValMatches]
    have h2 := (evalFormula_and_elim gconf assignment' tbExtra
      (.eq (FFTerm.var nextVarId) (simpleSymValToTerm svTb)) ms htbExtra').2
    have ht := evalTerm_simpleSymValToTerm gconf assignment' svTb v ms hmTb
    simp only [evalFormula, evalTerm, ht, Except.ok.injEq] at h2
    exact (beq_iff_eq ..).mp h2

/-- Mirror of `mergeSimpleSymVal_match_of_tb`, for the `eb` side. -/
theorem mergeSimpleSymVal_match_of_eb {c : ZKConfig} (gconf : GlobalConfig c) (ms : List (FFMacro c))
    (assignment' : Assignment c) (nextVarId : Nat) (tbExtra ebExtra : FFFormula c)
    (svTb svEb : SimpleSymVal c) (v : FF c)
    (hmEb : simpleValMatches assignment' svEb v)
    (hebExtra' : evalFormula gconf assignment'
        (mergeSimpleSymVal nextVarId tbExtra ebExtra svTb svEb).2.2.2 ms = Except.ok true) :
    simpleValMatches assignment' (mergeSimpleSymVal nextVarId tbExtra ebExtra svTb svEb).1 v := by
  rcases Bool.eq_false_or_eq_true (simpleSymValAgree svTb svEb) with hagree | hagree
  · simp only [mergeSimpleSymVal, hagree, if_true] at hebExtra' ⊢
    exact (simpleValMatches_agree_iff assignment' svTb svEb hagree v).mpr hmEb
  · simp only [mergeSimpleSymVal, hagree, Bool.false_eq_true, if_false] at hebExtra' ⊢
    simp only [simpleValMatches]
    have h2 := (evalFormula_and_elim gconf assignment' ebExtra
      (.eq (FFTerm.var nextVarId) (simpleSymValToTerm svEb)) ms hebExtra').2
    have ht := evalTerm_simpleSymValToTerm gconf assignment' svEb v ms hmEb
    simp only [evalFormula, evalTerm, ht, Except.ok.injEq] at h2
    exact (beq_iff_eq ..).mp h2

/-- `mergeSimpleSymVal` never lowers the variable counter. -/
theorem mergeSimpleSymVal_mono {c : ZKConfig}
    (nextVarId : Nat) (tbExtra ebExtra : FFFormula c) (svTb svEb : SimpleSymVal c) :
    nextVarId ≤ (mergeSimpleSymVal nextVarId tbExtra ebExtra svTb svEb).2.1 := by
  simp only [mergeSimpleSymVal]
  split
  · exact le_refl _
  · simp only []; omega

/-- Freshness w.r.t. a smaller counter implies freshness w.r.t. any larger one. -/
theorem varSetBelow_mono {vs : VarSet} {n n' : Nat} (h : n ≤ n') (hvs : varSetBelow vs n) :
    varSetBelow vs n' :=
  fun v hv => lt_of_lt_of_le (hvs v hv) h

/-- The merged value `mergeSimpleSymVal` produces is itself fresh below the *new* counter it
    returns: in the "agree" case it's `svTb`, already assumed fresh below the old (hence the
    new, not-smaller) counter; in the "disagree" case it's a variable at exactly the old
    counter, which is below the old counter plus one. -/
theorem mergeSimpleSymVal_result_fresh {c : ZKConfig}
    (nextVarId : Nat) (tbExtra ebExtra : FFFormula c) (svTb svEb : SimpleSymVal c)
    (hsvTbFresh : varSetBelow (simpleValVars svTb) nextVarId) :
    varSetBelow (simpleValVars (mergeSimpleSymVal nextVarId tbExtra ebExtra svTb svEb).1)
      (mergeSimpleSymVal nextVarId tbExtra ebExtra svTb svEb).2.1 := by
  simp only [mergeSimpleSymVal]
  split
  · exact hsvTbFresh
  · intro v hv
    simp only [simpleValVars] at hv
    rcases Std.TreeSet.mem_insert.mp hv with heq | hmem
    · cases v with
      | ffv m =>
          simp only [varIndex]
          have hnm : nextVarId = m := Nat.compare_eq_eq.mp heq
          omega
      | boolv m =>
          rw [show compare (Var.ffv nextVarId) (Var.boolv m) = Ordering.lt from rfl] at heq
          exact absurd heq (by decide)
    · exact absurd hmem Std.TreeSet.not_mem_emptyc

/-- Every var the merged value mentions is either one `svTb` already had, or is genuinely new
    (at the old counter) -- the subset-or-fresh analog of `mergeSimpleSymVal_result_fresh`,
    needed to show a merge's *output* only ever mentions "old or freshly-minted" vars relative
    to the original input, not just that it's fresh below the *new* counter. -/
theorem mergeSimpleSymVal_merged_subset {c : ZKConfig}
    (nextVarId : Nat) (tbExtra ebExtra : FFFormula c) (svTb svEb : SimpleSymVal c) :
    ∀ v ∈ simpleValVars (mergeSimpleSymVal nextVarId tbExtra ebExtra svTb svEb).1,
      v ∈ simpleValVars svTb ∨ nextVarId ≤ varIndex v := by
  simp only [mergeSimpleSymVal]
  split
  · exact fun v hv => Or.inl hv
  · intro v hv
    simp only [simpleValVars] at hv
    rcases Std.TreeSet.mem_insert.mp hv with heq | hmem
    · cases v with
      | ffv m =>
          right
          simp only [varIndex]
          have hnm : nextVarId = m := Nat.compare_eq_eq.mp heq
          omega
      | boolv m =>
          rw [show compare (Var.ffv nextVarId) (Var.boolv m) = Ordering.lt from rfl] at heq
          exact absurd heq (by decide)
    · exact absurd hmem Std.TreeSet.not_mem_emptyc

/-- `simpleSymValToTerm sv`'s FF-vars are exactly `simpleValVars sv` (`.val`/`.var` cases of
    `ffVarsOfTerm` line up with `.const`/`.ffvar` cases of `simpleValVars`, literally). -/
theorem ffVarsOfTerm_simpleSymValToTerm {c : ZKConfig} (sv : SimpleSymVal c) :
    ffVarsOfTerm (simpleSymValToTerm sv) = simpleValVars sv := by
  cases sv <;> simp only [simpleSymValToTerm, simpleValVars, ffVarsOfTerm]

/-- `simpleSymValToTerm sv` never mentions a bool variable. -/
theorem bVarsOfTerm_simpleSymValToTerm {c : ZKConfig} (sv : SimpleSymVal c) :
    bVarsOfTerm (simpleSymValToTerm sv) = emptyVarSet := by
  cases sv <;> simp only [simpleSymValToTerm, bVarsOfTerm]

/-- The union of two below-bounded var sets is below-bounded. -/
theorem varSetBelow_union {s1 s2 : VarSet} {n : Nat}
    (h1 : varSetBelow s1 n) (h2 : varSetBelow s2 n) : varSetBelow (s1 ∪ s2) n :=
  fun v hv => (Std.TreeSet.mem_union_iff.mp hv).elim (h1 v) (h2 v)

/-- The single variable `Var.ffv n` is below `n + 1`. -/
theorem varSetBelow_singleton_ffv {n : Nat} :
    varSetBelow (emptyVarSet.insert (Var.ffv n) : VarSet) (n + 1) := by
  intro v hv
  rcases Std.TreeSet.mem_insert.mp hv with heq | hmem
  · cases v with
    | ffv m => simp only [varIndex]; have := Nat.compare_eq_eq.mp heq; omega
    | boolv m =>
        rw [show compare (Var.ffv n) (Var.boolv m) = Ordering.lt from rfl] at heq
        exact absurd heq (by decide)
  · exact absurd hmem Std.TreeSet.not_mem_emptyc

/-- The accumulator of a union-fold is always a subset of the final result. -/
theorem foldl_union_subset {α : Type} (f : α → VarSet) (l : List α) (init : VarSet) :
    init ⊆ l.foldl (fun acc x => acc ∪ f x) init := by
  induction l generalizing init with
  | nil => exact fun _ hv => hv
  | cons x xs ih =>
      simp only [List.foldl_cons]
      exact fun v hv => ih (init ∪ f x) v (Std.TreeSet.mem_union_of_left hv)

/-- Each element's own contribution is a subset of the whole union-fold. -/
theorem foldl_union_mem_subset {α : Type} (f : α → VarSet) (l : List α) (x : α)
    (hx : x ∈ l) (init : VarSet) :
    f x ⊆ l.foldl (fun acc y => acc ∪ f y) init := by
  induction l generalizing init with
  | nil => cases hx
  | cons y ys ih =>
      rcases List.mem_cons.mp hx with heq | hmem
      · subst heq
        simp only [List.foldl_cons]
        exact fun v hv => foldl_union_subset f ys (init ∪ f x) v (Std.TreeSet.mem_union_of_right hv)
      · simp only [List.foldl_cons]
        exact ih hmem (init ∪ f y)

/-- If a whole array's vars are fresh below a bound, so is each of its elements'. -/
theorem symValVars_array_mem_below {c : ZKConfig} (arr : SymArray c) (s : SimpleSymVal c)
    (hs : s ∈ arr.toList) (bound : Nat) (hfresh : varSetBelow (symValVars (.array arr)) bound) :
    varSetBelow (simpleValVars s) bound := by
  intro v hv
  apply hfresh
  simp only [symValVars]
  rw [← Array.foldl_toList]
  exact foldl_union_mem_subset simpleValVars arr.toList s hs emptyVarSet v hv

/-- Set-based mirror of `symValVars_array_mem_below`: if a whole array's vars lie in `vs`, so do
    each of its elements'. -/
theorem symValVars_array_mem_below_subset {c : ZKConfig} (arr : SymArray c) (s : SimpleSymVal c)
    (hs : s ∈ arr.toList) (vs : VarSet) (hsub : symValVars (.array arr) ⊆ vs) :
    simpleValVars s ⊆ vs := by
  intro v hv
  apply hsub
  simp only [symValVars]
  rw [← Array.foldl_toList]
  exact foldl_union_mem_subset simpleValVars arr.toList s hs emptyVarSet v hv

/-- The extra equation `mergeSimpleSymVal` conjoins onto `tbExtra` keeps it fresh below the new
    counter -- it only ever mentions vars already below the old counter (`tbExtra`, `svTb`
    themselves) or the freshly-minted `nextVarId`, which sits just below the new counter. -/
theorem mergeSimpleSymVal_tbExtra_fresh {c : ZKConfig}
    (nextVarId : Nat) (tbExtra ebExtra : FFFormula c) (svTb svEb : SimpleSymVal c)
    (hfresh : varSetBelow (ffVarsOfFormula tbExtra ∪ bVarsOfFormula tbExtra) nextVarId)
    (hsvTbFresh : varSetBelow (simpleValVars svTb) nextVarId) :
    varSetBelow
      (ffVarsOfFormula (mergeSimpleSymVal nextVarId tbExtra ebExtra svTb svEb).2.2.1 ∪
       bVarsOfFormula (mergeSimpleSymVal nextVarId tbExtra ebExtra svTb svEb).2.2.1)
      (mergeSimpleSymVal nextVarId tbExtra ebExtra svTb svEb).2.1 := by
  simp only [mergeSimpleSymVal]
  split
  · exact hfresh
  · simp only [ffVarsOfFormula, bVarsOfFormula, ffVarsOfTerm_simpleSymValToTerm,
      bVarsOfTerm_simpleSymValToTerm, ffVarsOfTerm, bVarsOfTerm]
    have htbBound : varSetBelow (ffVarsOfFormula tbExtra ∪ bVarsOfFormula tbExtra) (nextVarId + 1) :=
      varSetBelow_mono (Nat.le_succ _) hfresh
    have hsvBound : varSetBelow (simpleValVars svTb) (nextVarId + 1) :=
      varSetBelow_mono (Nat.le_succ _) hsvTbFresh
    apply varSetBelow_union
    · apply varSetBelow_union
      · exact fun v hv => htbBound v (Std.TreeSet.mem_union_of_left hv)
      · exact varSetBelow_union varSetBelow_singleton_ffv hsvBound
    · apply varSetBelow_union
      · exact fun v hv => htbBound v (Std.TreeSet.mem_union_of_right hv)
      · exact varSetBelow_union (fun v hv => absurd hv Std.TreeSet.not_mem_emptyc)
          (fun v hv => absurd hv Std.TreeSet.not_mem_emptyc)

/-- Mirror of `mergeSimpleSymVal_tbExtra_fresh`, for `ebExtra`. -/
theorem mergeSimpleSymVal_ebExtra_fresh {c : ZKConfig}
    (nextVarId : Nat) (tbExtra ebExtra : FFFormula c) (svTb svEb : SimpleSymVal c)
    (hfresh : varSetBelow (ffVarsOfFormula ebExtra ∪ bVarsOfFormula ebExtra) nextVarId)
    (hsvEbFresh : varSetBelow (simpleValVars svEb) nextVarId) :
    varSetBelow
      (ffVarsOfFormula (mergeSimpleSymVal nextVarId tbExtra ebExtra svTb svEb).2.2.2 ∪
       bVarsOfFormula (mergeSimpleSymVal nextVarId tbExtra ebExtra svTb svEb).2.2.2)
      (mergeSimpleSymVal nextVarId tbExtra ebExtra svTb svEb).2.1 := by
  simp only [mergeSimpleSymVal]
  split
  · exact hfresh
  · simp only [ffVarsOfFormula, bVarsOfFormula, ffVarsOfTerm_simpleSymValToTerm,
      bVarsOfTerm_simpleSymValToTerm, ffVarsOfTerm, bVarsOfTerm]
    have hebBound : varSetBelow (ffVarsOfFormula ebExtra ∪ bVarsOfFormula ebExtra) (nextVarId + 1) :=
      varSetBelow_mono (Nat.le_succ _) hfresh
    have hsvBound : varSetBelow (simpleValVars svEb) (nextVarId + 1) :=
      varSetBelow_mono (Nat.le_succ _) hsvEbFresh
    apply varSetBelow_union
    · apply varSetBelow_union
      · exact fun v hv => hebBound v (Std.TreeSet.mem_union_of_left hv)
      · exact varSetBelow_union varSetBelow_singleton_ffv hsvBound
    · apply varSetBelow_union
      · exact fun v hv => hebBound v (Std.TreeSet.mem_union_of_right hv)
      · exact varSetBelow_union (fun v hv => absurd hv Std.TreeSet.not_mem_emptyc)
          (fun v hv => absurd hv Std.TreeSet.not_mem_emptyc)

/-- Subset-or-fresh analog of `mergeSimpleSymVal_tbExtra_fresh`: every var the merged
    `tbExtra'` mentions is either one the *old* `tbExtra` already had, one `svTb` mentions, or
    genuinely new relative to the counter the merge started from -- needed (unlike the plain
    freshness bound) to relate `tbExtra'`'s footprint back to the *original* input `symEnv`
    rather than just to the merge's own local counter. -/
theorem mergeSimpleSymVal_tbExtra_merged_subset {c : ZKConfig}
    (nextVarId : Nat) (tbExtra ebExtra : FFFormula c) (svTb svEb : SimpleSymVal c) :
    ∀ v ∈ (ffVarsOfFormula (mergeSimpleSymVal nextVarId tbExtra ebExtra svTb svEb).2.2.1 ∪
           bVarsOfFormula (mergeSimpleSymVal nextVarId tbExtra ebExtra svTb svEb).2.2.1),
      v ∈ (ffVarsOfFormula tbExtra ∪ bVarsOfFormula tbExtra) ∨ v ∈ simpleValVars svTb ∨
        nextVarId ≤ varIndex v := by
  simp only [mergeSimpleSymVal]
  split
  · exact fun v hv => Or.inl hv
  · intro v hv
    simp only [ffVarsOfFormula, bVarsOfFormula, ffVarsOfTerm_simpleSymValToTerm,
      bVarsOfTerm_simpleSymValToTerm, ffVarsOfTerm, bVarsOfTerm] at hv
    rcases Std.TreeSet.mem_union_iff.mp hv with hff | hbool
    · rcases Std.TreeSet.mem_union_iff.mp hff with htb | hnew
      · exact Or.inl (Std.TreeSet.mem_union_of_left htb)
      · rcases Std.TreeSet.mem_union_iff.mp hnew with hnv | hsv
        · rcases Std.TreeSet.mem_insert.mp hnv with heq | hmem
          · cases v with
            | ffv m =>
                right; right
                simp only [varIndex]
                have hnm : nextVarId = m := Nat.compare_eq_eq.mp heq
                omega
            | boolv m =>
                rw [show compare (Var.ffv nextVarId) (Var.boolv m) = Ordering.lt from rfl] at heq
                exact absurd heq (by decide)
          · exact absurd hmem Std.TreeSet.not_mem_emptyc
        · exact Or.inr (Or.inl hsv)
    · rcases Std.TreeSet.mem_union_iff.mp hbool with htb | hnew
      · exact Or.inl (Std.TreeSet.mem_union_of_right htb)
      · rcases Std.TreeSet.mem_union_iff.mp hnew with h1 | h2
        · exact absurd h1 Std.TreeSet.not_mem_emptyc
        · exact absurd h2 Std.TreeSet.not_mem_emptyc

/-- Mirror of `mergeSimpleSymVal_tbExtra_merged_subset`, for `ebExtra`. -/
theorem mergeSimpleSymVal_ebExtra_merged_subset {c : ZKConfig}
    (nextVarId : Nat) (tbExtra ebExtra : FFFormula c) (svTb svEb : SimpleSymVal c) :
    ∀ v ∈ (ffVarsOfFormula (mergeSimpleSymVal nextVarId tbExtra ebExtra svTb svEb).2.2.2 ∪
           bVarsOfFormula (mergeSimpleSymVal nextVarId tbExtra ebExtra svTb svEb).2.2.2),
      v ∈ (ffVarsOfFormula ebExtra ∪ bVarsOfFormula ebExtra) ∨ v ∈ simpleValVars svEb ∨
        nextVarId ≤ varIndex v := by
  simp only [mergeSimpleSymVal]
  split
  · exact fun v hv => Or.inl hv
  · intro v hv
    simp only [ffVarsOfFormula, bVarsOfFormula, ffVarsOfTerm_simpleSymValToTerm,
      bVarsOfTerm_simpleSymValToTerm, ffVarsOfTerm, bVarsOfTerm] at hv
    rcases Std.TreeSet.mem_union_iff.mp hv with hff | hbool
    · rcases Std.TreeSet.mem_union_iff.mp hff with heb | hnew
      · exact Or.inl (Std.TreeSet.mem_union_of_left heb)
      · rcases Std.TreeSet.mem_union_iff.mp hnew with hnv | hsv
        · rcases Std.TreeSet.mem_insert.mp hnv with heq | hmem
          · cases v with
            | ffv m =>
                right; right
                simp only [varIndex]
                have hnm : nextVarId = m := Nat.compare_eq_eq.mp heq
                omega
            | boolv m =>
                rw [show compare (Var.ffv nextVarId) (Var.boolv m) = Ordering.lt from rfl] at heq
                exact absurd heq (by decide)
          · exact absurd hmem Std.TreeSet.not_mem_emptyc
        · exact Or.inr (Or.inl hsv)
    · rcases Std.TreeSet.mem_union_iff.mp hbool with heb | hnew
      · exact Or.inl (Std.TreeSet.mem_union_of_right heb)
      · rcases Std.TreeSet.mem_union_iff.mp hnew with h1 | h2
        · exact absurd h1 Std.TreeSet.not_mem_emptyc
        · exact absurd h2 Std.TreeSet.not_mem_emptyc

/-- `mergeSimpleSymVal` only ever grows `tbExtra`'s footprint (by ANDing on a new conjunct, or
    leaving it untouched in the "agree" branch) -- never drops a variable it already
    mentioned. -/
theorem mergeSimpleSymVal_tbExtra_subset {c : ZKConfig}
    (nextVarId : Nat) (tbExtra ebExtra : FFFormula c) (svTb svEb : SimpleSymVal c) :
    (ffVarsOfFormula tbExtra ∪ bVarsOfFormula tbExtra) ⊆
      (ffVarsOfFormula (mergeSimpleSymVal nextVarId tbExtra ebExtra svTb svEb).2.2.1 ∪
       bVarsOfFormula (mergeSimpleSymVal nextVarId tbExtra ebExtra svTb svEb).2.2.1) := by
  simp only [mergeSimpleSymVal]
  split
  · exact fun v hv => hv
  · intro v hv
    simp only [ffVarsOfFormula, bVarsOfFormula]
    rcases Std.TreeSet.mem_union_iff.mp hv with hff | hbool
    · exact Std.TreeSet.mem_union_of_left (Std.TreeSet.mem_union_of_left hff)
    · exact Std.TreeSet.mem_union_of_right (Std.TreeSet.mem_union_of_left hbool)

/-- Mirror of `mergeSimpleSymVal_tbExtra_subset`, for `ebExtra`. -/
theorem mergeSimpleSymVal_ebExtra_subset {c : ZKConfig}
    (nextVarId : Nat) (tbExtra ebExtra : FFFormula c) (svTb svEb : SimpleSymVal c) :
    (ffVarsOfFormula ebExtra ∪ bVarsOfFormula ebExtra) ⊆
      (ffVarsOfFormula (mergeSimpleSymVal nextVarId tbExtra ebExtra svTb svEb).2.2.2 ∪
       bVarsOfFormula (mergeSimpleSymVal nextVarId tbExtra ebExtra svTb svEb).2.2.2) := by
  simp only [mergeSimpleSymVal]
  split
  · exact fun v hv => hv
  · intro v hv
    simp only [ffVarsOfFormula, bVarsOfFormula]
    rcases Std.TreeSet.mem_union_iff.mp hv with hff | hbool
    · exact Std.TreeSet.mem_union_of_left (Std.TreeSet.mem_union_of_left hff)
    · exact Std.TreeSet.mem_union_of_right (Std.TreeSet.mem_union_of_left hbool)

/-- A value fresh below `bound` still matches under any assignment that agrees with the
    original below `bound` -- extending an assignment further out never disturbs an
    already-fresh value's match. -/
theorem simpleValMatches_extend_preserves {c : ZKConfig} (a a' : Assignment c)
    (sv : SimpleSymVal c) (v : FF c) (bound : Nat)
    (hfresh : varSetBelow (simpleValVars sv) bound)
    (hagree : ∀ n, n < bound → a'.ff n = a.ff n)
    (h : simpleValMatches a sv v) : simpleValMatches a' sv v := by
  cases sv with
  | const v' => simpa only [simpleValMatches] using h
  | ffvar vbr =>
      have hlt : vbr.var < bound := hfresh (Var.ffv vbr.var) (by simp [simpleValVars])
      simp only [simpleValMatches] at h ⊢
      rw [hagree vbr.var hlt, h]

/-- Lifts `simpleValMatches_extend_preserves` pointwise across a `List.Forall₂`. -/
theorem forall2_simpleValMatches_extend_preserves {c : ZKConfig} (a a' : Assignment c)
    (svs : List (SimpleSymVal c)) (vs : List (FF c)) (bound : Nat)
    (hfresh : ∀ sv ∈ svs, varSetBelow (simpleValVars sv) bound)
    (hagree : ∀ n, n < bound → a'.ff n = a.ff n)
    (h : List.Forall₂ (simpleValMatches a) svs vs) :
    List.Forall₂ (simpleValMatches a') svs vs := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hd _tl ih =>
      rename_i sv0 v0 svrest vrest
      exact List.Forall₂.cons
        (simpleValMatches_extend_preserves a a' sv0 v0 bound
          (hfresh sv0 (List.mem_cons_self ..)) hagree hd)
        (ih (fun sv hsv => hfresh sv (List.mem_cons_of_mem _ hsv)))

/-- Mirror of `forall2_simpleValMatches_extend_preserves`, over one projection (`Prod.fst` for
    the `tb` side, `Prod.snd` for `eb`) of a list of pairs (needed for the `rest` of a list
    being processed pairwise, e.g. by `mergeSymValue`'s array case). -/
theorem forall2_pairs_simpleValMatches_extend_preserves {c : ZKConfig} (a a' : Assignment c)
    (proj : SimpleSymVal c × SimpleSymVal c → SimpleSymVal c)
    (pairs : List (SimpleSymVal c × SimpleSymVal c)) (vs : List (FF c)) (bound : Nat)
    (hfresh : ∀ p ∈ pairs, varSetBelow (simpleValVars (proj p)) bound)
    (hagree : ∀ n, n < bound → a'.ff n = a.ff n)
    (h : List.Forall₂ (fun p v => simpleValMatches a (proj p) v) pairs vs) :
    List.Forall₂ (fun p v => simpleValMatches a' (proj p) v) pairs vs := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hd _tl ih =>
      rename_i p0 v0 prest vrest
      exact List.Forall₂.cons
        (simpleValMatches_extend_preserves a a' (proj p0) v0 bound
          (hfresh p0 (List.mem_cons_self ..)) hagree hd)
        (ih (fun p hp => hfresh p (List.mem_cons_of_mem _ hp)))

/-- `List.Forall₂` respects `++`. -/
theorem forall2_append {α β : Type} {R : α → β → Prop} {l1 l1' l2 l2' : List _}
    (h1 : List.Forall₂ R l1 l1') (h2 : List.Forall₂ R l2 l2') :
    List.Forall₂ R (l1 ++ l2) (l1' ++ l2') := by
  induction h1 with
  | nil => simpa using h2
  | cons hd _tl ih => exact List.Forall₂.cons hd ih

/-- Pure (assignment-free) monotonicity of the fold `mergeSymValue`'s array case uses: the
    counter only grows. -/
theorem mergeSimpleSymValFoldl_mono {c : ZKConfig} :
    ∀ (pairs : List (SimpleSymVal c × SimpleSymVal c)) (nextVarId : Nat)
      (tbExtra ebExtra : FFFormula c) (revAcc : List (SimpleSymVal c)),
      nextVarId ≤ (pairs.foldl (fun acc p =>
        let (nvi, tbExtrai, ebExtrai, merged) := acc
        let (mergedVal, nv2, tbE2, ebE2) := mergeSimpleSymVal nvi tbExtrai ebExtrai p.1 p.2
        (nv2, tbE2, ebE2, mergedVal :: merged)) (nextVarId, tbExtra, ebExtra, revAcc)).1 := by
  intro pairs
  induction pairs with
  | nil => intro nextVarId tbExtra ebExtra revAcc; exact le_refl _
  | cons p rest ih =>
      intro nextVarId tbExtra ebExtra revAcc
      simp only [List.foldl_cons]
      exact le_trans (mergeSimpleSymVal_mono nextVarId tbExtra ebExtra p.1 p.2)
        (ih (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.1
          (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.1
          (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.2
          ((mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).1 :: revAcc))

/-- Pure (assignment-free) freshness of the fold's accumulated `tbExtra`. -/
theorem mergeSimpleSymValFoldl_tbExtra_fresh {c : ZKConfig} :
    ∀ (pairs : List (SimpleSymVal c × SimpleSymVal c)) (nextVarId : Nat)
      (tbExtra ebExtra : FFFormula c) (revAcc : List (SimpleSymVal c))
      (hfresh : varSetBelow (ffVarsOfFormula tbExtra ∪ bVarsOfFormula tbExtra) nextVarId)
      (hpfresh : ∀ p ∈ pairs, varSetBelow (simpleValVars p.1) nextVarId),
      let result := pairs.foldl (fun acc p =>
        let (nvi, tbExtrai, ebExtrai, merged) := acc
        let (mergedVal, nv2, tbE2, ebE2) := mergeSimpleSymVal nvi tbExtrai ebExtrai p.1 p.2
        (nv2, tbE2, ebE2, mergedVal :: merged)) (nextVarId, tbExtra, ebExtra, revAcc)
      varSetBelow (ffVarsOfFormula result.2.1 ∪ bVarsOfFormula result.2.1) result.1 := by
  intro pairs
  induction pairs with
  | nil => intro nextVarId tbExtra ebExtra revAcc hfresh _hpfresh; exact hfresh
  | cons p rest ih =>
      intro nextVarId tbExtra ebExtra revAcc hfresh hpfresh
      simp only [List.foldl_cons]
      have hp1fresh : varSetBelow (simpleValVars p.1) nextVarId := hpfresh p (List.mem_cons_self ..)
      have htbE1Fresh :=
        mergeSimpleSymVal_tbExtra_fresh nextVarId tbExtra ebExtra p.1 p.2 hfresh hp1fresh
      exact ih (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.1
        (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.1
        (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.2
        ((mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).1 :: revAcc)
        htbE1Fresh
        (fun q hq => varSetBelow_mono (mergeSimpleSymVal_mono nextVarId tbExtra ebExtra p.1 p.2)
          (hpfresh q (List.mem_cons_of_mem _ hq)))

/-- Mirror of `mergeSimpleSymValFoldl_tbExtra_fresh`, for `ebExtra` (only needs `p.2`'s
    freshness, not `p.1`'s). -/
theorem mergeSimpleSymValFoldl_ebExtra_fresh {c : ZKConfig} :
    ∀ (pairs : List (SimpleSymVal c × SimpleSymVal c)) (nextVarId : Nat)
      (tbExtra ebExtra : FFFormula c) (revAcc : List (SimpleSymVal c))
      (hfresh : varSetBelow (ffVarsOfFormula ebExtra ∪ bVarsOfFormula ebExtra) nextVarId)
      (hpfresh : ∀ p ∈ pairs, varSetBelow (simpleValVars p.2) nextVarId),
      let result := pairs.foldl (fun acc p =>
        let (nvi, tbExtrai, ebExtrai, merged) := acc
        let (mergedVal, nv2, tbE2, ebE2) := mergeSimpleSymVal nvi tbExtrai ebExtrai p.1 p.2
        (nv2, tbE2, ebE2, mergedVal :: merged)) (nextVarId, tbExtra, ebExtra, revAcc)
      varSetBelow (ffVarsOfFormula result.2.2.1 ∪ bVarsOfFormula result.2.2.1) result.1 := by
  intro pairs
  induction pairs with
  | nil => intro nextVarId tbExtra ebExtra revAcc hfresh _hpfresh; exact hfresh
  | cons p rest ih =>
      intro nextVarId tbExtra ebExtra revAcc hfresh hpfresh
      simp only [List.foldl_cons]
      have hp2fresh : varSetBelow (simpleValVars p.2) nextVarId := hpfresh p (List.mem_cons_self ..)
      have hebE1Fresh :=
        mergeSimpleSymVal_ebExtra_fresh nextVarId tbExtra ebExtra p.1 p.2 hfresh hp2fresh
      exact ih (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.1
        (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.1
        (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.2
        ((mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).1 :: revAcc)
        hebE1Fresh
        (fun q hq => varSetBelow_mono (mergeSimpleSymVal_mono nextVarId tbExtra ebExtra p.1 p.2)
          (hpfresh q (List.mem_cons_of_mem _ hq)))

/-- Subset-or-fresh analog of `mergeSimpleSymValFoldl_tbExtra_fresh`: every var the fold's
    accumulated `tbExtra` mentions is either one the *starting* `tbExtra` already had, one of
    the pairs' `p.1`s (tracked via a fixed `target` set, since those never change through the
    fold), or genuinely new relative to the *starting* `startVarId`. -/
theorem mergeSimpleSymValFoldl_tbExtra_merged_subset {c : ZKConfig} (target : VarSet)
    (startVarId : Nat) :
    ∀ (pairs : List (SimpleSymVal c × SimpleSymVal c)) (nextVarId : Nat)
      (tbExtra ebExtra : FFFormula c) (revAcc : List (SimpleSymVal c))
      (hstart : startVarId ≤ nextVarId)
      (htbExtraSubset : ∀ v ∈ (ffVarsOfFormula tbExtra ∪ bVarsOfFormula tbExtra),
        v ∈ target ∨ startVarId ≤ varIndex v)
      (hpsubset : ∀ p ∈ pairs, simpleValVars p.1 ⊆ target),
      let result := pairs.foldl (fun acc p =>
        let (nvi, tbExtrai, ebExtrai, merged) := acc
        let (mergedVal, nv2, tbE2, ebE2) := mergeSimpleSymVal nvi tbExtrai ebExtrai p.1 p.2
        (nv2, tbE2, ebE2, mergedVal :: merged)) (nextVarId, tbExtra, ebExtra, revAcc)
      ∀ v ∈ (ffVarsOfFormula result.2.1 ∪ bVarsOfFormula result.2.1),
        v ∈ target ∨ startVarId ≤ varIndex v := by
  intro pairs
  induction pairs with
  | nil => intro nextVarId tbExtra ebExtra revAcc _hstart htbExtraSubset _hpsubset; exact htbExtraSubset
  | cons p rest ih =>
      intro nextVarId tbExtra ebExtra revAcc hstart htbExtraSubset hpsubset
      simp only [List.foldl_cons]
      have hp1subset : simpleValVars p.1 ⊆ target := hpsubset p (List.mem_cons_self ..)
      have hnvMono := mergeSimpleSymVal_mono nextVarId tbExtra ebExtra p.1 p.2
      have htbE1Subset : ∀ v ∈
          (ffVarsOfFormula (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.1 ∪
           bVarsOfFormula (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.1),
          v ∈ target ∨ startVarId ≤ varIndex v := by
        intro v hv
        rcases mergeSimpleSymVal_tbExtra_merged_subset nextVarId tbExtra ebExtra p.1 p.2 v hv with
          h | h | h
        · exact htbExtraSubset v h
        · exact Or.inl (hp1subset v h)
        · exact Or.inr (hstart.trans h)
      exact ih (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.1
        (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.1
        (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.2
        ((mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).1 :: revAcc)
        (hstart.trans hnvMono)
        htbE1Subset
        (fun q hq => hpsubset q (List.mem_cons_of_mem _ hq))

/-- Mirror of `mergeSimpleSymValFoldl_tbExtra_merged_subset`, for `ebExtra` (needs `p.2`'s
    subset, not `p.1`'s). -/
theorem mergeSimpleSymValFoldl_ebExtra_merged_subset {c : ZKConfig} (target : VarSet)
    (startVarId : Nat) :
    ∀ (pairs : List (SimpleSymVal c × SimpleSymVal c)) (nextVarId : Nat)
      (tbExtra ebExtra : FFFormula c) (revAcc : List (SimpleSymVal c))
      (hstart : startVarId ≤ nextVarId)
      (hebExtraSubset : ∀ v ∈ (ffVarsOfFormula ebExtra ∪ bVarsOfFormula ebExtra),
        v ∈ target ∨ startVarId ≤ varIndex v)
      (hpsubset : ∀ p ∈ pairs, simpleValVars p.2 ⊆ target),
      let result := pairs.foldl (fun acc p =>
        let (nvi, tbExtrai, ebExtrai, merged) := acc
        let (mergedVal, nv2, tbE2, ebE2) := mergeSimpleSymVal nvi tbExtrai ebExtrai p.1 p.2
        (nv2, tbE2, ebE2, mergedVal :: merged)) (nextVarId, tbExtra, ebExtra, revAcc)
      ∀ v ∈ (ffVarsOfFormula result.2.2.1 ∪ bVarsOfFormula result.2.2.1),
        v ∈ target ∨ startVarId ≤ varIndex v := by
  intro pairs
  induction pairs with
  | nil => intro nextVarId tbExtra ebExtra revAcc _hstart hebExtraSubset _hpsubset; exact hebExtraSubset
  | cons p rest ih =>
      intro nextVarId tbExtra ebExtra revAcc hstart hebExtraSubset hpsubset
      simp only [List.foldl_cons]
      have hp2subset : simpleValVars p.2 ⊆ target := hpsubset p (List.mem_cons_self ..)
      have hnvMono := mergeSimpleSymVal_mono nextVarId tbExtra ebExtra p.1 p.2
      have hebE1Subset : ∀ v ∈
          (ffVarsOfFormula (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.2 ∪
           bVarsOfFormula (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.2),
          v ∈ target ∨ startVarId ≤ varIndex v := by
        intro v hv
        rcases mergeSimpleSymVal_ebExtra_merged_subset nextVarId tbExtra ebExtra p.1 p.2 v hv with
          h | h | h
        · exact hebExtraSubset v h
        · exact Or.inl (hp2subset v h)
        · exact Or.inr (hstart.trans h)
      exact ih (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.1
        (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.1
        (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.2
        ((mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).1 :: revAcc)
        (hstart.trans hnvMono)
        hebE1Subset
        (fun q hq => hpsubset q (List.mem_cons_of_mem _ hq))

/-- Pure (assignment-free) monotonicity of the fold's accumulated `tbExtra`'s footprint: it
    only ever grows. -/
theorem mergeSimpleSymValFoldl_tbExtra_subset {c : ZKConfig} :
    ∀ (pairs : List (SimpleSymVal c × SimpleSymVal c)) (nextVarId : Nat)
      (tbExtra ebExtra : FFFormula c) (revAcc : List (SimpleSymVal c)),
      let result := pairs.foldl (fun acc p =>
        let (nvi, tbExtrai, ebExtrai, merged) := acc
        let (mergedVal, nv2, tbE2, ebE2) := mergeSimpleSymVal nvi tbExtrai ebExtrai p.1 p.2
        (nv2, tbE2, ebE2, mergedVal :: merged)) (nextVarId, tbExtra, ebExtra, revAcc)
      (ffVarsOfFormula tbExtra ∪ bVarsOfFormula tbExtra) ⊆
        (ffVarsOfFormula result.2.1 ∪ bVarsOfFormula result.2.1) := by
  intro pairs
  induction pairs with
  | nil => intro nextVarId tbExtra ebExtra revAcc; exact fun v hv => hv
  | cons p rest ih =>
      intro nextVarId tbExtra ebExtra revAcc
      simp only [List.foldl_cons]
      exact fun v hv =>
        ih (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.1
          (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.1
          (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.2
          ((mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).1 :: revAcc)
          v (mergeSimpleSymVal_tbExtra_subset nextVarId tbExtra ebExtra p.1 p.2 v hv)

/-- Mirror of `mergeSimpleSymValFoldl_tbExtra_subset`, for `ebExtra`. -/
theorem mergeSimpleSymValFoldl_ebExtra_subset {c : ZKConfig} :
    ∀ (pairs : List (SimpleSymVal c × SimpleSymVal c)) (nextVarId : Nat)
      (tbExtra ebExtra : FFFormula c) (revAcc : List (SimpleSymVal c)),
      let result := pairs.foldl (fun acc p =>
        let (nvi, tbExtrai, ebExtrai, merged) := acc
        let (mergedVal, nv2, tbE2, ebE2) := mergeSimpleSymVal nvi tbExtrai ebExtrai p.1 p.2
        (nv2, tbE2, ebE2, mergedVal :: merged)) (nextVarId, tbExtra, ebExtra, revAcc)
      (ffVarsOfFormula ebExtra ∪ bVarsOfFormula ebExtra) ⊆
        (ffVarsOfFormula result.2.2.1 ∪ bVarsOfFormula result.2.2.1) := by
  intro pairs
  induction pairs with
  | nil => intro nextVarId tbExtra ebExtra revAcc; exact fun v hv => hv
  | cons p rest ih =>
      intro nextVarId tbExtra ebExtra revAcc
      simp only [List.foldl_cons]
      exact fun v hv =>
        ih (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.1
          (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.1
          (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.2
          ((mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).1 :: revAcc)
          v (mergeSimpleSymVal_ebExtra_subset nextVarId tbExtra ebExtra p.1 p.2 v hv)

/-- Base case of `mergeSimpleSymValFoldl_tbExtra_eval_mono`, for a single `mergeSimpleSymVal`
    step: if the (possibly-grown) result satisfies a fixed assignment, so did the input it grew
    from. -/
theorem mergeSimpleSymVal_tbExtra_eval_mono {c : ZKConfig} (gconf : GlobalConfig c)
    (ms : List (FFMacro c)) (assignment' : Assignment c)
    (nextVarId : Nat) (tbExtra ebExtra : FFFormula c) (svTb svEb : SimpleSymVal c) :
    evalFormula gconf assignment'
        (mergeSimpleSymVal nextVarId tbExtra ebExtra svTb svEb).2.2.1 ms = Except.ok true →
    evalFormula gconf assignment' tbExtra ms = Except.ok true := by
  rcases Bool.eq_false_or_eq_true (simpleSymValAgree svTb svEb) with hagree | hagree
  · simp only [mergeSimpleSymVal, hagree, if_true]; exact fun h => h
  · intro h
    simp only [mergeSimpleSymVal, hagree, Bool.false_eq_true, if_false] at h
    exact (evalFormula_and_elim gconf assignment' tbExtra
      (.eq (FFTerm.var nextVarId) (simpleSymValToTerm svTb)) ms h).1

/-- Mirror of `mergeSimpleSymVal_tbExtra_eval_mono`, for `ebExtra`. -/
theorem mergeSimpleSymVal_ebExtra_eval_mono {c : ZKConfig} (gconf : GlobalConfig c)
    (ms : List (FFMacro c)) (assignment' : Assignment c)
    (nextVarId : Nat) (tbExtra ebExtra : FFFormula c) (svTb svEb : SimpleSymVal c) :
    evalFormula gconf assignment'
        (mergeSimpleSymVal nextVarId tbExtra ebExtra svTb svEb).2.2.2 ms = Except.ok true →
    evalFormula gconf assignment' ebExtra ms = Except.ok true := by
  rcases Bool.eq_false_or_eq_true (simpleSymValAgree svTb svEb) with hagree | hagree
  · simp only [mergeSimpleSymVal, hagree, if_true]; exact fun h => h
  · intro h
    simp only [mergeSimpleSymVal, hagree, Bool.false_eq_true, if_false] at h
    exact (evalFormula_and_elim gconf assignment' ebExtra
      (.eq (FFTerm.var nextVarId) (simpleSymValToTerm svEb)) ms h).1

/-- If the fold's *final* accumulated `tbExtra` is satisfied by a fixed assignment, so is the
    *starting* `tbExtra` it was built on top of -- since the fold only ever grows `tbExtra` via
    `.and`, satisfying the whole conjunction satisfies every conjunct peeled off along the way
    (`evalFormula_and_elim`, applied once per step). This is what lets a completeness proof
    that only knows "the final formula holds" recover "this specific step's formula holds",
    working through the fold from the far end backwards via the induction itself. -/
theorem mergeSimpleSymValFoldl_tbExtra_eval_mono {c : ZKConfig} (gconf : GlobalConfig c)
    (ms : List (FFMacro c)) (assignment' : Assignment c) :
    ∀ (pairs : List (SimpleSymVal c × SimpleSymVal c)) (nextVarId : Nat)
      (tbExtra ebExtra : FFFormula c) (revAcc : List (SimpleSymVal c)),
      evalFormula gconf assignment' (pairs.foldl (fun acc p =>
        let (nvi, tbExtrai, ebExtrai, merged) := acc
        let (mergedVal, nv2, tbE2, ebE2) := mergeSimpleSymVal nvi tbExtrai ebExtrai p.1 p.2
        (nv2, tbE2, ebE2, mergedVal :: merged)) (nextVarId, tbExtra, ebExtra, revAcc)).2.1 ms
        = Except.ok true →
      evalFormula gconf assignment' tbExtra ms = Except.ok true := by
  intro pairs
  induction pairs with
  | nil => intro nextVarId tbExtra ebExtra revAcc h; exact h
  | cons p rest ih =>
      intro nextVarId tbExtra ebExtra revAcc h
      simp only [List.foldl_cons] at h
      have h1 := ih (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.1
        (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.1
        (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.2
        ((mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).1 :: revAcc) h
      rcases Bool.eq_false_or_eq_true (simpleSymValAgree p.1 p.2) with hagree | hagree
      · simpa only [mergeSimpleSymVal, hagree, if_true] using h1
      · simp only [mergeSimpleSymVal, hagree, Bool.false_eq_true, if_false] at h1
        exact (evalFormula_and_elim gconf assignment' tbExtra
          (.eq (FFTerm.var nextVarId) (simpleSymValToTerm p.1)) ms h1).1

/-- Mirror of `mergeSimpleSymValFoldl_tbExtra_eval_mono`, for `ebExtra`. -/
theorem mergeSimpleSymValFoldl_ebExtra_eval_mono {c : ZKConfig} (gconf : GlobalConfig c)
    (ms : List (FFMacro c)) (assignment' : Assignment c) :
    ∀ (pairs : List (SimpleSymVal c × SimpleSymVal c)) (nextVarId : Nat)
      (tbExtra ebExtra : FFFormula c) (revAcc : List (SimpleSymVal c)),
      evalFormula gconf assignment' (pairs.foldl (fun acc p =>
        let (nvi, tbExtrai, ebExtrai, merged) := acc
        let (mergedVal, nv2, tbE2, ebE2) := mergeSimpleSymVal nvi tbExtrai ebExtrai p.1 p.2
        (nv2, tbE2, ebE2, mergedVal :: merged)) (nextVarId, tbExtra, ebExtra, revAcc)).2.2.1 ms
        = Except.ok true →
      evalFormula gconf assignment' ebExtra ms = Except.ok true := by
  intro pairs
  induction pairs with
  | nil => intro nextVarId tbExtra ebExtra revAcc h; exact h
  | cons p rest ih =>
      intro nextVarId tbExtra ebExtra revAcc h
      simp only [List.foldl_cons] at h
      have h1 := ih (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.1
        (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.1
        (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.2
        ((mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).1 :: revAcc) h
      rcases Bool.eq_false_or_eq_true (simpleSymValAgree p.1 p.2) with hagree | hagree
      · simpa only [mergeSimpleSymVal, hagree, if_true] using h1
      · simp only [mergeSimpleSymVal, hagree, Bool.false_eq_true, if_false] at h1
        exact (evalFormula_and_elim gconf assignment' ebExtra
          (.eq (FFTerm.var nextVarId) (simpleSymValToTerm p.2)) ms h1).1

/-- Pure (assignment-free) freshness of the fold's accumulated merged list: every entry is
    below the new counter. -/
theorem mergeSimpleSymValFoldl_result_fresh {c : ZKConfig} :
    ∀ (pairs : List (SimpleSymVal c × SimpleSymVal c)) (nextVarId : Nat)
      (tbExtra ebExtra : FFFormula c) (revAcc : List (SimpleSymVal c))
      (hrevAccFresh : ∀ sv ∈ revAcc, varSetBelow (simpleValVars sv) nextVarId)
      (hpfresh : ∀ p ∈ pairs, varSetBelow (simpleValVars p.1) nextVarId),
      let result := pairs.foldl (fun acc p =>
        let (nvi, tbExtrai, ebExtrai, merged) := acc
        let (mergedVal, nv2, tbE2, ebE2) := mergeSimpleSymVal nvi tbExtrai ebExtrai p.1 p.2
        (nv2, tbE2, ebE2, mergedVal :: merged)) (nextVarId, tbExtra, ebExtra, revAcc)
      ∀ sv ∈ result.2.2.2, varSetBelow (simpleValVars sv) result.1 := by
  intro pairs
  induction pairs with
  | nil => intro nextVarId tbExtra ebExtra revAcc hrevAccFresh _hpfresh; exact hrevAccFresh
  | cons p rest ih =>
      intro nextVarId tbExtra ebExtra revAcc hrevAccFresh hpfresh
      simp only [List.foldl_cons]
      have hp1fresh : varSetBelow (simpleValVars p.1) nextVarId := hpfresh p (List.mem_cons_self ..)
      have hnvMono := mergeSimpleSymVal_mono nextVarId tbExtra ebExtra p.1 p.2
      have hmergedFresh := mergeSimpleSymVal_result_fresh nextVarId tbExtra ebExtra p.1 p.2 hp1fresh
      have hnewAccFresh : ∀ sv ∈ (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).1 :: revAcc,
          varSetBelow (simpleValVars sv) (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.1 := by
        intro sv hsv
        rcases List.mem_cons.mp hsv with heq | hmem
        · rw [heq]; exact hmergedFresh
        · exact varSetBelow_mono hnvMono (hrevAccFresh sv hmem)
      exact ih (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.1
        (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.1
        (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.2
        ((mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).1 :: revAcc)
        hnewAccFresh
        (fun q hq => varSetBelow_mono hnvMono (hpfresh q (List.mem_cons_of_mem _ hq)))

/-- Subset-or-fresh analog of `mergeSimpleSymValFoldl_result_fresh`: every var the fold's
    accumulated merged list mentions is either one the original pairs' `p.1`s already had
    (tracked via a fixed `target` set, since `p.1`s' own vars never change through the fold),
    or is genuinely new relative to the *starting* `startVarId` (not the per-step counter). -/
theorem mergeSimpleSymValFoldl_merged_subset {c : ZKConfig} (target : VarSet) (startVarId : Nat) :
    ∀ (pairs : List (SimpleSymVal c × SimpleSymVal c)) (nextVarId : Nat)
      (tbExtra ebExtra : FFFormula c) (revAcc : List (SimpleSymVal c))
      (hstart : startVarId ≤ nextVarId)
      (hrevAccSubset : ∀ sv ∈ revAcc, ∀ v ∈ simpleValVars sv, v ∈ target ∨ startVarId ≤ varIndex v)
      (hpsubset : ∀ p ∈ pairs, simpleValVars p.1 ⊆ target),
      let result := pairs.foldl (fun acc p =>
        let (nvi, tbExtrai, ebExtrai, merged) := acc
        let (mergedVal, nv2, tbE2, ebE2) := mergeSimpleSymVal nvi tbExtrai ebExtrai p.1 p.2
        (nv2, tbE2, ebE2, mergedVal :: merged)) (nextVarId, tbExtra, ebExtra, revAcc)
      ∀ sv ∈ result.2.2.2, ∀ v ∈ simpleValVars sv, v ∈ target ∨ startVarId ≤ varIndex v := by
  intro pairs
  induction pairs with
  | nil => intro nextVarId tbExtra ebExtra revAcc _hstart hrevAccSubset _hpsubset; exact hrevAccSubset
  | cons p rest ih =>
      intro nextVarId tbExtra ebExtra revAcc hstart hrevAccSubset hpsubset
      simp only [List.foldl_cons]
      have hp1subset : simpleValVars p.1 ⊆ target := hpsubset p (List.mem_cons_self ..)
      have hnvMono := mergeSimpleSymVal_mono nextVarId tbExtra ebExtra p.1 p.2
      have hmergedSubset := mergeSimpleSymVal_merged_subset nextVarId tbExtra ebExtra p.1 p.2
      have hnewAccSubset : ∀ sv ∈ (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).1 :: revAcc,
          ∀ v ∈ simpleValVars sv, v ∈ target ∨ startVarId ≤ varIndex v := by
        intro sv hsv v hv
        rcases List.mem_cons.mp hsv with heq | hmem
        · rw [heq] at hv
          rcases hmergedSubset v hv with h | h
          · exact Or.inl (hp1subset v h)
          · exact Or.inr (hstart.trans h)
        · exact hrevAccSubset sv hmem v hv
      exact ih (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.1
        (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.1
        (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.2
        ((mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).1 :: revAcc)
        (hstart.trans hnvMono)
        hnewAccSubset
        (fun q hq => hpsubset q (List.mem_cons_of_mem _ hq))

/-- If every element of a list is fresh below a bound, so is the union-fold over it (starting
    from any already-below-bound accumulator). -/
theorem varSetBelow_foldl_union {α : Type} (f : α → VarSet) (l : List α) (bound : Nat)
    (init : VarSet) (hinit : varSetBelow init bound) (hl : ∀ x ∈ l, varSetBelow (f x) bound) :
    varSetBelow (l.foldl (fun acc x => acc ∪ f x) init) bound := by
  induction l generalizing init with
  | nil => exact hinit
  | cons x xs ih =>
      simp only [List.foldl_cons]
      exact ih (init ∪ f x) (varSetBelow_union hinit (hl x (List.mem_cons_self ..)))
        (fun y hy => hl y (List.mem_cons_of_mem _ hy))

/-- Subset-or-fresh analog of `varSetBelow_foldl_union`: if every element's contribution (and
    `init`) lands in a fixed `target` set or is fresh above `bound`, so does the whole
    union-fold. -/
theorem foldl_union_subset_or_bound {α : Type} (f : α → VarSet) (target : VarSet) (l : List α)
    (bound : Nat) (init : VarSet) (hinit : ∀ v ∈ init, v ∈ target ∨ bound ≤ varIndex v)
    (hl : ∀ a ∈ l, ∀ v ∈ f a, v ∈ target ∨ bound ≤ varIndex v) :
    ∀ v ∈ l.foldl (fun acc a => acc ∪ f a) init, v ∈ target ∨ bound ≤ varIndex v := by
  induction l generalizing init with
  | nil => exact hinit
  | cons a xs ih =>
      simp only [List.foldl_cons]
      refine ih (init ∪ f a) ?_ (fun a' ha' => hl a' (List.mem_cons_of_mem _ ha'))
      intro v hv
      rcases Std.TreeSet.mem_union_iff.mp hv with hv1 | hv2
      · exact hinit v hv1
      · exact hl a (List.mem_cons_self ..) v hv2

/-- The merged value `mergeSymValue` produces is fresh below the new counter. -/
theorem mergeSymValue_result_fresh {c : ZKConfig}
    (nextVarId : Nat) (tbExtra ebExtra : FFFormula c) (svTb svEb : SymValue c)
    (merged : SymValue c) (nv' : Nat) (tbExtra' ebExtra' : FFFormula c)
    (heq : mergeSymValue nextVarId tbExtra ebExtra svTb svEb
      = Except.ok (merged, nv', tbExtra', ebExtra'))
    (hsvTbFresh : varSetBelow (symValVars svTb) nextVarId) :
    varSetBelow (symValVars merged) nv' := by
  cases svTb with
  | simple s1 =>
      cases svEb with
      | simple s2 =>
          simp only [mergeSymValue, Except.ok.injEq, Prod.mk.injEq] at heq
          rw [← heq.1, ← heq.2.1, symValVars]
          exact mergeSimpleSymVal_result_fresh nextVarId tbExtra ebExtra s1 s2 hsvTbFresh
      | array _ => exact absurd heq (by simp [mergeSymValue])
  | array arrTb =>
      cases svEb with
      | simple _ => exact absurd heq (by simp [mergeSymValue])
      | array arrEb =>
          simp only [mergeSymValue] at heq
          split at heq
          · simp only [Except.ok.injEq, Prod.mk.injEq] at heq
            rw [← heq.1]
            have hresultFresh := mergeSimpleSymValFoldl_result_fresh
              (arrTb.toList.zip arrEb.toList) nextVarId tbExtra ebExtra [] (by simp)
              (fun p hp => symValVars_array_mem_below arrTb p.1 (List.of_mem_zip hp).1
                nextVarId hsvTbFresh)
            rw [← heq.2.1]
            simp only [symValVars]
            rw [← Array.foldl_toList, List.toList_toArray]
            exact varSetBelow_foldl_union simpleValVars _ _ emptyVarSet
              (fun v hv => absurd hv Std.TreeSet.not_mem_emptyc)
              (fun sv hsv => hresultFresh sv (List.mem_reverse.mp hsv))
          · exact absurd heq (by simp)

/-- Subset-or-fresh analog of `mergeSymValue_result_fresh`: every var the merged value
    mentions is either one `svTb` already had, or is genuinely new relative to the counter
    the merge started from. -/
theorem mergeSymValue_merged_subset {c : ZKConfig}
    (nextVarId : Nat) (tbExtra ebExtra : FFFormula c) (svTb svEb : SymValue c)
    (merged : SymValue c) (nv' : Nat) (tbExtra' ebExtra' : FFFormula c)
    (heq : mergeSymValue nextVarId tbExtra ebExtra svTb svEb
      = Except.ok (merged, nv', tbExtra', ebExtra')) :
    ∀ v ∈ symValVars merged, v ∈ symValVars svTb ∨ nextVarId ≤ varIndex v := by
  cases svTb with
  | simple s1 =>
      cases svEb with
      | simple s2 =>
          simp only [mergeSymValue, Except.ok.injEq, Prod.mk.injEq] at heq
          rw [← heq.1]
          simp only [symValVars]
          exact mergeSimpleSymVal_merged_subset nextVarId tbExtra ebExtra s1 s2
      | array _ => exact absurd heq (by simp [mergeSymValue])
  | array arrTb =>
      cases svEb with
      | simple _ => exact absurd heq (by simp [mergeSymValue])
      | array arrEb =>
          simp only [mergeSymValue] at heq
          split at heq
          · simp only [Except.ok.injEq, Prod.mk.injEq] at heq
            rw [← heq.1]
            have hresultSubset := mergeSimpleSymValFoldl_merged_subset (symValVars (.array arrTb))
              nextVarId (arrTb.toList.zip arrEb.toList) nextVarId tbExtra ebExtra [] (le_refl _)
              (by simp)
              (fun p hp => symValVars_array_mem_below_subset arrTb p.1 (List.of_mem_zip hp).1
                (symValVars (.array arrTb)) (fun v hv => hv))
            intro v hv
            simp only [symValVars] at hv
            rw [← Array.foldl_toList, List.toList_toArray] at hv
            exact foldl_union_subset_or_bound simpleValVars (symValVars (.array arrTb)) _ nextVarId
              emptyVarSet (fun v hv => absurd hv Std.TreeSet.not_mem_emptyc)
              (fun sv hsv => hresultSubset sv (List.mem_reverse.mp hsv)) v hv
          · exact absurd heq (by simp)

/-- Lifts `simpleValMatches_extend_preserves` to whole symbolic values (scalars directly;
    arrays pointwise via `forall2_simpleValMatches_extend_preserves`). -/
theorem symValMatches_extend_preserves {c : ZKConfig} (a a' : Assignment c)
    (sv : SymValue c) (v : Value c) (bound : Nat)
    (hfresh : varSetBelow (symValVars sv) bound)
    (hagree : ∀ n, n < bound → a'.ff n = a.ff n)
    (h : symValMatches a sv v) : symValMatches a' sv v := by
  cases sv with
  | simple s =>
      cases v with
      | scalar v' =>
          simp only [symValMatches] at h ⊢
          exact simpleValMatches_extend_preserves a a' s v' bound hfresh hagree h
      | array _ => simp only [symValMatches] at h
  | array arr =>
      cases v with
      | scalar _ => simp only [symValMatches] at h
      | array varr =>
          simp only [symValMatches] at h ⊢
          exact forall2_simpleValMatches_extend_preserves a a' arr.toList varr.toList bound
            (fun s hs => symValVars_array_mem_below arr s hs bound hfresh) hagree h

/-- Folding `mergeSimpleSymVal` down a list of paired branch-values (as `mergeSymValue`'s array
    case does), starting from an arbitrary already-processed prefix (`revAcc`, most-recently
    processed first -- matching how the fold conses new results onto the front), extends a
    matching assignment to one matching the *whole* processed list, without disturbing
    anything already fixed below the starting counter. Generalized over `revAcc`/`revAccVals`
    so the induction goes through (`revAccVals` tracks `revAcc`'s matches in *forward* order,
    i.e. `revAcc.reverse`'s order, so that new matches can simply be appended as processing
    proceeds); `mergeSymValue` itself only ever calls this with `revAcc = revAccVals = []`. -/
theorem mergeSimpleSymValFoldl_extend_tb {c : ZKConfig}
    (gconf : GlobalConfig c) (ms : List (FFMacro c)) :
    ∀ (pairs : List (SimpleSymVal c × SimpleSymVal c))
      (nextVarId : Nat) (tbExtra ebExtra : FFFormula c)
      (revAcc : List (SimpleSymVal c)) (revAccVals : List (FF c))
      (hfresh : varSetBelow (ffVarsOfFormula tbExtra ∪ bVarsOfFormula tbExtra) nextVarId)
      (hrevAccFresh : ∀ sv ∈ revAcc, varSetBelow (simpleValVars sv) nextVarId)
      (hpfresh : ∀ p ∈ pairs, varSetBelow (simpleValVars p.1) nextVarId)
      (a : Assignment c)
      (haccMatch : List.Forall₂ (simpleValMatches a) revAcc.reverse revAccVals)
      (htbExtra : evalFormula gconf a tbExtra ms = Except.ok true)
      (vsTb : List (FF c))
      (hpMatch : List.Forall₂ (fun p v => simpleValMatches a p.1 v) pairs vsTb),
      ∃ a' nv tbE ebE mergedRev,
        pairs.foldl (fun acc p =>
          let (nvi, tbExtrai, ebExtrai, merged) := acc
          let (mergedVal, nv2, tbE2, ebE2) := mergeSimpleSymVal nvi tbExtrai ebExtrai p.1 p.2
          (nv2, tbE2, ebE2, mergedVal :: merged)) (nextVarId, tbExtra, ebExtra, revAcc)
          = (nv, tbE, ebE, mergedRev) ∧
        nextVarId ≤ nv ∧
        (∀ n, n < nextVarId → a'.ff n = a.ff n) ∧ (∀ n, a'.bool n = a.bool n) ∧
        (∀ n, Var.ffv n ∉ (ffVarsOfFormula tbE ∪ bVarsOfFormula tbE) → a'.ff n = a.ff n) ∧
        List.Forall₂ (simpleValMatches a') mergedRev.reverse (revAccVals ++ vsTb) ∧
        evalFormula gconf a' tbE ms = Except.ok true := by
  intro pairs
  induction pairs with
  | nil =>
      intro nextVarId tbExtra ebExtra revAcc revAccVals hfresh hrevAccFresh hpfresh
        a haccMatch htbExtra vsTb hpMatch
      cases hpMatch
      exact ⟨a, nextVarId, tbExtra, ebExtra, revAcc, rfl, le_refl _, fun _ _ => rfl, fun _ => rfl,
        fun _ _ => rfl, by simpa using haccMatch, htbExtra⟩
  | cons p rest ih =>
      intro nextVarId tbExtra ebExtra revAcc revAccVals hfresh hrevAccFresh hpfresh
        a haccMatch htbExtra vsTb hpMatch
      cases hpMatch with
      | cons hv0 hvrest =>
          rename_i v0 vsRest
          have hp1fresh : varSetBelow (simpleValVars p.1) nextVarId :=
            hpfresh p (List.mem_cons_self ..)
          obtain ⟨a1, ha1_range, ha1_bool, ha1_frame, ha1_match, ha1_extra⟩ :=
            mergeSimpleSymVal_extend_tb gconf ms nextVarId tbExtra ebExtra p.1 p.2
              hfresh hp1fresh a v0 hv0 htbExtra
          have ha1_below : ∀ n, n < nextVarId → a1.ff n = a.ff n :=
            fun n hn => ha1_range n (Nat.ne_of_lt hn)
          have haccMatch1 : List.Forall₂ (simpleValMatches a1) revAcc.reverse revAccVals :=
            forall2_simpleValMatches_extend_preserves a a1 revAcc.reverse revAccVals nextVarId
              (fun sv hsv => hrevAccFresh sv (List.mem_reverse.mp hsv)) ha1_below haccMatch
          have hvrest1 : List.Forall₂ (fun p v => simpleValMatches a1 p.1 v) rest vsRest :=
            forall2_pairs_simpleValMatches_extend_preserves a a1 Prod.fst rest vsRest nextVarId
              (fun q hq => hpfresh q (List.mem_cons_of_mem _ hq)) ha1_below hvrest
          have hnvMono : nextVarId ≤ (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.1 :=
            mergeSimpleSymVal_mono nextVarId tbExtra ebExtra p.1 p.2
          have hmergedFresh :
              varSetBelow (simpleValVars (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).1)
                (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.1 :=
            mergeSimpleSymVal_result_fresh nextVarId tbExtra ebExtra p.1 p.2 hp1fresh
          have htbEFresh : varSetBelow
              (ffVarsOfFormula (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.1 ∪
               bVarsOfFormula (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.1)
              (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.1 :=
            mergeSimpleSymVal_tbExtra_fresh nextVarId tbExtra ebExtra p.1 p.2 hfresh hp1fresh
          have hrest_fresh' : ∀ q ∈ rest,
              varSetBelow (simpleValVars q.1) (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.1 :=
            fun q hq => varSetBelow_mono hnvMono (hpfresh q (List.mem_cons_of_mem _ hq))
          have hnewAccFresh : ∀ sv ∈ (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).1 :: revAcc,
              varSetBelow (simpleValVars sv) (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.1 := by
            intro sv hsv
            rcases List.mem_cons.mp hsv with heq | hmem
            · rw [heq]; exact hmergedFresh
            · exact varSetBelow_mono hnvMono (hrevAccFresh sv hmem)
          have hnewAccMatch : List.Forall₂ (simpleValMatches a1)
              ((mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).1 :: revAcc).reverse
              (revAccVals ++ [v0]) := by
            rw [List.reverse_cons]
            exact forall2_append haccMatch1 (List.Forall₂.cons ha1_match List.Forall₂.nil)
          obtain ⟨a', nv, tbE, ebE, mergedRev, hfold, hnvMono2, ha'_range, ha'_bool, ha'_frame,
              ha'_match, ha'_extra⟩ :=
            ih (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.1
              (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.1
              (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.2
              ((mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).1 :: revAcc) (revAccVals ++ [v0])
              htbEFresh hnewAccFresh hrest_fresh' a1 hnewAccMatch ha1_extra vsRest hvrest1
          refine ⟨a', nv, tbE, ebE, mergedRev, ?_, le_trans hnvMono hnvMono2, ?_,
            fun n => (ha'_bool n).trans (ha1_bool n), ?_, ?_, ha'_extra⟩
          · simpa only [List.foldl_cons] using hfold
          · intro n hn
            rw [ha'_range n (lt_of_lt_of_le hn hnvMono), ha1_below n hn]
          · intro n hn
            have hsubset := mergeSimpleSymValFoldl_tbExtra_subset rest
              (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.1
              (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.1
              (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.2
              ((mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).1 :: revAcc)
            simp only [hfold] at hsubset
            rw [ha'_frame n hn]
            exact ha1_frame n (fun h => hn (hsubset (Var.ffv n) h))
          · simpa only [List.append_assoc, List.singleton_append] using ha'_match

/-- Mirror of `mergeSimpleSymValFoldl_extend_tb`, for the `eb` side. -/
theorem mergeSimpleSymValFoldl_extend_eb {c : ZKConfig}
    (gconf : GlobalConfig c) (ms : List (FFMacro c)) :
    ∀ (pairs : List (SimpleSymVal c × SimpleSymVal c))
      (nextVarId : Nat) (tbExtra ebExtra : FFFormula c)
      (revAcc : List (SimpleSymVal c)) (revAccVals : List (FF c))
      (hfresh : varSetBelow (ffVarsOfFormula ebExtra ∪ bVarsOfFormula ebExtra) nextVarId)
      (hrevAccFresh : ∀ sv ∈ revAcc, varSetBelow (simpleValVars sv) nextVarId)
      (hpfresh1 : ∀ p ∈ pairs, varSetBelow (simpleValVars p.1) nextVarId)
      (hpfresh : ∀ p ∈ pairs, varSetBelow (simpleValVars p.2) nextVarId)
      (a : Assignment c)
      (haccMatch : List.Forall₂ (simpleValMatches a) revAcc.reverse revAccVals)
      (hebExtra : evalFormula gconf a ebExtra ms = Except.ok true)
      (vsEb : List (FF c))
      (hpMatch : List.Forall₂ (fun p v => simpleValMatches a p.2 v) pairs vsEb),
      ∃ a' nv tbE ebE mergedRev,
        pairs.foldl (fun acc p =>
          let (nvi, tbExtrai, ebExtrai, merged) := acc
          let (mergedVal, nv2, tbE2, ebE2) := mergeSimpleSymVal nvi tbExtrai ebExtrai p.1 p.2
          (nv2, tbE2, ebE2, mergedVal :: merged)) (nextVarId, tbExtra, ebExtra, revAcc)
          = (nv, tbE, ebE, mergedRev) ∧
        nextVarId ≤ nv ∧
        (∀ n, n < nextVarId → a'.ff n = a.ff n) ∧ (∀ n, a'.bool n = a.bool n) ∧
        (∀ n, Var.ffv n ∉ (ffVarsOfFormula ebE ∪ bVarsOfFormula ebE) → a'.ff n = a.ff n) ∧
        List.Forall₂ (simpleValMatches a') mergedRev.reverse (revAccVals ++ vsEb) ∧
        evalFormula gconf a' ebE ms = Except.ok true := by
  intro pairs
  induction pairs with
  | nil =>
      intro nextVarId tbExtra ebExtra revAcc revAccVals hfresh hrevAccFresh hpfresh1 hpfresh
        a haccMatch hebExtra vsEb hpMatch
      cases hpMatch
      exact ⟨a, nextVarId, tbExtra, ebExtra, revAcc, rfl, le_refl _, fun _ _ => rfl, fun _ => rfl,
        fun _ _ => rfl, by simpa using haccMatch, hebExtra⟩
  | cons p rest ih =>
      intro nextVarId tbExtra ebExtra revAcc revAccVals hfresh hrevAccFresh hpfresh1 hpfresh
        a haccMatch hebExtra vsEb hpMatch
      cases hpMatch with
      | cons hv0 hvrest =>
          rename_i v0 vsRest
          have hp1fresh : varSetBelow (simpleValVars p.2) nextVarId :=
            hpfresh p (List.mem_cons_self ..)
          have hp1fresh' : varSetBelow (simpleValVars p.1) nextVarId :=
            hpfresh1 p (List.mem_cons_self ..)
          obtain ⟨a1, ha1_range, ha1_bool, ha1_frame, ha1_match, ha1_extra⟩ :=
            mergeSimpleSymVal_extend_eb gconf ms nextVarId tbExtra ebExtra p.1 p.2
              hfresh hp1fresh a v0 hv0 hebExtra
          have ha1_below : ∀ n, n < nextVarId → a1.ff n = a.ff n :=
            fun n hn => ha1_range n (Nat.ne_of_lt hn)
          have haccMatch1 : List.Forall₂ (simpleValMatches a1) revAcc.reverse revAccVals :=
            forall2_simpleValMatches_extend_preserves a a1 revAcc.reverse revAccVals nextVarId
              (fun sv hsv => hrevAccFresh sv (List.mem_reverse.mp hsv)) ha1_below haccMatch
          have hvrest1 : List.Forall₂ (fun p v => simpleValMatches a1 p.2 v) rest vsRest :=
            forall2_pairs_simpleValMatches_extend_preserves a a1 Prod.snd rest vsRest nextVarId
              (fun q hq => hpfresh q (List.mem_cons_of_mem _ hq)) ha1_below hvrest
          have hnvMono : nextVarId ≤ (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.1 :=
            mergeSimpleSymVal_mono nextVarId tbExtra ebExtra p.1 p.2
          have hmergedFresh :
              varSetBelow (simpleValVars (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).1)
                (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.1 :=
            mergeSimpleSymVal_result_fresh nextVarId tbExtra ebExtra p.1 p.2 hp1fresh'
          have hebEFresh : varSetBelow
              (ffVarsOfFormula (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.2 ∪
               bVarsOfFormula (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.2)
              (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.1 :=
            mergeSimpleSymVal_ebExtra_fresh nextVarId tbExtra ebExtra p.1 p.2 hfresh hp1fresh
          have hrest_fresh' : ∀ q ∈ rest,
              varSetBelow (simpleValVars q.2) (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.1 :=
            fun q hq => varSetBelow_mono hnvMono (hpfresh q (List.mem_cons_of_mem _ hq))
          have hrest_fresh1' : ∀ q ∈ rest,
              varSetBelow (simpleValVars q.1) (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.1 :=
            fun q hq => varSetBelow_mono hnvMono (hpfresh1 q (List.mem_cons_of_mem _ hq))
          have hnewAccFresh : ∀ sv ∈ (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).1 :: revAcc,
              varSetBelow (simpleValVars sv) (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.1 := by
            intro sv hsv
            rcases List.mem_cons.mp hsv with heq | hmem
            · rw [heq]; exact hmergedFresh
            · exact varSetBelow_mono hnvMono (hrevAccFresh sv hmem)
          have hnewAccMatch : List.Forall₂ (simpleValMatches a1)
              ((mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).1 :: revAcc).reverse
              (revAccVals ++ [v0]) := by
            rw [List.reverse_cons]
            exact forall2_append haccMatch1 (List.Forall₂.cons ha1_match List.Forall₂.nil)
          obtain ⟨a', nv, tbE, ebE, mergedRev, hfold, hnvMono2, ha'_range, ha'_bool, ha'_frame,
              ha'_match, ha'_extra⟩ :=
            ih (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.1
              (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.1
              (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.2
              ((mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).1 :: revAcc) (revAccVals ++ [v0])
              hebEFresh hnewAccFresh hrest_fresh1' hrest_fresh' a1 hnewAccMatch ha1_extra vsRest
              hvrest1
          refine ⟨a', nv, tbE, ebE, mergedRev, ?_, le_trans hnvMono hnvMono2, ?_,
            fun n => (ha'_bool n).trans (ha1_bool n), ?_, ?_, ha'_extra⟩
          · simpa only [List.foldl_cons] using hfold
          · intro n hn
            rw [ha'_range n (lt_of_lt_of_le hn hnvMono), ha1_below n hn]
          · intro n hn
            have hsubset := mergeSimpleSymValFoldl_ebExtra_subset rest
              (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.1
              (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.1
              (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.2
              ((mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).1 :: revAcc)
            simp only [hfold] at hsubset
            rw [ha'_frame n hn]
            exact ha1_frame n (fun h => hn (hsubset (Var.ffv n) h))
          · simpa only [List.append_assoc, List.singleton_append] using ha'_match

/-- **Completeness** half of `mergeSimpleSymValFoldl`, `tb` side: given a fixed assignment that
    already matches every pair's tb-side value and the pre-existing accumulator, and that
    satisfies the *final* accumulated `tbExtra` (the only fact available from the outside --
    intermediate steps' own formulas aren't known to hold on their own), the whole merged list
    matches too. `mergeSimpleSymValFoldl_tbExtra_eval_mono` recovers each step's own formula
    from the final one; `mergeSimpleSymVal_match_of_tb` then transfers the match at that step. -/
theorem mergeSimpleSymValFoldl_match_of_tb {c : ZKConfig} (gconf : GlobalConfig c)
    (ms : List (FFMacro c)) (assignment' : Assignment c) :
    ∀ (pairs : List (SimpleSymVal c × SimpleSymVal c))
      (nextVarId : Nat) (tbExtra ebExtra : FFFormula c)
      (revAcc : List (SimpleSymVal c)) (revAccVals : List (FF c))
      (haccMatch : List.Forall₂ (simpleValMatches assignment') revAcc.reverse revAccVals)
      (vsTb : List (FF c))
      (hpMatch : List.Forall₂ (fun p v => simpleValMatches assignment' p.1 v) pairs vsTb)
      (nv : Nat) (tbE ebE : FFFormula c) (mergedRev : List (SimpleSymVal c))
      (hfold : pairs.foldl (fun acc p =>
          let (nvi, tbExtrai, ebExtrai, merged) := acc
          let (mergedVal, nv2, tbE2, ebE2) := mergeSimpleSymVal nvi tbExtrai ebExtrai p.1 p.2
          (nv2, tbE2, ebE2, mergedVal :: merged)) (nextVarId, tbExtra, ebExtra, revAcc)
          = (nv, tbE, ebE, mergedRev))
      (htbE : evalFormula gconf assignment' tbE ms = Except.ok true),
      List.Forall₂ (simpleValMatches assignment') mergedRev.reverse (revAccVals ++ vsTb) := by
  intro pairs
  induction pairs with
  | nil =>
      intro nextVarId tbExtra ebExtra revAcc revAccVals haccMatch vsTb hpMatch nv tbE ebE mergedRev
        hfold _htbE
      cases hpMatch
      simp only [List.foldl_nil, Prod.mk.injEq] at hfold
      obtain ⟨_, _, _, hmerged⟩ := hfold
      rw [← hmerged]
      simpa using haccMatch
  | cons p rest ih =>
      intro nextVarId tbExtra ebExtra revAcc revAccVals haccMatch vsTb hpMatch nv tbE ebE mergedRev
        hfold htbE
      cases hpMatch with
      | cons hv0 hvrest =>
          rename_i v0 vsRest
          simp only [List.foldl_cons] at hfold
          have hstep_true : evalFormula gconf assignment'
              (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.1 ms = Except.ok true :=
            mergeSimpleSymValFoldl_tbExtra_eval_mono gconf ms assignment' rest
              (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.1
              (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.1
              (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.2
              ((mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).1 :: revAcc)
              (by rw [hfold]; exact htbE)
          have hmerged_v0 : simpleValMatches assignment'
              (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).1 v0 :=
            mergeSimpleSymVal_match_of_tb gconf ms assignment' nextVarId tbExtra ebExtra p.1 p.2 v0
              hv0 hstep_true
          have haccMatch1 : List.Forall₂ (simpleValMatches assignment')
              ((mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).1 :: revAcc).reverse
              (revAccVals ++ [v0]) := by
            rw [List.reverse_cons]
            exact forall2_append haccMatch (List.Forall₂.cons hmerged_v0 List.Forall₂.nil)
          have hrec := ih (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.1
            (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.1
            (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.2
            ((mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).1 :: revAcc)
            (revAccVals ++ [v0]) haccMatch1 vsRest hvrest nv tbE ebE mergedRev hfold htbE
          simpa only [List.append_assoc, List.singleton_append] using hrec

/-- Mirror of `mergeSimpleSymValFoldl_match_of_tb`, for the `eb` side. -/
theorem mergeSimpleSymValFoldl_match_of_eb {c : ZKConfig} (gconf : GlobalConfig c)
    (ms : List (FFMacro c)) (assignment' : Assignment c) :
    ∀ (pairs : List (SimpleSymVal c × SimpleSymVal c))
      (nextVarId : Nat) (tbExtra ebExtra : FFFormula c)
      (revAcc : List (SimpleSymVal c)) (revAccVals : List (FF c))
      (haccMatch : List.Forall₂ (simpleValMatches assignment') revAcc.reverse revAccVals)
      (vsEb : List (FF c))
      (hpMatch : List.Forall₂ (fun p v => simpleValMatches assignment' p.2 v) pairs vsEb)
      (nv : Nat) (tbE ebE : FFFormula c) (mergedRev : List (SimpleSymVal c))
      (hfold : pairs.foldl (fun acc p =>
          let (nvi, tbExtrai, ebExtrai, merged) := acc
          let (mergedVal, nv2, tbE2, ebE2) := mergeSimpleSymVal nvi tbExtrai ebExtrai p.1 p.2
          (nv2, tbE2, ebE2, mergedVal :: merged)) (nextVarId, tbExtra, ebExtra, revAcc)
          = (nv, tbE, ebE, mergedRev))
      (hebE : evalFormula gconf assignment' ebE ms = Except.ok true),
      List.Forall₂ (simpleValMatches assignment') mergedRev.reverse (revAccVals ++ vsEb) := by
  intro pairs
  induction pairs with
  | nil =>
      intro nextVarId tbExtra ebExtra revAcc revAccVals haccMatch vsEb hpMatch nv tbE ebE mergedRev
        hfold _hebE
      cases hpMatch
      simp only [List.foldl_nil, Prod.mk.injEq] at hfold
      obtain ⟨_, _, _, hmerged⟩ := hfold
      rw [← hmerged]
      simpa using haccMatch
  | cons p rest ih =>
      intro nextVarId tbExtra ebExtra revAcc revAccVals haccMatch vsEb hpMatch nv tbE ebE mergedRev
        hfold hebE
      cases hpMatch with
      | cons hv0 hvrest =>
          rename_i v0 vsRest
          simp only [List.foldl_cons] at hfold
          have hstep_true : evalFormula gconf assignment'
              (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.2 ms = Except.ok true :=
            mergeSimpleSymValFoldl_ebExtra_eval_mono gconf ms assignment' rest
              (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.1
              (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.1
              (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.2
              ((mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).1 :: revAcc)
              (by rw [hfold]; exact hebE)
          have hmerged_v0 : simpleValMatches assignment'
              (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).1 v0 :=
            mergeSimpleSymVal_match_of_eb gconf ms assignment' nextVarId tbExtra ebExtra p.1 p.2 v0
              hv0 hstep_true
          have haccMatch1 : List.Forall₂ (simpleValMatches assignment')
              ((mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).1 :: revAcc).reverse
              (revAccVals ++ [v0]) := by
            rw [List.reverse_cons]
            exact forall2_append haccMatch (List.Forall₂.cons hmerged_v0 List.Forall₂.nil)
          have hrec := ih (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.1
            (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.1
            (mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).2.2.2
            ((mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2).1 :: revAcc)
            (revAccVals ++ [v0]) haccMatch1 vsRest hvrest nv tbE ebE mergedRev hfold hebE
          simpa only [List.append_assoc, List.singleton_append] using hrec

/-- Re-indexes a `List.Forall₂` relating `l1` to `l2` into one over `l1`'s zip with any
    other same-length list `l3`, reading off the first component of each pair (`l3`'s
    elements are just carried along positionally, never examined). -/
theorem forall2_zip_fst_of_length_eq {α β γ : Type} {R : α → β → Prop} {l1 : List α}
    {l2 : List β} {l3 : List γ} (h : List.Forall₂ R l1 l2) (hlen : l1.length = l3.length) :
    List.Forall₂ (fun p v => R p.1 v) (l1.zip l3) l2 := by
  induction h generalizing l3 with
  | nil =>
      cases l3 with
      | nil => exact List.Forall₂.nil
      | cons _ _ => simp at hlen
  | cons hd _tl ih =>
      cases l3 with
      | nil => simp at hlen
      | cons z zs =>
          simp only [List.zip_cons_cons]
          exact List.Forall₂.cons hd (ih (by simpa using hlen))

/-- Soundness of `mergeSymValue`'s `tb` side: if it succeeds, and the assignment already
    matches `svTb`'s value and satisfies `tbExtra`, it extends -- without disturbing anything
    below `nextVarId` -- to one matching the merged value and satisfying the updated
    `tbExtra'`. Combines `mergeSimpleSymVal_extend_tb` (scalars) with
    `mergeSimpleSymValFoldl_extend_tb` (arrays, position-by-position). -/
theorem mergeSymValue_extend_tb {c : ZKConfig}
    (gconf : GlobalConfig c) (ms : List (FFMacro c))
    (nextVarId : Nat) (tbExtra ebExtra : FFFormula c) (svTb svEb : SymValue c)
    (merged : SymValue c) (nv' : Nat) (tbExtra' ebExtra' : FFFormula c)
    (heq : mergeSymValue nextVarId tbExtra ebExtra svTb svEb
      = Except.ok (merged, nv', tbExtra', ebExtra'))
    (hfresh : varSetBelow (ffVarsOfFormula tbExtra ∪ bVarsOfFormula tbExtra) nextVarId)
    (hsvTbFresh : varSetBelow (symValVars svTb) nextVarId)
    (a : Assignment c) (vTb : Value c) (hmTb : symValMatches a svTb vTb)
    (htbExtra : evalFormula gconf a tbExtra ms = Except.ok true) :
    ∃ a', (∀ n, n < nextVarId → a'.ff n = a.ff n) ∧ (∀ n, a'.bool n = a.bool n) ∧
      (∀ n, Var.ffv n ∉ (ffVarsOfFormula tbExtra' ∪ bVarsOfFormula tbExtra') → a'.ff n = a.ff n) ∧
      symValMatches a' merged vTb ∧ evalFormula gconf a' tbExtra' ms = Except.ok true := by
  cases svTb with
  | simple s1 =>
      cases svEb with
      | array _ => exact absurd heq (by simp [mergeSymValue])
      | simple s2 =>
          cases vTb with
          | array _ => simp only [symValMatches] at hmTb
          | scalar v1 =>
              simp only [symValMatches] at hmTb
              simp only [mergeSymValue, Except.ok.injEq, Prod.mk.injEq] at heq
              obtain ⟨a', ha'_range, ha'_bool, ha'_frame, ha'_match, ha'_extra⟩ :=
                mergeSimpleSymVal_extend_tb gconf ms nextVarId tbExtra ebExtra s1 s2
                  hfresh hsvTbFresh a v1 hmTb htbExtra
              refine ⟨a', fun n hn => ha'_range n (Nat.ne_of_lt hn), ha'_bool, ?_, ?_, ?_⟩
              · rw [← heq.2.2.1]; exact ha'_frame
              · rw [← heq.1, symValMatches]; exact ha'_match
              · rw [← heq.2.2.1]; exact ha'_extra
  | array arrTb =>
      cases svEb with
      | simple _ => exact absurd heq (by simp [mergeSymValue])
      | array arrEb =>
          simp only [mergeSymValue] at heq
          split at heq
          · rename_i hsize
            cases vTb with
            | scalar _ => simp only [symValMatches] at hmTb
            | array varr =>
                simp only [symValMatches] at hmTb
                have hlen : arrTb.toList.length = arrEb.toList.length := by
                  simp only [Array.length_toList]; exact hsize
                obtain ⟨a', nv, tbE, ebE, mergedRev, hfold, _hnvMono, ha'_range, ha'_bool,
                    ha'_frame, ha'_match, ha'_extra⟩ :=
                  mergeSimpleSymValFoldl_extend_tb gconf ms (arrTb.toList.zip arrEb.toList)
                    nextVarId tbExtra ebExtra [] [] hfresh (by simp)
                    (fun p hp => symValVars_array_mem_below arrTb p.1
                      (List.of_mem_zip hp).1 nextVarId hsvTbFresh)
                    a (by simp) htbExtra varr.toList (forall2_zip_fst_of_length_eq hmTb hlen)
                simp only [hfold, Except.ok.injEq, Prod.mk.injEq] at heq
                refine ⟨a', ha'_range, ha'_bool, ?_, ?_, ?_⟩
                · rw [← heq.2.2.1]; exact ha'_frame
                · rw [← heq.1]
                  simpa only [symValMatches, List.toList_toArray, List.nil_append] using ha'_match
                · rw [← heq.2.2.1]; exact ha'_extra
          · exact absurd heq (by simp)

/-- Mirror of `forall2_zip_fst_of_length_eq`, reading off the *second* component instead. -/
theorem forall2_zip_snd_of_length_eq {α β γ : Type} {R : β → γ → Prop} {l1 : List α}
    {l2 : List β} {l3 : List γ} (h : List.Forall₂ R l2 l3) (hlen : l1.length = l2.length) :
    List.Forall₂ (fun p v => R p.2 v) (l1.zip l2) l3 := by
  induction h generalizing l1 with
  | nil =>
      cases l1 with
      | nil => exact List.Forall₂.nil
      | cons _ _ => simp at hlen
  | cons hd _tl ih =>
      cases l1 with
      | nil => simp at hlen
      | cons z zs =>
          simp only [List.zip_cons_cons]
          exact List.Forall₂.cons hd (ih (by simpa using hlen))

/-- Mirror of `mergeSymValue_extend_tb`, for the `eb` side. -/
theorem mergeSymValue_extend_eb {c : ZKConfig}
    (gconf : GlobalConfig c) (ms : List (FFMacro c))
    (nextVarId : Nat) (tbExtra ebExtra : FFFormula c) (svTb svEb : SymValue c)
    (merged : SymValue c) (nv' : Nat) (tbExtra' ebExtra' : FFFormula c)
    (heq : mergeSymValue nextVarId tbExtra ebExtra svTb svEb
      = Except.ok (merged, nv', tbExtra', ebExtra'))
    (hfresh : varSetBelow (ffVarsOfFormula ebExtra ∪ bVarsOfFormula ebExtra) nextVarId)
    (hsvTbFresh : varSetBelow (symValVars svTb) nextVarId)
    (hsvEbFresh : varSetBelow (symValVars svEb) nextVarId)
    (a : Assignment c) (vEb : Value c) (hmEb : symValMatches a svEb vEb)
    (hebExtra : evalFormula gconf a ebExtra ms = Except.ok true) :
    ∃ a', (∀ n, n < nextVarId → a'.ff n = a.ff n) ∧ (∀ n, a'.bool n = a.bool n) ∧
      (∀ n, Var.ffv n ∉ (ffVarsOfFormula ebExtra' ∪ bVarsOfFormula ebExtra') → a'.ff n = a.ff n) ∧
      symValMatches a' merged vEb ∧ evalFormula gconf a' ebExtra' ms = Except.ok true := by
  cases svTb with
  | simple s1 =>
      cases svEb with
      | array _ => exact absurd heq (by simp [mergeSymValue])
      | simple s2 =>
          cases vEb with
          | array _ => simp only [symValMatches] at hmEb
          | scalar v2 =>
              simp only [symValMatches] at hmEb
              simp only [mergeSymValue, Except.ok.injEq, Prod.mk.injEq] at heq
              obtain ⟨a', ha'_range, ha'_bool, ha'_frame, ha'_match, ha'_extra⟩ :=
                mergeSimpleSymVal_extend_eb gconf ms nextVarId tbExtra ebExtra s1 s2
                  hfresh hsvEbFresh a v2 hmEb hebExtra
              refine ⟨a', fun n hn => ha'_range n (Nat.ne_of_lt hn), ha'_bool, ?_, ?_, ?_⟩
              · rw [← heq.2.2.2]; exact ha'_frame
              · rw [← heq.1, symValMatches]; exact ha'_match
              · rw [← heq.2.2.2]; exact ha'_extra
  | array arrTb =>
      cases svEb with
      | simple _ => exact absurd heq (by simp [mergeSymValue])
      | array arrEb =>
          simp only [mergeSymValue] at heq
          split at heq
          · rename_i hsize
            cases vEb with
            | scalar _ => simp only [symValMatches] at hmEb
            | array varr =>
                simp only [symValMatches] at hmEb
                have hlen : arrTb.toList.length = arrEb.toList.length := by
                  simp only [Array.length_toList]; exact hsize
                obtain ⟨a', nv, tbE, ebE, mergedRev, hfold, _hnvMono, ha'_range, ha'_bool,
                    ha'_frame, ha'_match, ha'_extra⟩ :=
                  mergeSimpleSymValFoldl_extend_eb gconf ms (arrTb.toList.zip arrEb.toList)
                    nextVarId tbExtra ebExtra [] [] hfresh (by simp)
                    (fun p hp => symValVars_array_mem_below arrTb p.1
                      (List.of_mem_zip hp).1 nextVarId hsvTbFresh)
                    (fun p hp => symValVars_array_mem_below arrEb p.2
                      (List.of_mem_zip hp).2 nextVarId hsvEbFresh)
                    a (by simp) hebExtra varr.toList (forall2_zip_snd_of_length_eq hmEb hlen)
                simp only [hfold, Except.ok.injEq, Prod.mk.injEq] at heq
                refine ⟨a', ha'_range, ha'_bool, ?_, ?_, ?_⟩
                · rw [← heq.2.2.2]; exact ha'_frame
                · rw [← heq.1]
                  simpa only [symValMatches, List.toList_toArray, List.nil_append] using ha'_match
                · rw [← heq.2.2.2]; exact ha'_extra
          · exact absurd heq (by simp)

/-- **Completeness** half of `mergeSymValue`, `tb` side: mirrors `mergeSymValue_extend_tb`, but
    for a fixed assignment (no construction needed) -- delegates to
    `mergeSimpleSymVal_match_of_tb`/`mergeSimpleSymValFoldl_match_of_tb` depending on shape. -/
theorem mergeSymValue_match_of_tb {c : ZKConfig} (gconf : GlobalConfig c) (ms : List (FFMacro c))
    (assignment' : Assignment c)
    (nextVarId : Nat) (tbExtra ebExtra : FFFormula c) (svTb svEb : SymValue c)
    (merged : SymValue c) (nv' : Nat) (tbExtra' ebExtra' : FFFormula c)
    (heq : mergeSymValue nextVarId tbExtra ebExtra svTb svEb
      = Except.ok (merged, nv', tbExtra', ebExtra'))
    (v : Value c) (hmTb : symValMatches assignment' svTb v)
    (htbExtra' : evalFormula gconf assignment' tbExtra' ms = Except.ok true) :
    symValMatches assignment' merged v := by
  cases svTb with
  | simple s1 =>
      cases svEb with
      | array _ => exact absurd heq (by simp [mergeSymValue])
      | simple s2 =>
          cases v with
          | array _ => simp only [symValMatches] at hmTb
          | scalar v1 =>
              simp only [symValMatches] at hmTb
              simp only [mergeSymValue, Except.ok.injEq, Prod.mk.injEq] at heq
              rw [← heq.1, symValMatches]
              exact mergeSimpleSymVal_match_of_tb gconf ms assignment' nextVarId tbExtra ebExtra
                s1 s2 v1 hmTb (heq.2.2.1 ▸ htbExtra')
  | array arrTb =>
      cases svEb with
      | simple _ => exact absurd heq (by simp [mergeSymValue])
      | array arrEb =>
          simp only [mergeSymValue] at heq
          split at heq
          · rename_i hsize
            cases v with
            | scalar _ => simp only [symValMatches] at hmTb
            | array varr =>
                simp only [symValMatches] at hmTb
                have hlen : arrTb.toList.length = arrEb.toList.length := by
                  simp only [Array.length_toList]; exact hsize
                cases hfold : (arrTb.toList.zip arrEb.toList).foldl (fun acc p =>
                    let (nvi, tbExtrai, ebExtrai, merged) := acc
                    let (mergedVal, nv2, tbE2, ebE2) := mergeSimpleSymVal nvi tbExtrai ebExtrai
                      p.1 p.2
                    (nv2, tbE2, ebE2, mergedVal :: merged)) (nextVarId, tbExtra, ebExtra, [])
                  with
                | mk nv result =>
                  obtain ⟨tbE, ebE, mergedRev⟩ := result
                  rw [hfold] at heq
                  simp only [Except.ok.injEq, Prod.mk.injEq] at heq
                  have hrec := mergeSimpleSymValFoldl_match_of_tb gconf ms assignment'
                    (arrTb.toList.zip arrEb.toList) nextVarId tbExtra ebExtra [] [] (by simp)
                    varr.toList (forall2_zip_fst_of_length_eq hmTb hlen)
                    nv tbE ebE mergedRev hfold (heq.2.2.1 ▸ htbExtra')
                  rw [← heq.1, symValMatches]
                  simpa only [List.toList_toArray, List.nil_append] using hrec
          · exact absurd heq (by simp)

/-- Mirror of `mergeSymValue_match_of_tb`, for the `eb` side. -/
theorem mergeSymValue_match_of_eb {c : ZKConfig} (gconf : GlobalConfig c) (ms : List (FFMacro c))
    (assignment' : Assignment c)
    (nextVarId : Nat) (tbExtra ebExtra : FFFormula c) (svTb svEb : SymValue c)
    (merged : SymValue c) (nv' : Nat) (tbExtra' ebExtra' : FFFormula c)
    (heq : mergeSymValue nextVarId tbExtra ebExtra svTb svEb
      = Except.ok (merged, nv', tbExtra', ebExtra'))
    (v : Value c) (hmEb : symValMatches assignment' svEb v)
    (hebExtra' : evalFormula gconf assignment' ebExtra' ms = Except.ok true) :
    symValMatches assignment' merged v := by
  cases svTb with
  | simple s1 =>
      cases svEb with
      | array _ => exact absurd heq (by simp [mergeSymValue])
      | simple s2 =>
          cases v with
          | array _ => simp only [symValMatches] at hmEb
          | scalar v2 =>
              simp only [symValMatches] at hmEb
              simp only [mergeSymValue, Except.ok.injEq, Prod.mk.injEq] at heq
              rw [← heq.1, symValMatches]
              exact mergeSimpleSymVal_match_of_eb gconf ms assignment' nextVarId tbExtra ebExtra
                s1 s2 v2 hmEb (heq.2.2.2 ▸ hebExtra')
  | array arrTb =>
      cases svEb with
      | simple _ => exact absurd heq (by simp [mergeSymValue])
      | array arrEb =>
          simp only [mergeSymValue] at heq
          split at heq
          · rename_i hsize
            cases v with
            | scalar _ => simp only [symValMatches] at hmEb
            | array varr =>
                simp only [symValMatches] at hmEb
                have hlen : arrTb.toList.length = arrEb.toList.length := by
                  simp only [Array.length_toList]; exact hsize
                cases hfold : (arrTb.toList.zip arrEb.toList).foldl (fun acc p =>
                    let (nvi, tbExtrai, ebExtrai, merged) := acc
                    let (mergedVal, nv2, tbE2, ebE2) := mergeSimpleSymVal nvi tbExtrai ebExtrai
                      p.1 p.2
                    (nv2, tbE2, ebE2, mergedVal :: merged)) (nextVarId, tbExtra, ebExtra, [])
                  with
                | mk nv result =>
                  obtain ⟨tbE, ebE, mergedRev⟩ := result
                  rw [hfold] at heq
                  simp only [Except.ok.injEq, Prod.mk.injEq] at heq
                  have hrec := mergeSimpleSymValFoldl_match_of_eb gconf ms assignment'
                    (arrTb.toList.zip arrEb.toList) nextVarId tbExtra ebExtra [] [] (by simp)
                    varr.toList (forall2_zip_snd_of_length_eq hmEb hlen)
                    nv tbE ebE mergedRev hfold (heq.2.2.2 ▸ hebExtra')
                  rw [← heq.1, symValMatches]
                  simpa only [List.toList_toArray, List.nil_append] using hrec
          · exact absurd heq (by simp)

/-- `mergeSymValue` never lowers the variable counter. -/
theorem mergeSymValue_mono {c : ZKConfig}
    (nextVarId : Nat) (tbExtra ebExtra : FFFormula c) (svTb svEb : SymValue c)
    (merged : SymValue c) (nv' : Nat) (tbExtra' ebExtra' : FFFormula c)
    (heq : mergeSymValue nextVarId tbExtra ebExtra svTb svEb
      = Except.ok (merged, nv', tbExtra', ebExtra')) :
    nextVarId ≤ nv' := by
  cases svTb with
  | simple s1 =>
      cases svEb with
      | simple s2 =>
          simp only [mergeSymValue, Except.ok.injEq, Prod.mk.injEq] at heq
          rw [← heq.2.1]
          exact mergeSimpleSymVal_mono nextVarId tbExtra ebExtra s1 s2
      | array _ => exact absurd heq (by simp [mergeSymValue])
  | array arrTb =>
      cases svEb with
      | simple _ => exact absurd heq (by simp [mergeSymValue])
      | array arrEb =>
          simp only [mergeSymValue] at heq
          split at heq
          · simp only [Except.ok.injEq, Prod.mk.injEq] at heq
            rw [← heq.2.1]
            exact mergeSimpleSymValFoldl_mono (arrTb.toList.zip arrEb.toList) nextVarId
              tbExtra ebExtra []
          · exact absurd heq (by simp)

/-- The `tbExtra'` that `mergeSymValue` produces is fresh below the new counter. -/
theorem mergeSymValue_tbExtra_fresh {c : ZKConfig}
    (nextVarId : Nat) (tbExtra ebExtra : FFFormula c) (svTb svEb : SymValue c)
    (merged : SymValue c) (nv' : Nat) (tbExtra' ebExtra' : FFFormula c)
    (heq : mergeSymValue nextVarId tbExtra ebExtra svTb svEb
      = Except.ok (merged, nv', tbExtra', ebExtra'))
    (hfresh : varSetBelow (ffVarsOfFormula tbExtra ∪ bVarsOfFormula tbExtra) nextVarId)
    (hsvTbFresh : varSetBelow (symValVars svTb) nextVarId) :
    varSetBelow (ffVarsOfFormula tbExtra' ∪ bVarsOfFormula tbExtra') nv' := by
  cases svTb with
  | simple s1 =>
      cases svEb with
      | simple s2 =>
          simp only [mergeSymValue, Except.ok.injEq, Prod.mk.injEq] at heq
          rw [← heq.2.1, ← heq.2.2.1]
          exact mergeSimpleSymVal_tbExtra_fresh nextVarId tbExtra ebExtra s1 s2 hfresh hsvTbFresh
      | array _ => exact absurd heq (by simp [mergeSymValue])
  | array arrTb =>
      cases svEb with
      | simple _ => exact absurd heq (by simp [mergeSymValue])
      | array arrEb =>
          simp only [mergeSymValue] at heq
          split at heq
          · simp only [Except.ok.injEq, Prod.mk.injEq] at heq
            rw [← heq.2.1, ← heq.2.2.1]
            exact mergeSimpleSymValFoldl_tbExtra_fresh (arrTb.toList.zip arrEb.toList) nextVarId
              tbExtra ebExtra [] hfresh
              (fun p hp => symValVars_array_mem_below arrTb p.1 (List.of_mem_zip hp).1
                nextVarId hsvTbFresh)
          · exact absurd heq (by simp)

/-- Mirror of `mergeSymValue_tbExtra_fresh`, for `ebExtra`. -/
theorem mergeSymValue_ebExtra_fresh {c : ZKConfig}
    (nextVarId : Nat) (tbExtra ebExtra : FFFormula c) (svTb svEb : SymValue c)
    (merged : SymValue c) (nv' : Nat) (tbExtra' ebExtra' : FFFormula c)
    (heq : mergeSymValue nextVarId tbExtra ebExtra svTb svEb
      = Except.ok (merged, nv', tbExtra', ebExtra'))
    (hfresh : varSetBelow (ffVarsOfFormula ebExtra ∪ bVarsOfFormula ebExtra) nextVarId)
    (hsvEbFresh : varSetBelow (symValVars svEb) nextVarId) :
    varSetBelow (ffVarsOfFormula ebExtra' ∪ bVarsOfFormula ebExtra') nv' := by
  cases svTb with
  | simple s1 =>
      cases svEb with
      | simple s2 =>
          simp only [mergeSymValue, Except.ok.injEq, Prod.mk.injEq] at heq
          rw [← heq.2.1, ← heq.2.2.2]
          exact mergeSimpleSymVal_ebExtra_fresh nextVarId tbExtra ebExtra s1 s2 hfresh hsvEbFresh
      | array _ => exact absurd heq (by simp [mergeSymValue])
  | array arrTb =>
      cases svEb with
      | simple _ => exact absurd heq (by simp [mergeSymValue])
      | array arrEb =>
          simp only [mergeSymValue] at heq
          split at heq
          · simp only [Except.ok.injEq, Prod.mk.injEq] at heq
            rw [← heq.2.1, ← heq.2.2.2]
            exact mergeSimpleSymValFoldl_ebExtra_fresh (arrTb.toList.zip arrEb.toList) nextVarId
              tbExtra ebExtra [] hfresh
              (fun p hp => symValVars_array_mem_below arrEb p.2 (List.of_mem_zip hp).2
                nextVarId hsvEbFresh)
          · exact absurd heq (by simp)

/-- Subset-or-fresh analog of `mergeSymValue_tbExtra_fresh`. Takes a `startVarId` separate from
    `nextVarId` (the merge's own starting counter) so it composes across multiple accumulating
    merge steps: `tbExtra`'s own footprint is only known relative to some earlier `startVarId`,
    not necessarily to this step's own `nextVarId`. -/
theorem mergeSymValue_tbExtra_merged_subset {c : ZKConfig} (target : VarSet) (startVarId : Nat)
    (nextVarId : Nat) (tbExtra ebExtra : FFFormula c) (svTb svEb : SymValue c)
    (merged : SymValue c) (nv' : Nat) (tbExtra' ebExtra' : FFFormula c)
    (heq : mergeSymValue nextVarId tbExtra ebExtra svTb svEb
      = Except.ok (merged, nv', tbExtra', ebExtra'))
    (hstart : startVarId ≤ nextVarId)
    (htbExtraSubset : ∀ v ∈ (ffVarsOfFormula tbExtra ∪ bVarsOfFormula tbExtra),
      v ∈ target ∨ startVarId ≤ varIndex v)
    (hsvTbSubset : symValVars svTb ⊆ target) :
    ∀ v ∈ (ffVarsOfFormula tbExtra' ∪ bVarsOfFormula tbExtra'),
      v ∈ target ∨ startVarId ≤ varIndex v := by
  cases svTb with
  | simple s1 =>
      cases svEb with
      | simple s2 =>
          simp only [mergeSymValue, Except.ok.injEq, Prod.mk.injEq] at heq
          rw [← heq.2.2.1]
          intro v hv
          rcases mergeSimpleSymVal_tbExtra_merged_subset nextVarId tbExtra ebExtra s1 s2 v hv with
            h | h | h
          · exact htbExtraSubset v h
          · exact Or.inl (hsvTbSubset v h)
          · exact Or.inr (hstart.trans h)
      | array _ => exact absurd heq (by simp [mergeSymValue])
  | array arrTb =>
      cases svEb with
      | simple _ => exact absurd heq (by simp [mergeSymValue])
      | array arrEb =>
          simp only [mergeSymValue] at heq
          split at heq
          · simp only [Except.ok.injEq, Prod.mk.injEq] at heq
            rw [← heq.2.2.1]
            exact mergeSimpleSymValFoldl_tbExtra_merged_subset target startVarId
              (arrTb.toList.zip arrEb.toList) nextVarId tbExtra ebExtra [] hstart
              htbExtraSubset
              (fun p hp => symValVars_array_mem_below_subset arrTb p.1 (List.of_mem_zip hp).1
                target hsvTbSubset)
          · exact absurd heq (by simp)

/-- Mirror of `mergeSymValue_tbExtra_merged_subset`, for `ebExtra`. -/
theorem mergeSymValue_ebExtra_merged_subset {c : ZKConfig} (target : VarSet) (startVarId : Nat)
    (nextVarId : Nat) (tbExtra ebExtra : FFFormula c) (svTb svEb : SymValue c)
    (merged : SymValue c) (nv' : Nat) (tbExtra' ebExtra' : FFFormula c)
    (heq : mergeSymValue nextVarId tbExtra ebExtra svTb svEb
      = Except.ok (merged, nv', tbExtra', ebExtra'))
    (hstart : startVarId ≤ nextVarId)
    (hebExtraSubset : ∀ v ∈ (ffVarsOfFormula ebExtra ∪ bVarsOfFormula ebExtra),
      v ∈ target ∨ startVarId ≤ varIndex v)
    (hsvEbSubset : symValVars svEb ⊆ target) :
    ∀ v ∈ (ffVarsOfFormula ebExtra' ∪ bVarsOfFormula ebExtra'),
      v ∈ target ∨ startVarId ≤ varIndex v := by
  cases svTb with
  | simple s1 =>
      cases svEb with
      | simple s2 =>
          simp only [mergeSymValue, Except.ok.injEq, Prod.mk.injEq] at heq
          rw [← heq.2.2.2]
          intro v hv
          rcases mergeSimpleSymVal_ebExtra_merged_subset nextVarId tbExtra ebExtra s1 s2 v hv with
            h | h | h
          · exact hebExtraSubset v h
          · exact Or.inl (hsvEbSubset v h)
          · exact Or.inr (hstart.trans h)
      | array _ => exact absurd heq (by simp [mergeSymValue])
  | array arrTb =>
      cases svEb with
      | simple _ => exact absurd heq (by simp [mergeSymValue])
      | array arrEb =>
          simp only [mergeSymValue] at heq
          split at heq
          · simp only [Except.ok.injEq, Prod.mk.injEq] at heq
            rw [← heq.2.2.2]
            exact mergeSimpleSymValFoldl_ebExtra_merged_subset target startVarId
              (arrTb.toList.zip arrEb.toList) nextVarId tbExtra ebExtra [] hstart
              hebExtraSubset
              (fun p hp => symValVars_array_mem_below_subset arrEb p.2 (List.of_mem_zip hp).2
                target hsvEbSubset)
          · exact absurd heq (by simp)

/-- `mergeSymValue` only ever grows `tbExtra`'s footprint. -/
theorem mergeSymValue_tbExtra_subset {c : ZKConfig}
    (nextVarId : Nat) (tbExtra ebExtra : FFFormula c) (svTb svEb : SymValue c)
    (merged : SymValue c) (nv' : Nat) (tbExtra' ebExtra' : FFFormula c)
    (heq : mergeSymValue nextVarId tbExtra ebExtra svTb svEb
      = Except.ok (merged, nv', tbExtra', ebExtra')) :
    (ffVarsOfFormula tbExtra ∪ bVarsOfFormula tbExtra) ⊆
      (ffVarsOfFormula tbExtra' ∪ bVarsOfFormula tbExtra') := by
  cases svTb with
  | simple s1 =>
      cases svEb with
      | simple s2 =>
          simp only [mergeSymValue, Except.ok.injEq, Prod.mk.injEq] at heq
          rw [← heq.2.2.1]
          exact mergeSimpleSymVal_tbExtra_subset nextVarId tbExtra ebExtra s1 s2
      | array _ => exact absurd heq (by simp [mergeSymValue])
  | array arrTb =>
      cases svEb with
      | simple _ => exact absurd heq (by simp [mergeSymValue])
      | array arrEb =>
          simp only [mergeSymValue] at heq
          split at heq
          · simp only [Except.ok.injEq, Prod.mk.injEq] at heq
            rw [← heq.2.2.1]
            exact mergeSimpleSymValFoldl_tbExtra_subset (arrTb.toList.zip arrEb.toList) nextVarId
              tbExtra ebExtra []
          · exact absurd heq (by simp)

/-- Mirror of `mergeSymValue_tbExtra_subset`, for `ebExtra`. -/
theorem mergeSymValue_ebExtra_subset {c : ZKConfig}
    (nextVarId : Nat) (tbExtra ebExtra : FFFormula c) (svTb svEb : SymValue c)
    (merged : SymValue c) (nv' : Nat) (tbExtra' ebExtra' : FFFormula c)
    (heq : mergeSymValue nextVarId tbExtra ebExtra svTb svEb
      = Except.ok (merged, nv', tbExtra', ebExtra')) :
    (ffVarsOfFormula ebExtra ∪ bVarsOfFormula ebExtra) ⊆
      (ffVarsOfFormula ebExtra' ∪ bVarsOfFormula ebExtra') := by
  cases svTb with
  | simple s1 =>
      cases svEb with
      | simple s2 =>
          simp only [mergeSymValue, Except.ok.injEq, Prod.mk.injEq] at heq
          rw [← heq.2.2.2]
          exact mergeSimpleSymVal_ebExtra_subset nextVarId tbExtra ebExtra s1 s2
      | array _ => exact absurd heq (by simp [mergeSymValue])
  | array arrTb =>
      cases svEb with
      | simple _ => exact absurd heq (by simp [mergeSymValue])
      | array arrEb =>
          simp only [mergeSymValue] at heq
          split at heq
          · simp only [Except.ok.injEq, Prod.mk.injEq] at heq
            rw [← heq.2.2.2]
            exact mergeSimpleSymValFoldl_ebExtra_subset (arrTb.toList.zip arrEb.toList) nextVarId
              tbExtra ebExtra []
          · exact absurd heq (by simp)

/-- If `mergeSymValue`'s (possibly-grown) result satisfies a fixed assignment, so did the input
    it grew from. -/
theorem mergeSymValue_tbExtra_eval_mono {c : ZKConfig} (gconf : GlobalConfig c)
    (ms : List (FFMacro c)) (assignment' : Assignment c)
    (nextVarId : Nat) (tbExtra ebExtra : FFFormula c) (svTb svEb : SymValue c)
    (merged : SymValue c) (nv' : Nat) (tbExtra' ebExtra' : FFFormula c)
    (heq : mergeSymValue nextVarId tbExtra ebExtra svTb svEb
      = Except.ok (merged, nv', tbExtra', ebExtra')) :
    evalFormula gconf assignment' tbExtra' ms = Except.ok true →
    evalFormula gconf assignment' tbExtra ms = Except.ok true := by
  cases svTb with
  | simple s1 =>
      cases svEb with
      | simple s2 =>
          simp only [mergeSymValue, Except.ok.injEq, Prod.mk.injEq] at heq
          rw [← heq.2.2.1]
          exact mergeSimpleSymVal_tbExtra_eval_mono gconf ms assignment' nextVarId tbExtra ebExtra
            s1 s2
      | array _ => exact absurd heq (by simp [mergeSymValue])
  | array arrTb =>
      cases svEb with
      | simple _ => exact absurd heq (by simp [mergeSymValue])
      | array arrEb =>
          simp only [mergeSymValue] at heq
          split at heq
          · simp only [Except.ok.injEq, Prod.mk.injEq] at heq
            rw [← heq.2.2.1]
            exact mergeSimpleSymValFoldl_tbExtra_eval_mono gconf ms assignment'
              (arrTb.toList.zip arrEb.toList) nextVarId tbExtra ebExtra []
          · exact absurd heq (by simp)

/-- Mirror of `mergeSymValue_tbExtra_eval_mono`, for `ebExtra`. -/
theorem mergeSymValue_ebExtra_eval_mono {c : ZKConfig} (gconf : GlobalConfig c)
    (ms : List (FFMacro c)) (assignment' : Assignment c)
    (nextVarId : Nat) (tbExtra ebExtra : FFFormula c) (svTb svEb : SymValue c)
    (merged : SymValue c) (nv' : Nat) (tbExtra' ebExtra' : FFFormula c)
    (heq : mergeSymValue nextVarId tbExtra ebExtra svTb svEb
      = Except.ok (merged, nv', tbExtra', ebExtra')) :
    evalFormula gconf assignment' ebExtra' ms = Except.ok true →
    evalFormula gconf assignment' ebExtra ms = Except.ok true := by
  cases svTb with
  | simple s1 =>
      cases svEb with
      | simple s2 =>
          simp only [mergeSymValue, Except.ok.injEq, Prod.mk.injEq] at heq
          rw [← heq.2.2.2]
          exact mergeSimpleSymVal_ebExtra_eval_mono gconf ms assignment' nextVarId tbExtra ebExtra
            s1 s2
      | array _ => exact absurd heq (by simp [mergeSymValue])
  | array arrTb =>
      cases svEb with
      | simple _ => exact absurd heq (by simp [mergeSymValue])
      | array arrEb =>
          simp only [mergeSymValue] at heq
          split at heq
          · simp only [Except.ok.injEq, Prod.mk.injEq] at heq
            rw [← heq.2.2.2]
            exact mergeSimpleSymValFoldl_ebExtra_eval_mono gconf ms assignment'
              (arrTb.toList.zip arrEb.toList) nextVarId tbExtra ebExtra []
          · exact absurd heq (by simp)

/-- If a whole symbolic environment's vars are fresh below a bound, so is each of its
    entries' individually. -/
theorem symEnvVars_mem_below {c : ZKConfig} (env : SymEnv c) (id : VarID) (sv : SymValue c)
    (hget : env.get? id = some sv) (bound : Nat) (hfresh : varSetBelow (symEnvVars env) bound) :
    varSetBelow (symValVars sv) bound := by
  intro v hv
  apply hfresh
  simp only [symEnvVars]
  rw [Std.TreeMap.foldl_eq_foldl_toList]
  have hmem : (id, sv) ∈ env.toList :=
    Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr (Std.TreeMap.get?_eq_getElem? ▸ hget)
  exact foldl_union_mem_subset (fun p => symValVars p.2) env.toList (id, sv) hmem emptyVarSet v hv

/-- Every var an entry of a symbolic environment denotes is among the environment's vars --
    the subset (rather than freshness-bound) version of `symEnvVars_mem_below`. -/
theorem symValVars_subset_symEnvVars {c : ZKConfig} (env : SymEnv c) (id : VarID) (sv : SymValue c)
    (hget : env.get? id = some sv) :
    symValVars sv ⊆ symEnvVars env := by
  intro v hv
  simp only [symEnvVars]
  rw [Std.TreeMap.foldl_eq_foldl_toList]
  have hmem : (id, sv) ∈ env.toList :=
    Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr (Std.TreeMap.get?_eq_getElem? ▸ hget)
  exact foldl_union_mem_subset (fun p => symValVars p.2) env.toList (id, sv) hmem emptyVarSet v hv

/-- Set-based (`agreesOnFF`) mirror of `simpleValMatches_extend_preserves`: a match survives
    moving to any assignment that agrees on the value's own vars, regardless of how that
    agreement is phrased (a var set, rather than "below some bound"). -/
theorem simpleValMatches_agreesOnFF_preserves {c : ZKConfig} (a a' : Assignment c)
    (sv : SimpleSymVal c) (v : FF c) (vs : VarSet)
    (hsub : simpleValVars sv ⊆ vs) (hagree : agreesOnFF vs a a')
    (h : simpleValMatches a sv v) : simpleValMatches a' sv v := by
  cases sv with
  | const v' => simpa only [simpleValMatches] using h
  | ffvar vbr =>
      have hmem : Var.ffv vbr.var ∈ vs := hsub (Var.ffv vbr.var) (by simp [simpleValVars])
      simp only [simpleValMatches] at h ⊢
      rw [← hagree vbr.var hmem]
      exact h

/-- Set-based (`agreesOnFF`) mirror of `forall2_simpleValMatches_extend_preserves`. -/
theorem forall2_simpleValMatches_agreesOnFF_preserves {c : ZKConfig} (a a' : Assignment c)
    (svs : List (SimpleSymVal c)) (vs' : List (FF c)) (vs : VarSet)
    (hsub : ∀ sv ∈ svs, simpleValVars sv ⊆ vs) (hagree : agreesOnFF vs a a')
    (h : List.Forall₂ (simpleValMatches a) svs vs') :
    List.Forall₂ (simpleValMatches a') svs vs' := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hd _tl ih =>
      rename_i sv0 v0 svrest vrest
      exact List.Forall₂.cons
        (simpleValMatches_agreesOnFF_preserves a a' sv0 v0 vs
          (hsub sv0 (List.mem_cons_self ..)) hagree hd)
        (ih (fun sv hsv => hsub sv (List.mem_cons_of_mem _ hsv)))

/-- Set-based (`agreesOnFF`) mirror of `symValMatches_extend_preserves`. -/
theorem symValMatches_agreesOnFF_preserves {c : ZKConfig} (a a' : Assignment c)
    (sv : SymValue c) (v : Value c) (vs : VarSet)
    (hsub : symValVars sv ⊆ vs) (hagree : agreesOnFF vs a a')
    (h : symValMatches a sv v) : symValMatches a' sv v := by
  cases sv with
  | simple s =>
      cases v with
      | scalar v' =>
          simp only [symValMatches] at h ⊢
          exact simpleValMatches_agreesOnFF_preserves a a' s v' vs hsub hagree h
      | array _ => simp only [symValMatches] at h
  | array arr =>
      cases v with
      | scalar _ => simp only [symValMatches] at h
      | array varr =>
          simp only [symValMatches] at h ⊢
          exact forall2_simpleValMatches_agreesOnFF_preserves a a' arr.toList varr.toList vs
            (fun s hs => symValVars_array_mem_below_subset arr s hs vs hsub) hagree h

/-- `EnvMatches` survives moving to any assignment that agrees with the original on
    `symEnv`'s own vars -- the `EnvMatches`-level lifting of `symValMatches_agreesOnFF_preserves`,
    used to re-derive a match after only "irrelevant" assignment changes (no new `env'` needed). -/
theorem EnvMatches_agreesOnFF_preserves {c : ZKConfig} (a a' : Assignment c) (symEnv : SymEnv c)
    (env : Env c) (hagree : agreesOnFF (symEnvVars symEnv) a a')
    (h : EnvMatches a symEnv env) : EnvMatches a' symEnv env := by
  refine ⟨h.1, ?_⟩
  intro id sv hget
  obtain ⟨v, hv, hmatch⟩ := h.2 id sv hget
  exact ⟨v, hv, symValMatches_agreesOnFF_preserves a a' sv v (symEnvVars symEnv)
    (symValVars_subset_symEnvVars symEnv id sv hget) hagree hmatch⟩

/-- Every var `resolveSimpleExpr` reads off `symEnv` for a variable expression is among
    `symEnv`'s own vars (constants contribute none at all). -/
theorem resolveSimpleExpr_vars_subset {c : ZKConfig} (symEnv : SymEnv c) (s : SimpleExpr c)
    (sv : SimpleSymVal c) (heq : resolveSimpleExpr symEnv s = Except.ok sv) :
    simpleValVars sv ⊆ symEnvVars symEnv := by
  cases s with
  | val v' =>
      simp only [resolveSimpleExpr] at heq
      injection heq with hsv
      intro v hv
      rw [← hsv] at hv
      simp only [simpleValVars] at hv
      exact absurd hv Std.TreeSet.not_mem_emptyc
  | var id =>
      simp only [resolveSimpleExpr, Corellzk2smt.SymExec.Basic.getVar] at heq
      cases hget : symEnv.get? id with
      | none => rw [hget] at heq; simp at heq
      | some rest =>
          rw [hget] at heq
          cases rest with
          | simple sv' =>
              simp only at heq
              injection heq with hsv
              intro v hv
              rw [← hsv] at hv
              have := symValVars_subset_symEnvVars symEnv id (.simple sv') hget
              simp only [symValVars] at this
              exact this v hv
          | array _ => simp at heq

/-- Every var `encodeCond` puts into a guard formula is among the input `symEnv`'s own vars,
    and the guard never mentions a bool var. -/
theorem encodeCond_vars_subset {c : ZKConfig} (symEnv : SymEnv c) (cond : Cond c) (g : FFFormula c)
    (heq : encodeCond symEnv cond = Except.ok g) :
    (ffVarsOfFormula g ⊆ symEnvVars symEnv) ∧ (∀ v ∈ bVarsOfFormula g, False) := by
  cases cond with
  | eq s1 s2 =>
      simp only [encodeCond] at heq
      cases heq1 : resolveSimpleExpr symEnv s1 with
      | error e => rw [heq1] at heq; simp at heq
      | ok sv1 =>
          rw [heq1] at heq
          cases heq2 : resolveSimpleExpr symEnv s2 with
          | error e => rw [heq2] at heq; simp at heq
          | ok sv2 =>
              rw [heq2] at heq
              simp only at heq
              injection heq with hg
              constructor
              · intro v hv
                rw [← hg] at hv
                simp only [ffVarsOfFormula, ffVarsOfTerm_simpleSymValToTerm] at hv
                rcases Std.TreeSet.mem_union_iff.mp hv with h | h
                · exact resolveSimpleExpr_vars_subset symEnv s1 sv1 heq1 v h
                · exact resolveSimpleExpr_vars_subset symEnv s2 sv2 heq2 v h
              · intro v hv
                rw [← hg] at hv
                simp only [bVarsOfFormula, bVarsOfTerm_simpleSymValToTerm] at hv
                rcases Std.TreeSet.mem_union_iff.mp hv with h | h <;>
                  exact absurd h Std.TreeSet.not_mem_emptyc

/-- Whether two symbolic values have the same "shape" for merging purposes: both scalars, or
    both arrays of the same length. This is the well-formedness condition under which
    `mergeSymValue` is guaranteed to succeed (never hits its "type/size mismatch" error
    cases). -/
def sameShape {c : ZKConfig} (s1 s2 : SymValue c) : Prop :=
  match s1, s2 with
  | .simple _, .simple _ => True
  | .array a1, .array a2 => a1.size = a2.size
  | _, _ => False

/-- `symValMatches` pins a symbolic value's own shape to whatever concrete value it matches
    (`.simple` only ever matches `.scalar`, `.array` only ever matches a same-length `.array`) --
    so two symbolic values that respectively match a `sameShapeValue`-related pair of concrete
    values must themselves be `sameShape`. The two `symValMatches` facts are allowed to use
    *different* assignments (`assignment1`/`assignment2`) -- the proof never inspects the
    assignment's actual values, only the structural shape pinning, so nothing ties them together.
    Lets `seIfStmt_correct` derive the *symbolic* shape-agreement it needs for merging directly
    from `WellShapedCom`'s concrete one, instead of assuming it separately (see
    `Language/Core/Analysis/WellShaped.lean`'s `.if_stmt` case). -/
theorem sameShape_of_symValMatches {c : ZKConfig} (assignment1 assignment2 : Assignment c)
    (sv1 sv2 : SymValue c) (v1 v2 : Value c)
    (hm1 : symValMatches assignment1 sv1 v1) (hm2 : symValMatches assignment2 sv2 v2)
    (hshapeValue : sameShapeValue v1 v2) : sameShape sv1 sv2 := by
  cases sv1 with
  | simple _ =>
      cases v1 with
      | scalar _ =>
          cases sv2 with
          | simple _ => simp only [sameShape]
          | array a2 =>
              cases v2 with
              | scalar _ => simp only [symValMatches] at hm2
              | array _ => simp only [sameShapeValue] at hshapeValue
      | array _ => simp only [symValMatches] at hm1
  | array a1 =>
      cases v1 with
      | scalar _ => simp only [symValMatches] at hm1
      | array a1' =>
          cases sv2 with
          | simple _ =>
              cases v2 with
              | scalar _ => simp only [sameShapeValue] at hshapeValue
              | array _ => simp only [symValMatches] at hm2
          | array a2 =>
              cases v2 with
              | scalar _ => simp only [symValMatches] at hm2
              | array a2' =>
                  simp only [symValMatches] at hm1 hm2
                  simp only [sameShapeValue] at hshapeValue
                  simp only [sameShape]
                  have h1 : a1.toList.length = a1'.toList.length := hm1.length_eq
                  have h2 : a2.toList.length = a2'.toList.length := hm2.length_eq
                  simp only [Array.length_toList] at h1 h2
                  omega

theorem mergeSymValue_succeeds_of_sameShape {c : ZKConfig}
    (nextVarId : Nat) (tbExtra ebExtra : FFFormula c) (svTb svEb : SymValue c)
    (hshape : sameShape svTb svEb) :
    ∃ result, mergeSymValue nextVarId tbExtra ebExtra svTb svEb = Except.ok result := by
  cases svTb with
  | simple _ =>
      cases svEb with
      | simple _ => exact ⟨_, rfl⟩
      | array _ => simp only [sameShape] at hshape
  | array arrTb =>
      cases svEb with
      | simple _ => simp only [sameShape] at hshape
      | array arrEb =>
          simp only [sameShape] at hshape
          simp only [mergeSymValue, hshape, if_true]
          exact ⟨_, rfl⟩

/-- Bridges `SymExec.Basic.getVar`'s success to `Std.TreeMap.get?` returning `some`. -/
theorem getVar_eq_ok_iff {c : ZKConfig} (env : SymEnv c) (id : VarID) (sv : SymValue c) :
    Corellzk2smt.SymExec.Basic.getVar env id = Except.ok sv ↔ env.get? id = some sv := by
  simp only [Corellzk2smt.SymExec.Basic.getVar]
  cases env.get? id with
  | none => simp
  | some sv' => simp

/-- `mergeSymEnvKeys` never lowers the variable counter, across the whole key list. -/
theorem mergeSymEnvKeys_mono {c : ZKConfig} :
    ∀ (keys : List VarID) (nextVarId : Nat) (tbEnv ebEnv : SymEnv c) (tbExtra ebExtra : FFFormula c)
      (mergedEnv : SymEnv c) (nv' : Nat) (tbE' ebE' : FFFormula c),
      mergeSymEnvKeys nextVarId tbEnv ebEnv tbExtra ebExtra keys
        = Except.ok (mergedEnv, nv', tbE', ebE') →
      nextVarId ≤ nv' := by
  intro keys
  induction keys with
  | nil =>
      intro nextVarId tbEnv ebEnv tbExtra ebExtra mergedEnv nv' tbE' ebE' heq
      simp only [mergeSymEnvKeys, Except.ok.injEq, Prod.mk.injEq] at heq
      rw [← heq.2.1]
  | cons id rest ih =>
      intro nextVarId tbEnv ebEnv tbExtra ebExtra mergedEnv nv' tbE' ebE' heq
      cases htb : Corellzk2smt.SymExec.Basic.getVar tbEnv id with
      | error e => simp only [mergeSymEnvKeys, htb] at heq; exact absurd heq (by simp)
      | ok svTb =>
        cases heb : Corellzk2smt.SymExec.Basic.getVar ebEnv id with
        | error e => simp only [mergeSymEnvKeys, htb, heb] at heq; exact absurd heq (by simp)
        | ok svEb =>
          cases hmv : mergeSymValue nextVarId tbExtra ebExtra svTb svEb with
          | error e => simp only [mergeSymEnvKeys, htb, heb, hmv] at heq; exact absurd heq (by simp)
          | ok result =>
            obtain ⟨mergedVal, nv1, tbE1, ebE1⟩ := result
            cases hrec : mergeSymEnvKeys nv1 tbEnv ebEnv tbE1 ebE1 rest with
            | error e =>
                simp only [mergeSymEnvKeys, htb, heb, hmv, hrec] at heq; exact absurd heq (by simp)
            | ok recResult =>
              obtain ⟨restEnv, nv'', tbE'', ebE''⟩ := recResult
              simp only [mergeSymEnvKeys, htb, heb, hmv, hrec, Except.ok.injEq, Prod.mk.injEq]
                at heq
              rw [← heq.2.1]
              exact le_trans (mergeSymValue_mono nextVarId tbExtra ebExtra svTb svEb mergedVal nv1
                tbE1 ebE1 hmv) (ih nv1 tbEnv ebEnv tbE1 ebE1 restEnv nv'' tbE'' ebE'' hrec)

/-- The `tbE'` that `mergeSymEnvKeys` produces is fresh below the new counter, across the whole
    key list. -/
theorem mergeSymEnvKeys_tbExtra_fresh {c : ZKConfig} :
    ∀ (keys : List VarID) (nextVarId : Nat) (tbEnv ebEnv : SymEnv c) (tbExtra ebExtra : FFFormula c)
      (mergedEnv : SymEnv c) (nv' : Nat) (tbE' ebE' : FFFormula c),
      mergeSymEnvKeys nextVarId tbEnv ebEnv tbExtra ebExtra keys
        = Except.ok (mergedEnv, nv', tbE', ebE') →
      varSetBelow (ffVarsOfFormula tbExtra ∪ bVarsOfFormula tbExtra) nextVarId →
      varSetBelow (symEnvVars tbEnv) nextVarId →
      varSetBelow (ffVarsOfFormula tbE' ∪ bVarsOfFormula tbE') nv' := by
  intro keys
  induction keys with
  | nil =>
      intro nextVarId tbEnv ebEnv tbExtra ebExtra mergedEnv nv' tbE' ebE' heq hfresh _htbEnvFresh
      simp only [mergeSymEnvKeys, Except.ok.injEq, Prod.mk.injEq] at heq
      rw [← heq.2.1, ← heq.2.2.1]
      exact hfresh
  | cons id rest ih =>
      intro nextVarId tbEnv ebEnv tbExtra ebExtra mergedEnv nv' tbE' ebE' heq hfresh htbEnvFresh
      cases htb : Corellzk2smt.SymExec.Basic.getVar tbEnv id with
      | error e => simp only [mergeSymEnvKeys, htb] at heq; exact absurd heq (by simp)
      | ok svTb =>
        cases heb : Corellzk2smt.SymExec.Basic.getVar ebEnv id with
        | error e => simp only [mergeSymEnvKeys, htb, heb] at heq; exact absurd heq (by simp)
        | ok svEb =>
          cases hmv : mergeSymValue nextVarId tbExtra ebExtra svTb svEb with
          | error e => simp only [mergeSymEnvKeys, htb, heb, hmv] at heq; exact absurd heq (by simp)
          | ok result =>
            obtain ⟨mergedVal, nv1, tbE1, ebE1⟩ := result
            cases hrec : mergeSymEnvKeys nv1 tbEnv ebEnv tbE1 ebE1 rest with
            | error e =>
                simp only [mergeSymEnvKeys, htb, heb, hmv, hrec] at heq; exact absurd heq (by simp)
            | ok recResult =>
              obtain ⟨restEnv, nv'', tbE'', ebE''⟩ := recResult
              simp only [mergeSymEnvKeys, htb, heb, hmv, hrec, Except.ok.injEq, Prod.mk.injEq]
                at heq
              rw [← heq.2.1, ← heq.2.2.1]
              have htb_get : tbEnv.get? id = some svTb := (getVar_eq_ok_iff tbEnv id svTb).mp htb
              have hsvTbFresh : varSetBelow (symValVars svTb) nextVarId :=
                symEnvVars_mem_below tbEnv id svTb htb_get nextVarId htbEnvFresh
              have htbE1Fresh := mergeSymValue_tbExtra_fresh nextVarId tbExtra ebExtra svTb svEb
                mergedVal nv1 tbE1 ebE1 hmv hfresh hsvTbFresh
              have hnvMono1 := mergeSymValue_mono nextVarId tbExtra ebExtra svTb svEb mergedVal nv1
                tbE1 ebE1 hmv
              exact ih nv1 tbEnv ebEnv tbE1 ebE1 restEnv nv'' tbE'' ebE'' hrec htbE1Fresh
                (varSetBelow_mono hnvMono1 htbEnvFresh)

/-- Mirror of `mergeSymEnvKeys_tbExtra_fresh`, for `ebExtra`. -/
theorem mergeSymEnvKeys_ebExtra_fresh {c : ZKConfig} :
    ∀ (keys : List VarID) (nextVarId : Nat) (tbEnv ebEnv : SymEnv c) (tbExtra ebExtra : FFFormula c)
      (mergedEnv : SymEnv c) (nv' : Nat) (tbE' ebE' : FFFormula c),
      mergeSymEnvKeys nextVarId tbEnv ebEnv tbExtra ebExtra keys
        = Except.ok (mergedEnv, nv', tbE', ebE') →
      varSetBelow (ffVarsOfFormula ebExtra ∪ bVarsOfFormula ebExtra) nextVarId →
      varSetBelow (symEnvVars ebEnv) nextVarId →
      varSetBelow (ffVarsOfFormula ebE' ∪ bVarsOfFormula ebE') nv' := by
  intro keys
  induction keys with
  | nil =>
      intro nextVarId tbEnv ebEnv tbExtra ebExtra mergedEnv nv' tbE' ebE' heq hfresh _hebEnvFresh
      simp only [mergeSymEnvKeys, Except.ok.injEq, Prod.mk.injEq] at heq
      rw [← heq.2.1, ← heq.2.2.2]
      exact hfresh
  | cons id rest ih =>
      intro nextVarId tbEnv ebEnv tbExtra ebExtra mergedEnv nv' tbE' ebE' heq hfresh hebEnvFresh
      cases htb : Corellzk2smt.SymExec.Basic.getVar tbEnv id with
      | error e => simp only [mergeSymEnvKeys, htb] at heq; exact absurd heq (by simp)
      | ok svTb =>
        cases heb : Corellzk2smt.SymExec.Basic.getVar ebEnv id with
        | error e => simp only [mergeSymEnvKeys, htb, heb] at heq; exact absurd heq (by simp)
        | ok svEb =>
          cases hmv : mergeSymValue nextVarId tbExtra ebExtra svTb svEb with
          | error e => simp only [mergeSymEnvKeys, htb, heb, hmv] at heq; exact absurd heq (by simp)
          | ok result =>
            obtain ⟨mergedVal, nv1, tbE1, ebE1⟩ := result
            cases hrec : mergeSymEnvKeys nv1 tbEnv ebEnv tbE1 ebE1 rest with
            | error e =>
                simp only [mergeSymEnvKeys, htb, heb, hmv, hrec] at heq; exact absurd heq (by simp)
            | ok recResult =>
              obtain ⟨restEnv, nv'', tbE'', ebE''⟩ := recResult
              simp only [mergeSymEnvKeys, htb, heb, hmv, hrec, Except.ok.injEq, Prod.mk.injEq]
                at heq
              rw [← heq.2.1, ← heq.2.2.2]
              have heb_get : ebEnv.get? id = some svEb := (getVar_eq_ok_iff ebEnv id svEb).mp heb
              have hsvEbFresh : varSetBelow (symValVars svEb) nextVarId :=
                symEnvVars_mem_below ebEnv id svEb heb_get nextVarId hebEnvFresh
              have hebE1Fresh := mergeSymValue_ebExtra_fresh nextVarId tbExtra ebExtra svTb svEb
                mergedVal nv1 tbE1 ebE1 hmv hfresh hsvEbFresh
              have hnvMono1 := mergeSymValue_mono nextVarId tbExtra ebExtra svTb svEb mergedVal nv1
                tbE1 ebE1 hmv
              exact ih nv1 tbEnv ebEnv tbE1 ebE1 restEnv nv'' tbE'' ebE'' hrec hebE1Fresh
                (varSetBelow_mono hnvMono1 hebEnvFresh)

/-- Subset-or-fresh analog of `mergeSymEnvKeys_tbExtra_fresh`: every var the accumulated
    `tbE'` mentions is either one somewhere in `tbEnv`, or genuinely new relative to the
    counter the merge started from. -/
theorem mergeSymEnvKeys_tbExtra_merged_subset {c : ZKConfig} (startVarId : Nat) :
    ∀ (keys : List VarID) (nextVarId : Nat) (tbEnv ebEnv : SymEnv c) (tbExtra ebExtra : FFFormula c)
      (mergedEnv : SymEnv c) (nv' : Nat) (tbE' ebE' : FFFormula c),
      mergeSymEnvKeys nextVarId tbEnv ebEnv tbExtra ebExtra keys
        = Except.ok (mergedEnv, nv', tbE', ebE') →
      startVarId ≤ nextVarId →
      (∀ v ∈ (ffVarsOfFormula tbExtra ∪ bVarsOfFormula tbExtra),
        v ∈ symEnvVars tbEnv ∨ startVarId ≤ varIndex v) →
      ∀ v ∈ (ffVarsOfFormula tbE' ∪ bVarsOfFormula tbE'),
        v ∈ symEnvVars tbEnv ∨ startVarId ≤ varIndex v := by
  intro keys
  induction keys with
  | nil =>
      intro nextVarId tbEnv ebEnv tbExtra ebExtra mergedEnv nv' tbE' ebE' heq _hstart hsubset
      simp only [mergeSymEnvKeys, Except.ok.injEq, Prod.mk.injEq] at heq
      rw [← heq.2.2.1]
      exact hsubset
  | cons id rest ih =>
      intro nextVarId tbEnv ebEnv tbExtra ebExtra mergedEnv nv' tbE' ebE' heq hstart hsubset
      cases htb : Corellzk2smt.SymExec.Basic.getVar tbEnv id with
      | error e => simp only [mergeSymEnvKeys, htb] at heq; exact absurd heq (by simp)
      | ok svTb =>
        cases heb : Corellzk2smt.SymExec.Basic.getVar ebEnv id with
        | error e => simp only [mergeSymEnvKeys, htb, heb] at heq; exact absurd heq (by simp)
        | ok svEb =>
          cases hmv : mergeSymValue nextVarId tbExtra ebExtra svTb svEb with
          | error e => simp only [mergeSymEnvKeys, htb, heb, hmv] at heq; exact absurd heq (by simp)
          | ok result =>
            obtain ⟨mergedVal, nv1, tbE1, ebE1⟩ := result
            cases hrec : mergeSymEnvKeys nv1 tbEnv ebEnv tbE1 ebE1 rest with
            | error e =>
                simp only [mergeSymEnvKeys, htb, heb, hmv, hrec] at heq; exact absurd heq (by simp)
            | ok recResult =>
              obtain ⟨restEnv, nv'', tbE'', ebE''⟩ := recResult
              simp only [mergeSymEnvKeys, htb, heb, hmv, hrec, Except.ok.injEq, Prod.mk.injEq]
                at heq
              rw [← heq.2.2.1]
              have htb_get : tbEnv.get? id = some svTb := (getVar_eq_ok_iff tbEnv id svTb).mp htb
              have hsvTbSub : symValVars svTb ⊆ symEnvVars tbEnv :=
                symValVars_subset_symEnvVars tbEnv id svTb htb_get
              have hnvMono1 := mergeSymValue_mono nextVarId tbExtra ebExtra svTb svEb mergedVal nv1
                tbE1 ebE1 hmv
              have htbE1Subset : ∀ v ∈ (ffVarsOfFormula tbE1 ∪ bVarsOfFormula tbE1),
                  v ∈ symEnvVars tbEnv ∨ startVarId ≤ varIndex v := by
                intro v hv
                rcases mergeSymValue_tbExtra_merged_subset (symEnvVars tbEnv) startVarId nextVarId
                    tbExtra ebExtra svTb svEb mergedVal nv1 tbE1 ebE1 hmv hstart hsubset hsvTbSub v
                    hv with h | h
                · exact Or.inl h
                · exact Or.inr h
              exact ih nv1 tbEnv ebEnv tbE1 ebE1 restEnv nv'' tbE'' ebE'' hrec
                (hstart.trans hnvMono1) htbE1Subset

/-- Mirror of `mergeSymEnvKeys_tbExtra_merged_subset`, for `ebExtra`. -/
theorem mergeSymEnvKeys_ebExtra_merged_subset {c : ZKConfig} (startVarId : Nat) :
    ∀ (keys : List VarID) (nextVarId : Nat) (tbEnv ebEnv : SymEnv c) (tbExtra ebExtra : FFFormula c)
      (mergedEnv : SymEnv c) (nv' : Nat) (tbE' ebE' : FFFormula c),
      mergeSymEnvKeys nextVarId tbEnv ebEnv tbExtra ebExtra keys
        = Except.ok (mergedEnv, nv', tbE', ebE') →
      startVarId ≤ nextVarId →
      (∀ v ∈ (ffVarsOfFormula ebExtra ∪ bVarsOfFormula ebExtra),
        v ∈ symEnvVars ebEnv ∨ startVarId ≤ varIndex v) →
      ∀ v ∈ (ffVarsOfFormula ebE' ∪ bVarsOfFormula ebE'),
        v ∈ symEnvVars ebEnv ∨ startVarId ≤ varIndex v := by
  intro keys
  induction keys with
  | nil =>
      intro nextVarId tbEnv ebEnv tbExtra ebExtra mergedEnv nv' tbE' ebE' heq _hstart hsubset
      simp only [mergeSymEnvKeys, Except.ok.injEq, Prod.mk.injEq] at heq
      rw [← heq.2.2.2]
      exact hsubset
  | cons id rest ih =>
      intro nextVarId tbEnv ebEnv tbExtra ebExtra mergedEnv nv' tbE' ebE' heq hstart hsubset
      cases htb : Corellzk2smt.SymExec.Basic.getVar tbEnv id with
      | error e => simp only [mergeSymEnvKeys, htb] at heq; exact absurd heq (by simp)
      | ok svTb =>
        cases heb : Corellzk2smt.SymExec.Basic.getVar ebEnv id with
        | error e => simp only [mergeSymEnvKeys, htb, heb] at heq; exact absurd heq (by simp)
        | ok svEb =>
          cases hmv : mergeSymValue nextVarId tbExtra ebExtra svTb svEb with
          | error e => simp only [mergeSymEnvKeys, htb, heb, hmv] at heq; exact absurd heq (by simp)
          | ok result =>
            obtain ⟨mergedVal, nv1, tbE1, ebE1⟩ := result
            cases hrec : mergeSymEnvKeys nv1 tbEnv ebEnv tbE1 ebE1 rest with
            | error e =>
                simp only [mergeSymEnvKeys, htb, heb, hmv, hrec] at heq; exact absurd heq (by simp)
            | ok recResult =>
              obtain ⟨restEnv, nv'', tbE'', ebE''⟩ := recResult
              simp only [mergeSymEnvKeys, htb, heb, hmv, hrec, Except.ok.injEq, Prod.mk.injEq]
                at heq
              rw [← heq.2.2.2]
              have heb_get : ebEnv.get? id = some svEb := (getVar_eq_ok_iff ebEnv id svEb).mp heb
              have hsvEbSub : symValVars svEb ⊆ symEnvVars ebEnv :=
                symValVars_subset_symEnvVars ebEnv id svEb heb_get
              have hnvMono1 := mergeSymValue_mono nextVarId tbExtra ebExtra svTb svEb mergedVal nv1
                tbE1 ebE1 hmv
              have hebE1Subset : ∀ v ∈ (ffVarsOfFormula ebE1 ∪ bVarsOfFormula ebE1),
                  v ∈ symEnvVars ebEnv ∨ startVarId ≤ varIndex v := by
                intro v hv
                rcases mergeSymValue_ebExtra_merged_subset (symEnvVars ebEnv) startVarId nextVarId
                    tbExtra ebExtra svTb svEb mergedVal nv1 tbE1 ebE1 hmv hstart hsubset hsvEbSub v
                    hv with h | h
                · exact Or.inl h
                · exact Or.inr h
              exact ih nv1 tbEnv ebEnv tbE1 ebE1 restEnv nv'' tbE'' ebE'' hrec
                (hstart.trans hnvMono1) hebE1Subset

/-- `mergeSymEnvKeys` only ever grows `tbExtra`'s footprint, across the whole key list. -/
theorem mergeSymEnvKeys_tbExtra_subset {c : ZKConfig} :
    ∀ (keys : List VarID) (nextVarId : Nat) (tbEnv ebEnv : SymEnv c) (tbExtra ebExtra : FFFormula c)
      (mergedEnv : SymEnv c) (nv' : Nat) (tbE' ebE' : FFFormula c),
      mergeSymEnvKeys nextVarId tbEnv ebEnv tbExtra ebExtra keys
        = Except.ok (mergedEnv, nv', tbE', ebE') →
      (ffVarsOfFormula tbExtra ∪ bVarsOfFormula tbExtra) ⊆ (ffVarsOfFormula tbE' ∪ bVarsOfFormula tbE') := by
  intro keys
  induction keys with
  | nil =>
      intro nextVarId tbEnv ebEnv tbExtra ebExtra mergedEnv nv' tbE' ebE' heq
      simp only [mergeSymEnvKeys, Except.ok.injEq, Prod.mk.injEq] at heq
      rw [← heq.2.2.1]
      exact fun v hv => hv
  | cons id rest ih =>
      intro nextVarId tbEnv ebEnv tbExtra ebExtra mergedEnv nv' tbE' ebE' heq
      cases htb : Corellzk2smt.SymExec.Basic.getVar tbEnv id with
      | error e => simp only [mergeSymEnvKeys, htb] at heq; exact absurd heq (by simp)
      | ok svTb =>
        cases heb : Corellzk2smt.SymExec.Basic.getVar ebEnv id with
        | error e => simp only [mergeSymEnvKeys, htb, heb] at heq; exact absurd heq (by simp)
        | ok svEb =>
          cases hmv : mergeSymValue nextVarId tbExtra ebExtra svTb svEb with
          | error e => simp only [mergeSymEnvKeys, htb, heb, hmv] at heq; exact absurd heq (by simp)
          | ok result =>
            obtain ⟨mergedVal, nv1, tbE1, ebE1⟩ := result
            cases hrec : mergeSymEnvKeys nv1 tbEnv ebEnv tbE1 ebE1 rest with
            | error e => simp only [mergeSymEnvKeys, htb, heb, hmv, hrec] at heq; exact absurd heq (by simp)
            | ok recResult =>
              obtain ⟨restEnv, nv'', tbE'', ebE''⟩ := recResult
              simp only [mergeSymEnvKeys, htb, heb, hmv, hrec, Except.ok.injEq, Prod.mk.injEq]
                at heq
              have hstep := mergeSymValue_tbExtra_subset nextVarId tbExtra ebExtra svTb svEb
                mergedVal nv1 tbE1 ebE1 hmv
              have hrest := ih nv1 tbEnv ebEnv tbE1 ebE1 restEnv nv'' tbE'' ebE'' hrec
              rw [← heq.2.2.1]
              exact fun v hv => hrest v (hstep v hv)

/-- Mirror of `mergeSymEnvKeys_tbExtra_subset`, for `ebExtra`. -/
theorem mergeSymEnvKeys_ebExtra_subset {c : ZKConfig} :
    ∀ (keys : List VarID) (nextVarId : Nat) (tbEnv ebEnv : SymEnv c) (tbExtra ebExtra : FFFormula c)
      (mergedEnv : SymEnv c) (nv' : Nat) (tbE' ebE' : FFFormula c),
      mergeSymEnvKeys nextVarId tbEnv ebEnv tbExtra ebExtra keys
        = Except.ok (mergedEnv, nv', tbE', ebE') →
      (ffVarsOfFormula ebExtra ∪ bVarsOfFormula ebExtra) ⊆ (ffVarsOfFormula ebE' ∪ bVarsOfFormula ebE') := by
  intro keys
  induction keys with
  | nil =>
      intro nextVarId tbEnv ebEnv tbExtra ebExtra mergedEnv nv' tbE' ebE' heq
      simp only [mergeSymEnvKeys, Except.ok.injEq, Prod.mk.injEq] at heq
      rw [← heq.2.2.2]
      exact fun v hv => hv
  | cons id rest ih =>
      intro nextVarId tbEnv ebEnv tbExtra ebExtra mergedEnv nv' tbE' ebE' heq
      cases htb : Corellzk2smt.SymExec.Basic.getVar tbEnv id with
      | error e => simp only [mergeSymEnvKeys, htb] at heq; exact absurd heq (by simp)
      | ok svTb =>
        cases heb : Corellzk2smt.SymExec.Basic.getVar ebEnv id with
        | error e => simp only [mergeSymEnvKeys, htb, heb] at heq; exact absurd heq (by simp)
        | ok svEb =>
          cases hmv : mergeSymValue nextVarId tbExtra ebExtra svTb svEb with
          | error e => simp only [mergeSymEnvKeys, htb, heb, hmv] at heq; exact absurd heq (by simp)
          | ok result =>
            obtain ⟨mergedVal, nv1, tbE1, ebE1⟩ := result
            cases hrec : mergeSymEnvKeys nv1 tbEnv ebEnv tbE1 ebE1 rest with
            | error e => simp only [mergeSymEnvKeys, htb, heb, hmv, hrec] at heq; exact absurd heq (by simp)
            | ok recResult =>
              obtain ⟨restEnv, nv'', tbE'', ebE''⟩ := recResult
              simp only [mergeSymEnvKeys, htb, heb, hmv, hrec, Except.ok.injEq, Prod.mk.injEq]
                at heq
              have hstep := mergeSymValue_ebExtra_subset nextVarId tbExtra ebExtra svTb svEb
                mergedVal nv1 tbE1 ebE1 hmv
              have hrest := ih nv1 tbEnv ebEnv tbE1 ebE1 restEnv nv'' tbE'' ebE'' hrec
              rw [← heq.2.2.2]
              exact fun v hv => hrest v (hstep v hv)

/-- `mergeSymEnvKeys`'s output has exactly `keys` as its domain -- every key it processes gets
    set exactly once (via `setVar`), and nothing else. -/
theorem mergeSymEnvKeys_domain {c : ZKConfig} :
    ∀ (keys : List VarID) (nextVarId : Nat) (tbEnv ebEnv : SymEnv c) (tbExtra ebExtra : FFFormula c)
      (mergedEnv : SymEnv c) (nv' : Nat) (tbE' ebE' : FFFormula c),
      mergeSymEnvKeys nextVarId tbEnv ebEnv tbExtra ebExtra keys
        = Except.ok (mergedEnv, nv', tbE', ebE') →
      ∀ id, mergedEnv.contains id ↔ id ∈ keys := by
  intro keys
  induction keys with
  | nil =>
      intro nextVarId tbEnv ebEnv tbExtra ebExtra mergedEnv nv' tbE' ebE' heq id
      simp only [mergeSymEnvKeys, Except.ok.injEq, Prod.mk.injEq] at heq
      rw [← heq.1]
      simp [Corellzk2smt.SymExec.Basic.emptySymEnv]
  | cons id0 rest ih =>
      intro nextVarId tbEnv ebEnv tbExtra ebExtra mergedEnv nv' tbE' ebE' heq id
      cases htb : Corellzk2smt.SymExec.Basic.getVar tbEnv id0 with
      | error e => simp only [mergeSymEnvKeys, htb] at heq; exact absurd heq (by simp)
      | ok svTb =>
        cases heb : Corellzk2smt.SymExec.Basic.getVar ebEnv id0 with
        | error e => simp only [mergeSymEnvKeys, htb, heb] at heq; exact absurd heq (by simp)
        | ok svEb =>
          cases hmv : mergeSymValue nextVarId tbExtra ebExtra svTb svEb with
          | error e =>
              simp only [mergeSymEnvKeys, htb, heb, hmv] at heq; exact absurd heq (by simp)
          | ok result =>
            obtain ⟨mergedVal, nv1, tbE1, ebE1⟩ := result
            cases hrec : mergeSymEnvKeys nv1 tbEnv ebEnv tbE1 ebE1 rest with
            | error e =>
                simp only [mergeSymEnvKeys, htb, heb, hmv, hrec] at heq; exact absurd heq (by simp)
            | ok recResult =>
              obtain ⟨restEnv, nv'', tbE'', ebE''⟩ := recResult
              simp only [mergeSymEnvKeys, htb, heb, hmv, hrec, Except.ok.injEq, Prod.mk.injEq]
                at heq
              rw [← heq.1]
              have hrest := ih nv1 tbEnv ebEnv tbE1 ebE1 restEnv nv'' tbE'' ebE'' hrec id
              by_cases hideq : id = id0
              · subst hideq
                simp only [Corellzk2smt.SymExec.Basic.setVar, Std.TreeMap.contains_insert,
                  List.mem_cons, true_or, iff_true]
                simp
              · have hne : id0 ≠ id := Ne.symm hideq
                simp [Corellzk2smt.SymExec.Basic.setVar, Std.TreeMap.contains_insert,
                  List.mem_cons, hrest, hne, hideq]

/-- Every value `mergeSymEnvKeys` binds a key to is fresh below the new counter -- the
    per-key version of `mergeSymValue_result_fresh`, lifted across the whole key list. -/
theorem mergeSymEnvKeys_result_fresh {c : ZKConfig} :
    ∀ (keys : List VarID) (nextVarId : Nat) (tbEnv ebEnv : SymEnv c) (tbExtra ebExtra : FFFormula c)
      (mergedEnv : SymEnv c) (nv' : Nat) (tbE' ebE' : FFFormula c),
      mergeSymEnvKeys nextVarId tbEnv ebEnv tbExtra ebExtra keys
        = Except.ok (mergedEnv, nv', tbE', ebE') →
      varSetBelow (symEnvVars tbEnv) nextVarId →
      ∀ id sv, mergedEnv.get? id = some sv → varSetBelow (symValVars sv) nv' := by
  intro keys
  induction keys with
  | nil =>
      intro nextVarId tbEnv ebEnv tbExtra ebExtra mergedEnv nv' tbE' ebE' heq _htbEnvFresh id sv hsv
      simp only [mergeSymEnvKeys, Except.ok.injEq, Prod.mk.injEq] at heq
      rw [← heq.1] at hsv
      exact absurd hsv (by simp [Corellzk2smt.SymExec.Basic.emptySymEnv])
  | cons id0 rest ih =>
      intro nextVarId tbEnv ebEnv tbExtra ebExtra mergedEnv nv' tbE' ebE' heq htbEnvFresh id sv hsv
      cases htb : Corellzk2smt.SymExec.Basic.getVar tbEnv id0 with
      | error e => simp only [mergeSymEnvKeys, htb] at heq; exact absurd heq (by simp)
      | ok svTb =>
        cases heb : Corellzk2smt.SymExec.Basic.getVar ebEnv id0 with
        | error e => simp only [mergeSymEnvKeys, htb, heb] at heq; exact absurd heq (by simp)
        | ok svEb =>
          cases hmv : mergeSymValue nextVarId tbExtra ebExtra svTb svEb with
          | error e => simp only [mergeSymEnvKeys, htb, heb, hmv] at heq; exact absurd heq (by simp)
          | ok result =>
            obtain ⟨mergedVal, nv1, tbE1, ebE1⟩ := result
            cases hrec : mergeSymEnvKeys nv1 tbEnv ebEnv tbE1 ebE1 rest with
            | error e =>
                simp only [mergeSymEnvKeys, htb, heb, hmv, hrec] at heq; exact absurd heq (by simp)
            | ok recResult =>
              obtain ⟨restEnv, nv'', tbE'', ebE''⟩ := recResult
              simp only [mergeSymEnvKeys, htb, heb, hmv, hrec, Except.ok.injEq, Prod.mk.injEq]
                at heq
              rw [← heq.1] at hsv
              have htb_get : tbEnv.get? id0 = some svTb := (getVar_eq_ok_iff tbEnv id0 svTb).mp htb
              have hsvTbFresh : varSetBelow (symValVars svTb) nextVarId :=
                symEnvVars_mem_below tbEnv id0 svTb htb_get nextVarId htbEnvFresh
              have hnvMono1 := mergeSymValue_mono nextVarId tbExtra ebExtra svTb svEb mergedVal nv1
                tbE1 ebE1 hmv
              have hnvMono2 := mergeSymEnvKeys_mono rest nv1 tbEnv ebEnv tbE1 ebE1 restEnv nv''
                tbE'' ebE'' hrec
              by_cases hideq : id = id0
              · subst hideq
                have hval : sv = mergedVal := by
                  rw [Corellzk2smt.SymExec.Basic.setVar, Std.TreeMap.get?_eq_getElem?,
                    Std.TreeMap.getElem?_insert_self] at hsv
                  injection hsv with hsv'
                  exact hsv'.symm
                rw [hval, ← heq.2.1]
                exact varSetBelow_mono hnvMono2
                  (mergeSymValue_result_fresh nextVarId tbExtra ebExtra svTb svEb mergedVal nv1
                    tbE1 ebE1 hmv hsvTbFresh)
              · have hne : id0 ≠ id := Ne.symm hideq
                rw [Corellzk2smt.SymExec.Basic.setVar, Std.TreeMap.get?_eq_getElem?,
                  Std.TreeMap.getElem?_insert, if_neg (by simp [hne])] at hsv
                rw [← Std.TreeMap.get?_eq_getElem?] at hsv
                rw [← heq.2.1]
                exact ih nv1 tbEnv ebEnv tbE1 ebE1 restEnv nv'' tbE'' ebE'' hrec
                  (varSetBelow_mono hnvMono1 htbEnvFresh) id sv hsv

/-- Subset-or-fresh analog of `mergeSymEnvKeys_result_fresh`: every var a merged key's value
    mentions is either one `tbEnv` already had somewhere, or genuinely new relative to the
    counter the merge started from. -/
theorem mergeSymEnvKeys_merged_subset {c : ZKConfig} :
    ∀ (keys : List VarID) (nextVarId : Nat) (tbEnv ebEnv : SymEnv c) (tbExtra ebExtra : FFFormula c)
      (mergedEnv : SymEnv c) (nv' : Nat) (tbE' ebE' : FFFormula c),
      mergeSymEnvKeys nextVarId tbEnv ebEnv tbExtra ebExtra keys
        = Except.ok (mergedEnv, nv', tbE', ebE') →
      ∀ id sv, mergedEnv.get? id = some sv →
        ∀ v ∈ symValVars sv, v ∈ symEnvVars tbEnv ∨ nextVarId ≤ varIndex v := by
  intro keys
  induction keys with
  | nil =>
      intro nextVarId tbEnv ebEnv tbExtra ebExtra mergedEnv nv' tbE' ebE' heq id sv hsv v hv
      simp only [mergeSymEnvKeys, Except.ok.injEq, Prod.mk.injEq] at heq
      rw [← heq.1] at hsv
      exact absurd hsv (by simp [Corellzk2smt.SymExec.Basic.emptySymEnv])
  | cons id0 rest ih =>
      intro nextVarId tbEnv ebEnv tbExtra ebExtra mergedEnv nv' tbE' ebE' heq id sv hsv v hv
      cases htb : Corellzk2smt.SymExec.Basic.getVar tbEnv id0 with
      | error e => simp only [mergeSymEnvKeys, htb] at heq; exact absurd heq (by simp)
      | ok svTb =>
        cases heb : Corellzk2smt.SymExec.Basic.getVar ebEnv id0 with
        | error e => simp only [mergeSymEnvKeys, htb, heb] at heq; exact absurd heq (by simp)
        | ok svEb =>
          cases hmv : mergeSymValue nextVarId tbExtra ebExtra svTb svEb with
          | error e => simp only [mergeSymEnvKeys, htb, heb, hmv] at heq; exact absurd heq (by simp)
          | ok result =>
            obtain ⟨mergedVal, nv1, tbE1, ebE1⟩ := result
            cases hrec : mergeSymEnvKeys nv1 tbEnv ebEnv tbE1 ebE1 rest with
            | error e =>
                simp only [mergeSymEnvKeys, htb, heb, hmv, hrec] at heq; exact absurd heq (by simp)
            | ok recResult =>
              obtain ⟨restEnv, nv'', tbE'', ebE''⟩ := recResult
              simp only [mergeSymEnvKeys, htb, heb, hmv, hrec, Except.ok.injEq, Prod.mk.injEq]
                at heq
              rw [← heq.1] at hsv
              have htb_get : tbEnv.get? id0 = some svTb := (getVar_eq_ok_iff tbEnv id0 svTb).mp htb
              have htbSub : symValVars svTb ⊆ symEnvVars tbEnv :=
                symValVars_subset_symEnvVars tbEnv id0 svTb htb_get
              have hnvMono1 := mergeSymValue_mono nextVarId tbExtra ebExtra svTb svEb mergedVal nv1
                tbE1 ebE1 hmv
              by_cases hideq : id = id0
              · subst hideq
                have hval : sv = mergedVal := by
                  rw [Corellzk2smt.SymExec.Basic.setVar, Std.TreeMap.get?_eq_getElem?,
                    Std.TreeMap.getElem?_insert_self] at hsv
                  injection hsv with hsv'
                  exact hsv'.symm
                rw [hval] at hv
                rcases mergeSymValue_merged_subset nextVarId tbExtra ebExtra svTb svEb mergedVal nv1
                    tbE1 ebE1 hmv v hv with h | h
                · exact Or.inl (htbSub v h)
                · exact Or.inr h
              · have hne : id0 ≠ id := Ne.symm hideq
                rw [Corellzk2smt.SymExec.Basic.setVar, Std.TreeMap.get?_eq_getElem?,
                  Std.TreeMap.getElem?_insert, if_neg (by simp [hne])] at hsv
                rw [← Std.TreeMap.get?_eq_getElem?] at hsv
                rcases ih nv1 tbEnv ebEnv tbE1 ebE1 restEnv nv'' tbE'' ebE'' hrec id sv hsv v hv with
                  h | h
                · exact Or.inl h
                · exact Or.inr (hnvMono1.trans h)

/-- If `mergeSymEnvKeys`'s *final* accumulated `tbExtra` is satisfied by a fixed assignment, so
    is the *starting* `tbExtra` it was built on top of -- across the whole key list, mirroring
    `mergeSimpleSymValFoldl_tbExtra_eval_mono` one level up. -/
theorem mergeSymEnvKeys_tbExtra_eval_mono {c : ZKConfig} (gconf : GlobalConfig c)
    (ms : List (FFMacro c)) (assignment' : Assignment c) :
    ∀ (keys : List VarID) (nextVarId : Nat) (tbEnv ebEnv : SymEnv c) (tbExtra ebExtra : FFFormula c)
      (mergedEnv : SymEnv c) (nv' : Nat) (tbE' ebE' : FFFormula c),
      mergeSymEnvKeys nextVarId tbEnv ebEnv tbExtra ebExtra keys
        = Except.ok (mergedEnv, nv', tbE', ebE') →
      evalFormula gconf assignment' tbE' ms = Except.ok true →
      evalFormula gconf assignment' tbExtra ms = Except.ok true := by
  intro keys
  induction keys with
  | nil =>
      intro nextVarId tbEnv ebEnv tbExtra ebExtra mergedEnv nv' tbE' ebE' heq h
      simp only [mergeSymEnvKeys, Except.ok.injEq, Prod.mk.injEq] at heq
      rw [← heq.2.2.1] at h
      exact h
  | cons id rest ih =>
      intro nextVarId tbEnv ebEnv tbExtra ebExtra mergedEnv nv' tbE' ebE' heq h
      cases htb : Corellzk2smt.SymExec.Basic.getVar tbEnv id with
      | error e => simp only [mergeSymEnvKeys, htb] at heq; exact absurd heq (by simp)
      | ok svTb =>
        cases heb : Corellzk2smt.SymExec.Basic.getVar ebEnv id with
        | error e => simp only [mergeSymEnvKeys, htb, heb] at heq; exact absurd heq (by simp)
        | ok svEb =>
          cases hmv : mergeSymValue nextVarId tbExtra ebExtra svTb svEb with
          | error e => simp only [mergeSymEnvKeys, htb, heb, hmv] at heq; exact absurd heq (by simp)
          | ok result =>
            obtain ⟨mergedVal, nv1, tbE1, ebE1⟩ := result
            cases hrec : mergeSymEnvKeys nv1 tbEnv ebEnv tbE1 ebE1 rest with
            | error e =>
                simp only [mergeSymEnvKeys, htb, heb, hmv, hrec] at heq; exact absurd heq (by simp)
            | ok recResult =>
              obtain ⟨restEnv, nv'', tbE'', ebE''⟩ := recResult
              simp only [mergeSymEnvKeys, htb, heb, hmv, hrec, Except.ok.injEq, Prod.mk.injEq]
                at heq
              rw [← heq.2.2.1] at h
              have hrest := ih nv1 tbEnv ebEnv tbE1 ebE1 restEnv nv'' tbE'' ebE'' hrec h
              exact mergeSymValue_tbExtra_eval_mono gconf ms assignment' nextVarId tbExtra ebExtra
                svTb svEb mergedVal nv1 tbE1 ebE1 hmv hrest

/-- Mirror of `mergeSymEnvKeys_tbExtra_eval_mono`, for `ebExtra`. -/
theorem mergeSymEnvKeys_ebExtra_eval_mono {c : ZKConfig} (gconf : GlobalConfig c)
    (ms : List (FFMacro c)) (assignment' : Assignment c) :
    ∀ (keys : List VarID) (nextVarId : Nat) (tbEnv ebEnv : SymEnv c) (tbExtra ebExtra : FFFormula c)
      (mergedEnv : SymEnv c) (nv' : Nat) (tbE' ebE' : FFFormula c),
      mergeSymEnvKeys nextVarId tbEnv ebEnv tbExtra ebExtra keys
        = Except.ok (mergedEnv, nv', tbE', ebE') →
      evalFormula gconf assignment' ebE' ms = Except.ok true →
      evalFormula gconf assignment' ebExtra ms = Except.ok true := by
  intro keys
  induction keys with
  | nil =>
      intro nextVarId tbEnv ebEnv tbExtra ebExtra mergedEnv nv' tbE' ebE' heq h
      simp only [mergeSymEnvKeys, Except.ok.injEq, Prod.mk.injEq] at heq
      rw [← heq.2.2.2] at h
      exact h
  | cons id rest ih =>
      intro nextVarId tbEnv ebEnv tbExtra ebExtra mergedEnv nv' tbE' ebE' heq h
      cases htb : Corellzk2smt.SymExec.Basic.getVar tbEnv id with
      | error e => simp only [mergeSymEnvKeys, htb] at heq; exact absurd heq (by simp)
      | ok svTb =>
        cases heb : Corellzk2smt.SymExec.Basic.getVar ebEnv id with
        | error e => simp only [mergeSymEnvKeys, htb, heb] at heq; exact absurd heq (by simp)
        | ok svEb =>
          cases hmv : mergeSymValue nextVarId tbExtra ebExtra svTb svEb with
          | error e => simp only [mergeSymEnvKeys, htb, heb, hmv] at heq; exact absurd heq (by simp)
          | ok result =>
            obtain ⟨mergedVal, nv1, tbE1, ebE1⟩ := result
            cases hrec : mergeSymEnvKeys nv1 tbEnv ebEnv tbE1 ebE1 rest with
            | error e =>
                simp only [mergeSymEnvKeys, htb, heb, hmv, hrec] at heq; exact absurd heq (by simp)
            | ok recResult =>
              obtain ⟨restEnv, nv'', tbE'', ebE''⟩ := recResult
              simp only [mergeSymEnvKeys, htb, heb, hmv, hrec, Except.ok.injEq, Prod.mk.injEq]
                at heq
              rw [← heq.2.2.2] at h
              have hrest := ih nv1 tbEnv ebEnv tbE1 ebE1 restEnv nv'' tbE'' ebE'' hrec h
              exact mergeSymValue_ebExtra_eval_mono gconf ms assignment' nextVarId tbExtra ebExtra
                svTb svEb mergedVal nv1 tbE1 ebE1 hmv hrest

/-- Folding `mergeSymValue` down every key of two symbolic environments (as `mergeSymEnvKeys`
    does), extends a matching assignment to one matching the *whole* merged environment,
    without disturbing anything below the starting counter. Every key in `keys` must resolve
    in both `tbEnv` and `ebEnv` with the same shape (guaranteed in practice by the zero-init
    invariant -- every function-local variable is always defined, so both branches of a
    conditional always agree on which variables exist -- together with the language's
    expectation that a variable has the same shape, array or scalar, on both sides of a
    conditional). -/
theorem mergeSymEnvKeys_extend_tb {c : ZKConfig}
    (gconf : GlobalConfig c) (ms : List (FFMacro c)) :
    ∀ (keys : List VarID) (nextVarId : Nat) (tbEnv ebEnv : SymEnv c) (tbExtra ebExtra : FFFormula c)
      (hfresh : varSetBelow (ffVarsOfFormula tbExtra ∪ bVarsOfFormula tbExtra) nextVarId)
      (htbEnvFresh : varSetBelow (symEnvVars tbEnv) nextVarId)
      (hnodup : keys.Nodup)
      (htbDomain : ∀ id ∈ keys, ∃ sv, tbEnv.get? id = some sv)
      (hebDomain : ∀ id ∈ keys, ∃ sv, ebEnv.get? id = some sv)
      (hshape : ∀ id ∈ keys, ∀ svTb svEb, tbEnv.get? id = some svTb → ebEnv.get? id = some svEb →
          sameShape svTb svEb)
      (a : Assignment c)
      (htbExtra : evalFormula gconf a tbExtra ms = Except.ok true)
      (env : Env c)
      (htbMatch : ∀ id ∈ keys, ∀ sv, tbEnv.get? id = some sv →
          ∃ v, env.get? id = some v ∧ symValMatches a sv v),
      ∃ a' mergedEnv nv tbE ebE,
        mergeSymEnvKeys nextVarId tbEnv ebEnv tbExtra ebExtra keys
          = Except.ok (mergedEnv, nv, tbE, ebE) ∧
        nextVarId ≤ nv ∧
        (∀ n, n < nextVarId → a'.ff n = a.ff n) ∧ (∀ n, a'.bool n = a.bool n) ∧
        (∀ n, Var.ffv n ∉ (ffVarsOfFormula tbE ∪ bVarsOfFormula tbE) → a'.ff n = a.ff n) ∧
        (∀ id ∈ keys, ∀ v, env.get? id = some v →
          ∃ sv, mergedEnv.get? id = some sv ∧ symValMatches a' sv v) ∧
        evalFormula gconf a' tbE ms = Except.ok true := by
  intro keys
  induction keys with
  | nil =>
      intro nextVarId tbEnv ebEnv tbExtra ebExtra hfresh htbEnvFresh hnodup
        htbDomain hebDomain hshape a htbExtra env htbMatch
      exact ⟨a, emptySymEnv, nextVarId, tbExtra, ebExtra, rfl, le_refl _, fun _ _ => rfl,
        fun _ => rfl, fun _ _ => rfl, fun id hid => absurd hid (by simp), htbExtra⟩
  | cons id rest ih =>
      intro nextVarId tbEnv ebEnv tbExtra ebExtra hfresh htbEnvFresh hnodup
        htbDomain hebDomain hshape a htbExtra env htbMatch
      obtain ⟨hidNotMemRest, hrestNodup⟩ := List.nodup_cons.mp hnodup
      obtain ⟨svTb0, htb0⟩ := htbDomain id (List.mem_cons_self ..)
      obtain ⟨v0, henv0, hm0⟩ := htbMatch id (List.mem_cons_self ..) svTb0 htb0
      obtain ⟨svEb0, heb0⟩ := hebDomain id (List.mem_cons_self ..)
      have hshape0 : sameShape svTb0 svEb0 := hshape id (List.mem_cons_self ..) svTb0 svEb0 htb0 heb0
      obtain ⟨result, hresult⟩ := mergeSymValue_succeeds_of_sameShape nextVarId tbExtra ebExtra
        svTb0 svEb0 hshape0
      obtain ⟨mergedVal, nv1, tbE1, ebE1⟩ := result
      have hsvTbFresh : varSetBelow (symValVars svTb0) nextVarId :=
        symEnvVars_mem_below tbEnv id svTb0 htb0 nextVarId htbEnvFresh
      obtain ⟨a1, ha1_range, ha1_bool, ha1_frame, ha1_match, ha1_extra⟩ :=
        mergeSymValue_extend_tb gconf ms nextVarId tbExtra ebExtra svTb0 svEb0 mergedVal nv1
          tbE1 ebE1 hresult hfresh hsvTbFresh a v0 hm0 htbExtra
      have hnvMono1 : nextVarId ≤ nv1 :=
        mergeSymValue_mono nextVarId tbExtra ebExtra svTb0 svEb0 mergedVal nv1 tbE1 ebE1 hresult
      have htbE1Fresh : varSetBelow (ffVarsOfFormula tbE1 ∪ bVarsOfFormula tbE1) nv1 :=
        mergeSymValue_tbExtra_fresh nextVarId tbExtra ebExtra svTb0 svEb0 mergedVal nv1 tbE1 ebE1
          hresult hfresh hsvTbFresh
      have htbEnvFresh1 : varSetBelow (symEnvVars tbEnv) nv1 := varSetBelow_mono hnvMono1 htbEnvFresh
      have htbMatch1 : ∀ id' ∈ rest, ∀ sv, tbEnv.get? id' = some sv →
          ∃ v, env.get? id' = some v ∧ symValMatches a1 sv v := by
        intro id' hid' sv' hsv'
        obtain ⟨v', henv', hm'⟩ := htbMatch id' (List.mem_cons_of_mem _ hid') sv' hsv'
        exact ⟨v', henv', symValMatches_extend_preserves a a1 sv' v' nextVarId
          (symEnvVars_mem_below tbEnv id' sv' hsv' nextVarId htbEnvFresh) ha1_range hm'⟩
      obtain ⟨a', mergedEnvRest, nv, tbE, ebE, hfoldRest, hnvMono2, ha'_range, ha'_bool, ha'_frame,
          ha'_match, ha'_extra⟩ :=
        ih nv1 tbEnv ebEnv tbE1 ebE1 htbE1Fresh htbEnvFresh1 hrestNodup
          (fun id' hid' => htbDomain id' (List.mem_cons_of_mem _ hid'))
          (fun id' hid' => hebDomain id' (List.mem_cons_of_mem _ hid'))
          (fun id' hid' => hshape id' (List.mem_cons_of_mem _ hid'))
          a1 ha1_extra env htbMatch1
      refine ⟨a', Corellzk2smt.SymExec.Basic.setVar mergedEnvRest id mergedVal, nv, tbE, ebE, ?_,
        le_trans hnvMono1 hnvMono2,
        fun n hn => (ha'_range n (lt_of_lt_of_le hn hnvMono1)).trans (ha1_range n hn),
        fun n => (ha'_bool n).trans (ha1_bool n), ?_, ?_, ha'_extra⟩
      · show mergeSymEnvKeys nextVarId tbEnv ebEnv tbExtra ebExtra (id :: rest) = _
        simp only [mergeSymEnvKeys, Corellzk2smt.SymExec.Basic.getVar, htb0, heb0, hresult,
          hfoldRest]
      · intro n hn
        have hsubset := mergeSymEnvKeys_tbExtra_subset rest nv1 tbEnv ebEnv tbE1 ebE1
          mergedEnvRest nv tbE ebE hfoldRest
        rw [ha'_frame n hn]
        exact ha1_frame n (fun h => hn (hsubset (Var.ffv n) h))
      · intro id' hid' v hv
        rcases List.mem_cons.mp hid' with heq | hmem
        · have hid'env : env.get? id' = some v0 := by rw [heq]; exact henv0
          rw [hid'env] at hv
          injection hv with hv0eq
          refine ⟨mergedVal, ?_, ?_⟩
          · rw [heq]
            simp only [Corellzk2smt.SymExec.Basic.setVar, Std.TreeMap.get?_eq_getElem?,
              Std.TreeMap.getElem?_insert_self]
          · rw [← hv0eq]
            exact symValMatches_extend_preserves a1 a' mergedVal v0 nv1
              (mergeSymValue_result_fresh nextVarId tbExtra ebExtra svTb0 svEb0 mergedVal nv1
                tbE1 ebE1 hresult hsvTbFresh)
              ha'_range ha1_match
        · obtain ⟨sv, hsv, hm⟩ := ha'_match id' hmem v hv
          refine ⟨sv, ?_, hm⟩
          have hne : id' ≠ id := fun heq => hidNotMemRest (heq ▸ hmem)
          simp only [Corellzk2smt.SymExec.Basic.setVar, Std.TreeMap.get?_eq_getElem?,
            Std.TreeMap.getElem?_insert]
          rw [if_neg (by simp [hne, Ne.symm hne])]
          rw [← Std.TreeMap.get?_eq_getElem?]
          exact hsv

/-- Mirror of `mergeSymEnvKeys_extend_tb`, for the `eb` side. -/
theorem mergeSymEnvKeys_extend_eb {c : ZKConfig}
    (gconf : GlobalConfig c) (ms : List (FFMacro c)) :
    ∀ (keys : List VarID) (nextVarId : Nat) (tbEnv ebEnv : SymEnv c) (tbExtra ebExtra : FFFormula c)
      (hfresh : varSetBelow (ffVarsOfFormula ebExtra ∪ bVarsOfFormula ebExtra) nextVarId)
      (htbEnvFresh : varSetBelow (symEnvVars tbEnv) nextVarId)
      (hebEnvFresh : varSetBelow (symEnvVars ebEnv) nextVarId)
      (hnodup : keys.Nodup)
      (htbDomain : ∀ id ∈ keys, ∃ sv, tbEnv.get? id = some sv)
      (hebDomain : ∀ id ∈ keys, ∃ sv, ebEnv.get? id = some sv)
      (hshape : ∀ id ∈ keys, ∀ svTb svEb, tbEnv.get? id = some svTb → ebEnv.get? id = some svEb →
          sameShape svTb svEb)
      (a : Assignment c)
      (hebExtra : evalFormula gconf a ebExtra ms = Except.ok true)
      (env : Env c)
      (hebMatch : ∀ id ∈ keys, ∀ sv, ebEnv.get? id = some sv →
          ∃ v, env.get? id = some v ∧ symValMatches a sv v),
      ∃ a' mergedEnv nv tbE ebE,
        mergeSymEnvKeys nextVarId tbEnv ebEnv tbExtra ebExtra keys
          = Except.ok (mergedEnv, nv, tbE, ebE) ∧
        nextVarId ≤ nv ∧
        (∀ n, n < nextVarId → a'.ff n = a.ff n) ∧ (∀ n, a'.bool n = a.bool n) ∧
        (∀ n, Var.ffv n ∉ (ffVarsOfFormula ebE ∪ bVarsOfFormula ebE) → a'.ff n = a.ff n) ∧
        (∀ id ∈ keys, ∀ v, env.get? id = some v →
          ∃ sv, mergedEnv.get? id = some sv ∧ symValMatches a' sv v) ∧
        evalFormula gconf a' ebE ms = Except.ok true := by
  intro keys
  induction keys with
  | nil =>
      intro nextVarId tbEnv ebEnv tbExtra ebExtra hfresh htbEnvFresh hebEnvFresh hnodup
        htbDomain hebDomain hshape a hebExtra env hebMatch
      exact ⟨a, emptySymEnv, nextVarId, tbExtra, ebExtra, rfl, le_refl _, fun _ _ => rfl,
        fun _ => rfl, fun _ _ => rfl, fun id hid => absurd hid (by simp), hebExtra⟩
  | cons id rest ih =>
      intro nextVarId tbEnv ebEnv tbExtra ebExtra hfresh htbEnvFresh hebEnvFresh hnodup
        htbDomain hebDomain hshape a hebExtra env hebMatch
      obtain ⟨hidNotMemRest, hrestNodup⟩ := List.nodup_cons.mp hnodup
      obtain ⟨svTb0, htb0⟩ := htbDomain id (List.mem_cons_self ..)
      obtain ⟨svEb0, heb0⟩ := hebDomain id (List.mem_cons_self ..)
      obtain ⟨v0, henv0, hm0⟩ := hebMatch id (List.mem_cons_self ..) svEb0 heb0
      have hshape0 : sameShape svTb0 svEb0 := hshape id (List.mem_cons_self ..) svTb0 svEb0 htb0 heb0
      obtain ⟨result, hresult⟩ := mergeSymValue_succeeds_of_sameShape nextVarId tbExtra ebExtra
        svTb0 svEb0 hshape0
      obtain ⟨mergedVal, nv1, tbE1, ebE1⟩ := result
      have hsvTbFresh : varSetBelow (symValVars svTb0) nextVarId :=
        symEnvVars_mem_below tbEnv id svTb0 htb0 nextVarId htbEnvFresh
      have hsvEbFresh : varSetBelow (symValVars svEb0) nextVarId :=
        symEnvVars_mem_below ebEnv id svEb0 heb0 nextVarId hebEnvFresh
      obtain ⟨a1, ha1_range, ha1_bool, ha1_frame, ha1_match, ha1_extra⟩ :=
        mergeSymValue_extend_eb gconf ms nextVarId tbExtra ebExtra svTb0 svEb0 mergedVal nv1
          tbE1 ebE1 hresult hfresh hsvTbFresh hsvEbFresh a v0 hm0 hebExtra
      have hnvMono1 : nextVarId ≤ nv1 :=
        mergeSymValue_mono nextVarId tbExtra ebExtra svTb0 svEb0 mergedVal nv1 tbE1 ebE1 hresult
      have hebE1Fresh : varSetBelow (ffVarsOfFormula ebE1 ∪ bVarsOfFormula ebE1) nv1 :=
        mergeSymValue_ebExtra_fresh nextVarId tbExtra ebExtra svTb0 svEb0 mergedVal nv1 tbE1 ebE1
          hresult hfresh hsvEbFresh
      have htbEnvFresh1 : varSetBelow (symEnvVars tbEnv) nv1 := varSetBelow_mono hnvMono1 htbEnvFresh
      have hebEnvFresh1 : varSetBelow (symEnvVars ebEnv) nv1 := varSetBelow_mono hnvMono1 hebEnvFresh
      have hebMatch1 : ∀ id' ∈ rest, ∀ sv, ebEnv.get? id' = some sv →
          ∃ v, env.get? id' = some v ∧ symValMatches a1 sv v := by
        intro id' hid' sv' hsv'
        obtain ⟨v', henv', hm'⟩ := hebMatch id' (List.mem_cons_of_mem _ hid') sv' hsv'
        exact ⟨v', henv', symValMatches_extend_preserves a a1 sv' v' nextVarId
          (symEnvVars_mem_below ebEnv id' sv' hsv' nextVarId hebEnvFresh) ha1_range hm'⟩
      obtain ⟨a', mergedEnvRest, nv, tbE, ebE, hfoldRest, hnvMono2, ha'_range, ha'_bool, ha'_frame,
          ha'_match, ha'_extra⟩ :=
        ih nv1 tbEnv ebEnv tbE1 ebE1 hebE1Fresh htbEnvFresh1 hebEnvFresh1 hrestNodup
          (fun id' hid' => htbDomain id' (List.mem_cons_of_mem _ hid'))
          (fun id' hid' => hebDomain id' (List.mem_cons_of_mem _ hid'))
          (fun id' hid' => hshape id' (List.mem_cons_of_mem _ hid'))
          a1 ha1_extra env hebMatch1
      refine ⟨a', Corellzk2smt.SymExec.Basic.setVar mergedEnvRest id mergedVal, nv, tbE, ebE, ?_,
        le_trans hnvMono1 hnvMono2,
        fun n hn => (ha'_range n (lt_of_lt_of_le hn hnvMono1)).trans (ha1_range n hn),
        fun n => (ha'_bool n).trans (ha1_bool n), ?_, ?_, ha'_extra⟩
      · show mergeSymEnvKeys nextVarId tbEnv ebEnv tbExtra ebExtra (id :: rest) = _
        simp only [mergeSymEnvKeys, Corellzk2smt.SymExec.Basic.getVar, htb0, heb0, hresult,
          hfoldRest]
      · intro n hn
        have hsubset := mergeSymEnvKeys_ebExtra_subset rest nv1 tbEnv ebEnv tbE1 ebE1
          mergedEnvRest nv tbE ebE hfoldRest
        rw [ha'_frame n hn]
        exact ha1_frame n (fun h => hn (hsubset (Var.ffv n) h))
      · intro id' hid' v hv
        rcases List.mem_cons.mp hid' with heq | hmem
        · have hid'env : env.get? id' = some v0 := by rw [heq]; exact henv0
          rw [hid'env] at hv
          injection hv with hv0eq
          refine ⟨mergedVal, ?_, ?_⟩
          · rw [heq]
            simp only [Corellzk2smt.SymExec.Basic.setVar, Std.TreeMap.get?_eq_getElem?,
              Std.TreeMap.getElem?_insert_self]
          · rw [← hv0eq]
            exact symValMatches_extend_preserves a1 a' mergedVal v0 nv1
              (mergeSymValue_result_fresh nextVarId tbExtra ebExtra svTb0 svEb0 mergedVal nv1
                tbE1 ebE1 hresult hsvTbFresh)
              ha'_range ha1_match
        · obtain ⟨sv, hsv, hm⟩ := ha'_match id' hmem v hv
          refine ⟨sv, ?_, hm⟩
          have hne : id' ≠ id := fun heq => hidNotMemRest (heq ▸ hmem)
          simp only [Corellzk2smt.SymExec.Basic.setVar, Std.TreeMap.get?_eq_getElem?,
            Std.TreeMap.getElem?_insert]
          rw [if_neg (by simp [hne, Ne.symm hne])]
          rw [← Std.TreeMap.get?_eq_getElem?]
          exact hsv

/-- **Completeness** half of `mergeSymEnvKeys`, `tb` side: if a fixed assignment already
    matches, for every key, the concrete env's value against `tbEnv`'s own symbolic value, and
    also satisfies the *final* accumulated `tbExtra`, then it matches the concrete env against
    the *merged* symbolic value too. Mirrors `mergeSymEnvKeys_extend_tb`, but -- since nothing
    needs to be constructed, `assignment'` is already fixed throughout -- doesn't need
    `hebDomain`/`hshape`/`hnodup` at all: `hfold`'s bare success already guarantees
    `mergeSymValue` succeeded at every key. -/
theorem mergeSymEnvKeys_match_of_tb {c : ZKConfig} (gconf : GlobalConfig c) (ms : List (FFMacro c))
    (assignment' : Assignment c) :
    ∀ (keys : List VarID) (nextVarId : Nat) (tbEnv ebEnv : SymEnv c) (tbExtra ebExtra : FFFormula c)
      (mergedEnv : SymEnv c) (nv' : Nat) (tbE' ebE' : FFFormula c),
      mergeSymEnvKeys nextVarId tbEnv ebEnv tbExtra ebExtra keys
        = Except.ok (mergedEnv, nv', tbE', ebE') →
      ∀ (env : Env c),
      (∀ id ∈ keys, ∀ sv, tbEnv.get? id = some sv →
          ∃ v, env.get? id = some v ∧ symValMatches assignment' sv v) →
      evalFormula gconf assignment' tbE' ms = Except.ok true →
      ∀ id ∈ keys, ∀ v, env.get? id = some v →
        ∃ sv, mergedEnv.get? id = some sv ∧ symValMatches assignment' sv v := by
  intro keys
  induction keys with
  | nil =>
      intro nextVarId tbEnv ebEnv tbExtra ebExtra mergedEnv nv' tbE' ebE' heq env htbMatch htbE'
        id hid
      cases hid
  | cons id0 rest ih =>
      intro nextVarId tbEnv ebEnv tbExtra ebExtra mergedEnv nv' tbE' ebE' heq env htbMatch htbE'
      cases htb : Corellzk2smt.SymExec.Basic.getVar tbEnv id0 with
      | error e => simp only [mergeSymEnvKeys, htb] at heq; exact absurd heq (by simp)
      | ok svTb =>
        cases heb : Corellzk2smt.SymExec.Basic.getVar ebEnv id0 with
        | error e => simp only [mergeSymEnvKeys, htb, heb] at heq; exact absurd heq (by simp)
        | ok svEb =>
          cases hmv : mergeSymValue nextVarId tbExtra ebExtra svTb svEb with
          | error e => simp only [mergeSymEnvKeys, htb, heb, hmv] at heq; exact absurd heq (by simp)
          | ok result =>
            obtain ⟨mergedVal, nv1, tbE1, ebE1⟩ := result
            cases hrec : mergeSymEnvKeys nv1 tbEnv ebEnv tbE1 ebE1 rest with
            | error e =>
                simp only [mergeSymEnvKeys, htb, heb, hmv, hrec] at heq; exact absurd heq (by simp)
            | ok recResult =>
              obtain ⟨restEnv, nv'', tbE'', ebE''⟩ := recResult
              simp only [mergeSymEnvKeys, htb, heb, hmv, hrec, Except.ok.injEq, Prod.mk.injEq]
                at heq
              have htb_get : tbEnv.get? id0 = some svTb := (getVar_eq_ok_iff tbEnv id0 svTb).mp htb
              rw [← heq.2.2.1] at htbE'
              have htbE1 : evalFormula gconf assignment' tbE1 ms = Except.ok true :=
                mergeSymEnvKeys_tbExtra_eval_mono gconf ms assignment' rest nv1 tbEnv ebEnv tbE1
                  ebE1 restEnv nv'' tbE'' ebE'' hrec htbE'
              have hmerged_v0 : ∀ v, env.get? id0 = some v →
                  ∃ sv, mergedVal = sv ∧ symValMatches assignment' sv v := by
                intro v hv
                obtain ⟨v', hv', hm'⟩ := htbMatch id0 (List.mem_cons_self ..) svTb htb_get
                rw [hv] at hv'
                injection hv' with hveq
                subst hveq
                exact ⟨mergedVal, rfl,
                  mergeSymValue_match_of_tb gconf ms assignment' nextVarId tbExtra ebExtra svTb
                    svEb mergedVal nv1 tbE1 ebE1 hmv v hm' htbE1⟩
              have htbMatch1 : ∀ id ∈ rest, ∀ sv, tbEnv.get? id = some sv →
                  ∃ v, env.get? id = some v ∧ symValMatches assignment' sv v :=
                fun id hid => htbMatch id (List.mem_cons_of_mem _ hid)
              have hrest := ih nv1 tbEnv ebEnv tbE1 ebE1 restEnv nv'' tbE'' ebE'' hrec env
                htbMatch1 htbE'
              intro id hid v hv
              rw [← heq.1]
              by_cases hideq : id = id0
              · subst hideq
                obtain ⟨sv, hsveq, hsm⟩ := hmerged_v0 v hv
                refine ⟨sv, ?_, hsm⟩
                rw [← hsveq]
                simp only [Corellzk2smt.SymExec.Basic.setVar, Std.TreeMap.get?_eq_getElem?,
                  Std.TreeMap.getElem?_insert_self]
              · rcases List.mem_cons.mp hid with heqid | hmem
                · exact absurd heqid hideq
                · obtain ⟨sv, hsv, hsm⟩ := hrest id hmem v hv
                  refine ⟨sv, ?_, hsm⟩
                  simp only [Corellzk2smt.SymExec.Basic.setVar, Std.TreeMap.get?_eq_getElem?,
                    Std.TreeMap.getElem?_insert]
                  rw [if_neg (by simp [hideq, Ne.symm hideq])]
                  rwa [← Std.TreeMap.get?_eq_getElem?]

/-- Mirror of `mergeSymEnvKeys_match_of_tb`, for the `eb` side. -/
theorem mergeSymEnvKeys_match_of_eb {c : ZKConfig} (gconf : GlobalConfig c) (ms : List (FFMacro c))
    (assignment' : Assignment c) :
    ∀ (keys : List VarID) (nextVarId : Nat) (tbEnv ebEnv : SymEnv c) (tbExtra ebExtra : FFFormula c)
      (mergedEnv : SymEnv c) (nv' : Nat) (tbE' ebE' : FFFormula c),
      mergeSymEnvKeys nextVarId tbEnv ebEnv tbExtra ebExtra keys
        = Except.ok (mergedEnv, nv', tbE', ebE') →
      ∀ (env : Env c),
      (∀ id ∈ keys, ∀ sv, ebEnv.get? id = some sv →
          ∃ v, env.get? id = some v ∧ symValMatches assignment' sv v) →
      evalFormula gconf assignment' ebE' ms = Except.ok true →
      ∀ id ∈ keys, ∀ v, env.get? id = some v →
        ∃ sv, mergedEnv.get? id = some sv ∧ symValMatches assignment' sv v := by
  intro keys
  induction keys with
  | nil =>
      intro nextVarId tbEnv ebEnv tbExtra ebExtra mergedEnv nv' tbE' ebE' heq env hebMatch hebE'
        id hid
      cases hid
  | cons id0 rest ih =>
      intro nextVarId tbEnv ebEnv tbExtra ebExtra mergedEnv nv' tbE' ebE' heq env hebMatch hebE'
      cases htb : Corellzk2smt.SymExec.Basic.getVar tbEnv id0 with
      | error e => simp only [mergeSymEnvKeys, htb] at heq; exact absurd heq (by simp)
      | ok svTb =>
        cases heb : Corellzk2smt.SymExec.Basic.getVar ebEnv id0 with
        | error e => simp only [mergeSymEnvKeys, htb, heb] at heq; exact absurd heq (by simp)
        | ok svEb =>
          cases hmv : mergeSymValue nextVarId tbExtra ebExtra svTb svEb with
          | error e => simp only [mergeSymEnvKeys, htb, heb, hmv] at heq; exact absurd heq (by simp)
          | ok result =>
            obtain ⟨mergedVal, nv1, tbE1, ebE1⟩ := result
            cases hrec : mergeSymEnvKeys nv1 tbEnv ebEnv tbE1 ebE1 rest with
            | error e =>
                simp only [mergeSymEnvKeys, htb, heb, hmv, hrec] at heq; exact absurd heq (by simp)
            | ok recResult =>
              obtain ⟨restEnv, nv'', tbE'', ebE''⟩ := recResult
              simp only [mergeSymEnvKeys, htb, heb, hmv, hrec, Except.ok.injEq, Prod.mk.injEq]
                at heq
              have heb_get : ebEnv.get? id0 = some svEb := (getVar_eq_ok_iff ebEnv id0 svEb).mp heb
              rw [← heq.2.2.2] at hebE'
              have hebE1 : evalFormula gconf assignment' ebE1 ms = Except.ok true :=
                mergeSymEnvKeys_ebExtra_eval_mono gconf ms assignment' rest nv1 tbEnv ebEnv tbE1
                  ebE1 restEnv nv'' tbE'' ebE'' hrec hebE'
              have hmerged_v0 : ∀ v, env.get? id0 = some v →
                  ∃ sv, mergedVal = sv ∧ symValMatches assignment' sv v := by
                intro v hv
                obtain ⟨v', hv', hm'⟩ := hebMatch id0 (List.mem_cons_self ..) svEb heb_get
                rw [hv] at hv'
                injection hv' with hveq
                subst hveq
                exact ⟨mergedVal, rfl,
                  mergeSymValue_match_of_eb gconf ms assignment' nextVarId tbExtra ebExtra svTb
                    svEb mergedVal nv1 tbE1 ebE1 hmv v hm' hebE1⟩
              have hebMatch1 : ∀ id ∈ rest, ∀ sv, ebEnv.get? id = some sv →
                  ∃ v, env.get? id = some v ∧ symValMatches assignment' sv v :=
                fun id hid => hebMatch id (List.mem_cons_of_mem _ hid)
              have hrest := ih nv1 tbEnv ebEnv tbE1 ebE1 restEnv nv'' tbE'' ebE'' hrec env
                hebMatch1 hebE'
              intro id hid v hv
              rw [← heq.1]
              by_cases hideq : id = id0
              · subst hideq
                obtain ⟨sv, hsveq, hsm⟩ := hmerged_v0 v hv
                refine ⟨sv, ?_, hsm⟩
                rw [← hsveq]
                simp only [Corellzk2smt.SymExec.Basic.setVar, Std.TreeMap.get?_eq_getElem?,
                  Std.TreeMap.getElem?_insert_self]
              · rcases List.mem_cons.mp hid with heqid | hmem
                · exact absurd heqid hideq
                · obtain ⟨sv, hsv, hsm⟩ := hrest id hmem v hv
                  refine ⟨sv, ?_, hsm⟩
                  simp only [Corellzk2smt.SymExec.Basic.setVar, Std.TreeMap.get?_eq_getElem?,
                    Std.TreeMap.getElem?_insert]
                  rw [if_neg (by simp [hideq, Ne.symm hideq])]
                  rwa [← Std.TreeMap.get?_eq_getElem?]

-- ---------------------------------------------------------------------------
-- `mergeSymEnv`: thin wrappers around `mergeSymEnvKeys_extend_tb`/`_eb`
-- ---------------------------------------------------------------------------

/-- Bridges `Std.TreeMap.keys` membership to `get?` returning `some` -- the domain
    membership fact needed to instantiate `mergeSymEnvKeys_extend_tb`/`_eb`'s key-list
    hypotheses (`htbDomain`/`hebDomain`/`hnodup`) from a plain `SymEnv`. -/
theorem mem_keys_iff_get?_isSome {β : Type} (env : Std.TreeMap VarID β) (id : VarID) :
    id ∈ env.keys ↔ ∃ sv, env.get? id = some sv := by
  rw [Std.TreeMap.mem_keys, Std.TreeMap.mem_iff_isSome_getElem?, Std.TreeMap.get?_eq_getElem?]
  exact Option.isSome_iff_exists

/-- Bridges `.contains` to `get?` returning `some`. -/
theorem contains_iff_get?_isSome {β : Type} (env : Std.TreeMap VarID β) (id : VarID) :
    env.contains id ↔ ∃ sv, env.get? id = some sv := by
  rw [show env.contains id ↔ id ∈ env from Iff.rfl, ← Std.TreeMap.mem_keys]
  exact mem_keys_iff_get?_isSome env id

/-- Bridges `Semantics.Basic.getVar`'s success to `Std.TreeMap.get?` returning `some` --
    the concrete-`Env` mirror of `getVar_eq_ok_iff`. -/
theorem getVarEnv_eq_ok_iff {c : ZKConfig} (env : Env c) (id : VarID) (v : Value c) :
    Corellzk2smt.Language.Core.Semantics.Basic.getVar env id = Except.ok v ↔
      env.get? id = some v := by
  simp only [Corellzk2smt.Language.Core.Semantics.Basic.getVar]
  cases env.get? id with
  | none => simp
  | some v' => simp

/-- Pure (assignment-free): `mergeSymEnv` never lowers the variable counter. -/
theorem mergeSymEnv_mono {c : ZKConfig} (nextVarId : Nat) (tbEnv ebEnv : SymEnv c)
    (mergedEnv : SymEnv c) (nv' : Nat) (tbE' ebE' : FFFormula c)
    (heq : mergeSymEnv nextVarId tbEnv ebEnv = Except.ok (mergedEnv, nv', tbE', ebE')) :
    nextVarId ≤ nv' :=
  mergeSymEnvKeys_mono tbEnv.keys nextVarId tbEnv ebEnv FFFormula.true FFFormula.true
    mergedEnv nv' tbE' ebE' heq

/-- Pure (assignment-free): the `tbE'` `mergeSymEnv` produces is fresh below the new counter. -/
theorem mergeSymEnv_tbExtra_fresh {c : ZKConfig} (nextVarId : Nat) (tbEnv ebEnv : SymEnv c)
    (htbEnvFresh : varSetBelow (symEnvVars tbEnv) nextVarId)
    (mergedEnv : SymEnv c) (nv' : Nat) (tbE' ebE' : FFFormula c)
    (heq : mergeSymEnv nextVarId tbEnv ebEnv = Except.ok (mergedEnv, nv', tbE', ebE')) :
    varSetBelow (ffVarsOfFormula tbE' ∪ bVarsOfFormula tbE') nv' :=
  mergeSymEnvKeys_tbExtra_fresh tbEnv.keys nextVarId tbEnv ebEnv FFFormula.true FFFormula.true
    mergedEnv nv' tbE' ebE' heq
    (by intro v hv
        simp only [ffVarsOfFormula, bVarsOfFormula] at hv
        rcases Std.TreeSet.mem_union_iff.mp hv with h | h <;>
          exact absurd h Std.TreeSet.not_mem_emptyc)
    htbEnvFresh

/-- Mirror of `mergeSymEnv_tbExtra_fresh`, for `ebExtra`. -/
theorem mergeSymEnv_ebExtra_fresh {c : ZKConfig} (nextVarId : Nat) (tbEnv ebEnv : SymEnv c)
    (hebEnvFresh : varSetBelow (symEnvVars ebEnv) nextVarId)
    (mergedEnv : SymEnv c) (nv' : Nat) (tbE' ebE' : FFFormula c)
    (heq : mergeSymEnv nextVarId tbEnv ebEnv = Except.ok (mergedEnv, nv', tbE', ebE')) :
    varSetBelow (ffVarsOfFormula ebE' ∪ bVarsOfFormula ebE') nv' :=
  mergeSymEnvKeys_ebExtra_fresh tbEnv.keys nextVarId tbEnv ebEnv FFFormula.true FFFormula.true
    mergedEnv nv' tbE' ebE' heq
    (by intro v hv
        simp only [ffVarsOfFormula, bVarsOfFormula] at hv
        rcases Std.TreeSet.mem_union_iff.mp hv with h | h <;>
          exact absurd h Std.TreeSet.not_mem_emptyc)
    hebEnvFresh

/-- Subset-or-fresh analog of `mergeSymEnv_tbExtra_fresh`: every var the merged `tbE'`
    mentions is either one somewhere in `tbEnv`, or genuinely new relative to the counter the
    merge started from. -/
theorem mergeSymEnv_tbExtra_merged_subset {c : ZKConfig} (nextVarId : Nat) (tbEnv ebEnv : SymEnv c)
    (mergedEnv : SymEnv c) (nv' : Nat) (tbE' ebE' : FFFormula c)
    (heq : mergeSymEnv nextVarId tbEnv ebEnv = Except.ok (mergedEnv, nv', tbE', ebE')) :
    ∀ v ∈ (ffVarsOfFormula tbE' ∪ bVarsOfFormula tbE'),
      v ∈ symEnvVars tbEnv ∨ nextVarId ≤ varIndex v :=
  mergeSymEnvKeys_tbExtra_merged_subset nextVarId tbEnv.keys nextVarId tbEnv ebEnv FFFormula.true
    FFFormula.true mergedEnv nv' tbE' ebE' heq (le_refl _)
    (by intro v hv
        simp only [ffVarsOfFormula, bVarsOfFormula] at hv
        rcases Std.TreeSet.mem_union_iff.mp hv with h | h <;>
          exact absurd h Std.TreeSet.not_mem_emptyc)

/-- Mirror of `mergeSymEnv_tbExtra_merged_subset`, for `ebExtra`. -/
theorem mergeSymEnv_ebExtra_merged_subset {c : ZKConfig} (nextVarId : Nat) (tbEnv ebEnv : SymEnv c)
    (mergedEnv : SymEnv c) (nv' : Nat) (tbE' ebE' : FFFormula c)
    (heq : mergeSymEnv nextVarId tbEnv ebEnv = Except.ok (mergedEnv, nv', tbE', ebE')) :
    ∀ v ∈ (ffVarsOfFormula ebE' ∪ bVarsOfFormula ebE'),
      v ∈ symEnvVars ebEnv ∨ nextVarId ≤ varIndex v :=
  mergeSymEnvKeys_ebExtra_merged_subset nextVarId tbEnv.keys nextVarId tbEnv ebEnv FFFormula.true
    FFFormula.true mergedEnv nv' tbE' ebE' heq (le_refl _)
    (by intro v hv
        simp only [ffVarsOfFormula, bVarsOfFormula] at hv
        rcases Std.TreeSet.mem_union_iff.mp hv with h | h <;>
          exact absurd h Std.TreeSet.not_mem_emptyc)

/-- `mergeSymEnv`'s output has exactly `tbEnv`'s domain. -/
theorem mergeSymEnv_domain {c : ZKConfig} (nextVarId : Nat) (tbEnv ebEnv : SymEnv c)
    (mergedEnv : SymEnv c) (nv' : Nat) (tbE' ebE' : FFFormula c)
    (heq : mergeSymEnv nextVarId tbEnv ebEnv = Except.ok (mergedEnv, nv', tbE', ebE')) (id : VarID) :
    mergedEnv.contains id ↔ tbEnv.contains id := by
  rw [mergeSymEnvKeys_domain tbEnv.keys nextVarId tbEnv ebEnv FFFormula.true FFFormula.true
    mergedEnv nv' tbE' ebE' heq id, Std.TreeMap.mem_keys]
  rfl

/-- Every value `mergeSymEnv` binds a key to is fresh below the new counter. -/
theorem mergeSymEnv_result_fresh {c : ZKConfig} (nextVarId : Nat) (tbEnv ebEnv : SymEnv c)
    (htbEnvFresh : varSetBelow (symEnvVars tbEnv) nextVarId)
    (mergedEnv : SymEnv c) (nv' : Nat) (tbE' ebE' : FFFormula c)
    (heq : mergeSymEnv nextVarId tbEnv ebEnv = Except.ok (mergedEnv, nv', tbE', ebE'))
    (id : VarID) (sv : SymValue c) (hsv : mergedEnv.get? id = some sv) :
    varSetBelow (symValVars sv) nv' :=
  mergeSymEnvKeys_result_fresh tbEnv.keys nextVarId tbEnv ebEnv FFFormula.true FFFormula.true
    mergedEnv nv' tbE' ebE' heq htbEnvFresh id sv hsv

/-- `symEnvVars` of `mergeSymEnv`'s merged output is fresh below the new counter --
    the whole-environment lift of `mergeSymEnv_result_fresh` via `symEnvVars`'s own
    fold-based definition. -/
theorem mergeSymEnv_out_fresh {c : ZKConfig} (nextVarId : Nat) (tbEnv ebEnv : SymEnv c)
    (htbEnvFresh : varSetBelow (symEnvVars tbEnv) nextVarId)
    (mergedEnv : SymEnv c) (nv' : Nat) (tbE' ebE' : FFFormula c)
    (heq : mergeSymEnv nextVarId tbEnv ebEnv = Except.ok (mergedEnv, nv', tbE', ebE')) :
    varSetBelow (symEnvVars mergedEnv) nv' := by
  simp only [symEnvVars]
  rw [Std.TreeMap.foldl_eq_foldl_toList]
  apply varSetBelow_foldl_union (fun p => symValVars p.2) mergedEnv.toList nv' emptyVarSet
    (fun v hv => absurd hv Std.TreeSet.not_mem_emptyc)
  intro ab hab
  have hget : mergedEnv.get? ab.1 = some ab.2 := by
    rw [Std.TreeMap.get?_eq_getElem?]
    exact Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hab
  exact mergeSymEnv_result_fresh nextVarId tbEnv ebEnv htbEnvFresh mergedEnv nv' tbE' ebE'
    heq ab.1 ab.2 hget

/-- Subset-or-fresh analog of `mergeSymEnv_result_fresh`. -/
theorem mergeSymEnv_merged_subset {c : ZKConfig} (nextVarId : Nat) (tbEnv ebEnv : SymEnv c)
    (mergedEnv : SymEnv c) (nv' : Nat) (tbE' ebE' : FFFormula c)
    (heq : mergeSymEnv nextVarId tbEnv ebEnv = Except.ok (mergedEnv, nv', tbE', ebE'))
    (id : VarID) (sv : SymValue c) (hsv : mergedEnv.get? id = some sv) :
    ∀ v ∈ symValVars sv, v ∈ symEnvVars tbEnv ∨ nextVarId ≤ varIndex v :=
  mergeSymEnvKeys_merged_subset tbEnv.keys nextVarId tbEnv ebEnv FFFormula.true FFFormula.true
    mergedEnv nv' tbE' ebE' heq id sv hsv

/-- `symEnvVars` of `mergeSymEnv`'s merged output is either one of `tbEnv`'s own vars, or
    genuinely new relative to the counter the merge started from -- the whole-environment
    lift of `mergeSymEnv_merged_subset` via `symEnvVars`'s own fold-based definition. -/
theorem mergeSymEnv_out_subset {c : ZKConfig} (nextVarId : Nat) (tbEnv ebEnv : SymEnv c)
    (mergedEnv : SymEnv c) (nv' : Nat) (tbE' ebE' : FFFormula c)
    (heq : mergeSymEnv nextVarId tbEnv ebEnv = Except.ok (mergedEnv, nv', tbE', ebE')) :
    ∀ v ∈ symEnvVars mergedEnv, v ∈ symEnvVars tbEnv ∨ nextVarId ≤ varIndex v := by
  simp only [symEnvVars]
  rw [Std.TreeMap.foldl_eq_foldl_toList]
  apply foldl_union_subset_or_bound (fun p => symValVars p.2) (symEnvVars tbEnv) mergedEnv.toList
    nextVarId emptyVarSet (fun v hv => absurd hv Std.TreeSet.not_mem_emptyc)
  intro ab hab
  have hget : mergedEnv.get? ab.1 = some ab.2 := by
    rw [Std.TreeMap.get?_eq_getElem?]
    exact Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hab
  exact mergeSymEnv_merged_subset nextVarId tbEnv ebEnv mergedEnv nv' tbE' ebE' heq ab.1 ab.2 hget

/-- Packages the domain + pointwise reasoning needed to lift `EnvMatches` from one branch's
    `outSymEnv` (`sideEnv`) to the merged environment: since `mergedEnv` and `sideEnv` share a
    domain (`hdomeq`), any symbolic value `mergedEnv` reports for `id` is also what `sideEnv`
    reports (same `get?`, by `mergedEnv.get?`/`sideEnv.get?` both being deterministic functions
    of `id`), so the side's own match fact (`hside_match`) and the merge's match fact
    (`ha'_match`) compose into a match fact for the merged environment directly. -/
theorem mergedEnv_matches_of_side {c : ZKConfig}
    (sideEnv mergedEnv : SymEnv c)
    (hdomeq : ∀ id, mergedEnv.contains id ↔ sideEnv.contains id)
    (assignment1 a' : Assignment c) (env' : Env c)
    (hside_match : ∀ id sv, sideEnv.get? id = some sv →
        ∃ v, env'.get? id = some v ∧ symValMatches assignment1 sv v)
    (ha'_match : ∀ id sv, sideEnv.get? id = some sv → ∀ v, env'.get? id = some v →
        ∃ sv', mergedEnv.get? id = some sv' ∧ symValMatches a' sv' v)
    (id : VarID) (sv : SymValue c) (hsv : mergedEnv.get? id = some sv) :
    ∃ v, env'.get? id = some v ∧ symValMatches a' sv v := by
  have hcont : mergedEnv.contains id := (contains_iff_get?_isSome mergedEnv id).mpr ⟨sv, hsv⟩
  obtain ⟨svSide, hsvSide⟩ := (contains_iff_get?_isSome sideEnv id).mp ((hdomeq id).mp hcont)
  obtain ⟨v, henv'v, _⟩ := hside_match id svSide hsvSide
  obtain ⟨sv', hsv', hmatch'⟩ := ha'_match id svSide hsvSide v henv'v
  rw [hsv] at hsv'
  injection hsv' with hsveq
  exact ⟨v, henv'v, hsveq ▸ hmatch'⟩

/-- **Soundness (`tb` side)** of `mergeSymEnv`: mirrors `mergeSymEnvKeys_extend_tb`, but
    stated directly over the two `SymEnv`s (with `mergeSymEnv`'s own key list, `tbEnv.keys`,
    and starting extras `FFFormula.true`) rather than over an explicit key list -- this is
    the form `mergeIfBranches_sound` actually needs. `hdom` records that `tbEnv`/`ebEnv` agree
    on domain (guaranteed in practice by zero-initializing every function-local variable at
    entry, see `zeroInitEnv`, so an if-statement's two branches never disagree on which
    variables exist). -/
theorem mergeSymEnv_extend_tb {c : ZKConfig}
    (gconf : GlobalConfig c) (ms : List (FFMacro c))
    (nextVarId : Nat) (tbEnv ebEnv : SymEnv c)
    (htbEnvFresh : varSetBelow (symEnvVars tbEnv) nextVarId)
    (hdom : ∀ id, (∃ sv, tbEnv.get? id = some sv) ↔ (∃ sv, ebEnv.get? id = some sv))
    (hshape : ∀ id svTb svEb, tbEnv.get? id = some svTb → ebEnv.get? id = some svEb →
        sameShape svTb svEb)
    (a : Assignment c)
    (env : Env c)
    (htbMatch : ∀ id sv, tbEnv.get? id = some sv →
        ∃ v, env.get? id = some v ∧ symValMatches a sv v) :
    ∃ a' mergedEnv nv tbE ebE,
      mergeSymEnv nextVarId tbEnv ebEnv = Except.ok (mergedEnv, nv, tbE, ebE) ∧
      nextVarId ≤ nv ∧
      (∀ n, n < nextVarId → a'.ff n = a.ff n) ∧ (∀ n, a'.bool n = a.bool n) ∧
      (∀ n, Var.ffv n ∉ (ffVarsOfFormula tbE ∪ bVarsOfFormula tbE) → a'.ff n = a.ff n) ∧
      (∀ id sv, tbEnv.get? id = some sv → ∀ v, env.get? id = some v →
        ∃ sv', mergedEnv.get? id = some sv' ∧ symValMatches a' sv' v) ∧
      evalFormula gconf a' tbE ms = Except.ok true := by
  obtain ⟨a', mergedEnv, nv, tbE, ebE, hcall, hnvMono, ha'_range, ha'_bool, ha'_frame, ha'_match,
      ha'_extra⟩ :=
    mergeSymEnvKeys_extend_tb gconf ms tbEnv.keys nextVarId tbEnv ebEnv FFFormula.true
      FFFormula.true
      (by intro v hv
          simp only [ffVarsOfFormula, bVarsOfFormula] at hv
          rcases Std.TreeSet.mem_union_iff.mp hv with h | h <;>
            exact absurd h Std.TreeSet.not_mem_emptyc)
      htbEnvFresh (Std.TreeMap.nodup_keys)
      (fun id hid => (mem_keys_iff_get?_isSome tbEnv id).mp hid)
      (fun id hid => hdom id |>.mp ((mem_keys_iff_get?_isSome tbEnv id).mp hid))
      (fun id _ svTb svEb htb heb => hshape id svTb svEb htb heb)
      a (by simp only [evalFormula]) env
      (fun id hid sv hsv => htbMatch id sv hsv)
  refine ⟨a', mergedEnv, nv, tbE, ebE, ?_, hnvMono, ha'_range, ha'_bool, ha'_frame, ?_, ha'_extra⟩
  · show mergeSymEnv nextVarId tbEnv ebEnv = _
    simp only [mergeSymEnv, hcall]
  · intro id sv hsv v hv
    exact ha'_match id ((mem_keys_iff_get?_isSome tbEnv id).mpr ⟨sv, hsv⟩) v hv

/-- **Soundness (`eb` side)** of `mergeSymEnv`: the `eb`-side mirror of
    `mergeSymEnv_extend_tb`. -/
theorem mergeSymEnv_extend_eb {c : ZKConfig}
    (gconf : GlobalConfig c) (ms : List (FFMacro c))
    (nextVarId : Nat) (tbEnv ebEnv : SymEnv c)
    (htbEnvFresh : varSetBelow (symEnvVars tbEnv) nextVarId)
    (hebEnvFresh : varSetBelow (symEnvVars ebEnv) nextVarId)
    (hdom : ∀ id, (∃ sv, tbEnv.get? id = some sv) ↔ (∃ sv, ebEnv.get? id = some sv))
    (hshape : ∀ id svTb svEb, tbEnv.get? id = some svTb → ebEnv.get? id = some svEb →
        sameShape svTb svEb)
    (a : Assignment c)
    (env : Env c)
    (hebMatch : ∀ id sv, ebEnv.get? id = some sv →
        ∃ v, env.get? id = some v ∧ symValMatches a sv v) :
    ∃ a' mergedEnv nv tbE ebE,
      mergeSymEnv nextVarId tbEnv ebEnv = Except.ok (mergedEnv, nv, tbE, ebE) ∧
      nextVarId ≤ nv ∧
      (∀ n, n < nextVarId → a'.ff n = a.ff n) ∧ (∀ n, a'.bool n = a.bool n) ∧
      (∀ n, Var.ffv n ∉ (ffVarsOfFormula ebE ∪ bVarsOfFormula ebE) → a'.ff n = a.ff n) ∧
      (∀ id sv, ebEnv.get? id = some sv → ∀ v, env.get? id = some v →
        ∃ sv', mergedEnv.get? id = some sv' ∧ symValMatches a' sv' v) ∧
      evalFormula gconf a' ebE ms = Except.ok true := by
  obtain ⟨a', mergedEnv, nv, tbE, ebE, hcall, hnvMono, ha'_range, ha'_bool, ha'_frame, ha'_match,
      ha'_extra⟩ :=
    mergeSymEnvKeys_extend_eb gconf ms tbEnv.keys nextVarId tbEnv ebEnv FFFormula.true
      FFFormula.true
      (by intro v hv
          simp only [ffVarsOfFormula, bVarsOfFormula] at hv
          rcases Std.TreeSet.mem_union_iff.mp hv with h | h <;>
            exact absurd h Std.TreeSet.not_mem_emptyc)
      htbEnvFresh hebEnvFresh (Std.TreeMap.nodup_keys)
      (fun id hid => (mem_keys_iff_get?_isSome tbEnv id).mp hid)
      (fun id hid => hdom id |>.mp ((mem_keys_iff_get?_isSome tbEnv id).mp hid))
      (fun id _ svTb svEb htb heb => hshape id svTb svEb htb heb)
      a (by simp only [evalFormula]) env
      (fun id hid sv hsv =>
        hebMatch id sv hsv)
  refine ⟨a', mergedEnv, nv, tbE, ebE, ?_, hnvMono, ha'_range, ha'_bool, ha'_frame, ?_, ha'_extra⟩
  · show mergeSymEnv nextVarId tbEnv ebEnv = _
    simp only [mergeSymEnv, hcall]
  · intro id sv hsv v hv
    have hid : id ∈ tbEnv.keys := (mem_keys_iff_get?_isSome tbEnv id).mpr (hdom id |>.mpr ⟨sv, hsv⟩)
    exact ha'_match id hid v hv

/-- **Completeness (`tb` side)** of `mergeSymEnv`: mirrors `mergeSymEnv_extend_tb`, but for a
    fixed assignment that already matches `tbEnv` against a concrete `env` and satisfies the
    merge's own final `tbE`. -/
theorem mergeSymEnv_match_of_tb {c : ZKConfig} (gconf : GlobalConfig c) (ms : List (FFMacro c))
    (assignment' : Assignment c)
    (nextVarId : Nat) (tbEnv ebEnv : SymEnv c)
    (mergedEnv : SymEnv c) (nv' : Nat) (tbE' ebE' : FFFormula c)
    (hfold : mergeSymEnv nextVarId tbEnv ebEnv = Except.ok (mergedEnv, nv', tbE', ebE'))
    (env : Env c)
    (htbMatch : ∀ id sv, tbEnv.get? id = some sv →
        ∃ v, env.get? id = some v ∧ symValMatches assignment' sv v)
    (htbE' : evalFormula gconf assignment' tbE' ms = Except.ok true) :
    ∀ id sv, tbEnv.get? id = some sv → ∀ v, env.get? id = some v →
      ∃ sv', mergedEnv.get? id = some sv' ∧ symValMatches assignment' sv' v := by
  intro id sv hsv v hv
  exact mergeSymEnvKeys_match_of_tb gconf ms assignment' tbEnv.keys nextVarId tbEnv ebEnv
    FFFormula.true FFFormula.true mergedEnv nv' tbE' ebE' hfold env
    (fun id' hid' sv' hsv' => htbMatch id' sv' hsv') htbE'
    id ((mem_keys_iff_get?_isSome tbEnv id).mpr ⟨sv, hsv⟩) v hv

/-- Mirror of `mergeSymEnv_match_of_tb`, for the `eb` side. -/
theorem mergeSymEnv_match_of_eb {c : ZKConfig} (gconf : GlobalConfig c) (ms : List (FFMacro c))
    (assignment' : Assignment c)
    (nextVarId : Nat) (tbEnv ebEnv : SymEnv c)
    (hdom : ∀ id, (∃ sv, tbEnv.get? id = some sv) ↔ (∃ sv, ebEnv.get? id = some sv))
    (mergedEnv : SymEnv c) (nv' : Nat) (tbE' ebE' : FFFormula c)
    (hfold : mergeSymEnv nextVarId tbEnv ebEnv = Except.ok (mergedEnv, nv', tbE', ebE'))
    (env : Env c)
    (hebMatch : ∀ id sv, ebEnv.get? id = some sv →
        ∃ v, env.get? id = some v ∧ symValMatches assignment' sv v)
    (hebE' : evalFormula gconf assignment' ebE' ms = Except.ok true) :
    ∀ id sv, ebEnv.get? id = some sv → ∀ v, env.get? id = some v →
      ∃ sv', mergedEnv.get? id = some sv' ∧ symValMatches assignment' sv' v := by
  intro id sv hsv v hv
  exact mergeSymEnvKeys_match_of_eb gconf ms assignment' tbEnv.keys nextVarId tbEnv ebEnv
    FFFormula.true FFFormula.true mergedEnv nv' tbE' ebE' hfold env
    (fun id' hid' sv' hsv' => hebMatch id' sv' hsv') hebE'
    id ((mem_keys_iff_get?_isSome tbEnv id).mpr (hdom id |>.mpr ⟨sv, hsv⟩)) v hv

-- ---------------------------------------------------------------------------
-- Soundness of `mergeIfBranches`
-- ---------------------------------------------------------------------------

/-- **Soundness** of `mergeIfBranches`: if the concrete `if`-statement succeeds, the merged
    formula (`ite g (f_tb ∧ tbExtra) (f_eb ∧ ebExtra)`) has a matching satisfying extension.
    Only ever needs the *taken* branch's own soundness fact (`h_tb_sound`/`h_eb_sound`) and the
    guard's correctness (`encodeCond_sound`, via `hg`) -- crucially, thanks to `.ite`
    short-circuiting in `evalFormula`, the untaken branch's formula is never evaluated, so no
    totality/well-formedness hypothesis about it is needed at all. `hdom`/`hshape` record that
    `tbSpec.outSymEnv`/`ebSpec.outSymEnv` agree on domain and per-variable shape (guaranteed in
    practice by the zero-init invariant, see `mergeSymEnv_extend_tb`).

    (Sound-only, mirroring `seqComposition_sound`: the converse -- completeness -- additionally
    needs the not-yet-built "a matching concrete env always exists" lemma, so it's deferred.) -/
theorem mergeIfBranches_sound {c : ZKConfig}
    (gconf : GlobalConfig c) (sconf : SymExecConfig c) (specs : List (FuncSpec c))
    (symEnv : SymEnv c) (md : CmdMD) (cond : Cond c)
    (tb eb : List (ComWithMD c)) (p : Prog c)
    (tbSpec ebSpec : CmdsSpec c)
    (hsymEnv_below : varSetBelow (symEnvVars symEnv) sconf.nextVarId)
    (h_tb_mono : sconf.nextVarId ≤ tbSpec.nextVarId)
    (h_eb_mono : sconf.nextVarId ≤ ebSpec.nextVarId)
    (h_tb_below : varSetBelow (specVars tbSpec) tbSpec.nextVarId)
    (h_eb_below : varSetBelow (specVars ebSpec) ebSpec.nextVarId)
    (h_tb_out_below : varSetBelow (symEnvVars tbSpec.outSymEnv) tbSpec.nextVarId)
    (h_eb_out_below : varSetBelow (symEnvVars ebSpec.outSymEnv) ebSpec.nextVarId)
    (hdom : ∀ id, (∃ sv, tbSpec.outSymEnv.get? id = some sv) ↔
        (∃ sv, ebSpec.outSymEnv.get? id = some sv))
    (hshape : ∀ id svTb svEb, tbSpec.outSymEnv.get? id = some svTb →
        ebSpec.outSymEnv.get? id = some svEb → sameShape svTb svEb)
    (g : FFFormula c) (hg : encodeCond symEnv cond = Except.ok g)
    (h_tb_sound : ∀ env assignment, EnvMatches assignment symEnv env →
        ∀ env', evalCmds gconf p env tb = Except.ok env' →
          ∃ assignment',
            agreesOnFF (symEnvVars symEnv) assignment assignment' ∧
            (∀ n, Var.ffv n ∉ specVars tbSpec → assignment'.ff n = assignment.ff n) ∧
            (∀ n, Var.boolv n ∉ specVars tbSpec → assignment'.bool n = assignment.bool n) ∧
            evalFormula gconf assignment' tbSpec.f (specs.map (·.f)) = Except.ok true ∧
            EnvMatches assignment' tbSpec.outSymEnv env')
    (h_eb_sound : ∀ env assignment, EnvMatches assignment symEnv env →
        ∀ env', evalCmds gconf p env eb = Except.ok env' →
          ∃ assignment',
            agreesOnFF (symEnvVars symEnv) assignment assignment' ∧
            (∀ n, Var.ffv n ∉ specVars ebSpec → assignment'.ff n = assignment.ff n) ∧
            (∀ n, Var.boolv n ∉ specVars ebSpec → assignment'.bool n = assignment.bool n) ∧
            evalFormula gconf assignment' ebSpec.f (specs.map (·.f)) = Except.ok true ∧
            EnvMatches assignment' ebSpec.outSymEnv env')
    (env : Env c) (assignment : Assignment c) (hmatch : EnvMatches assignment symEnv env)
    (env' : Env c) (hif : evalIfStmt gconf p env md cond tb eb = Except.ok env') :
    ∃ mergedSpec, mergeIfBranches gconf sconf symEnv specs md tbSpec ebSpec cond
        = Except.ok mergedSpec ∧
      ∃ assignment',
        agreesOnFF (symEnvVars symEnv) assignment assignment' ∧
        (∀ n, Var.ffv n ∉ specVars mergedSpec → assignment'.ff n = assignment.ff n) ∧
        (∀ n, Var.boolv n ∉ specVars mergedSpec → assignment'.bool n = assignment.bool n) ∧
        evalFormula gconf assignment' mergedSpec.f (specs.map (·.f)) = Except.ok true ∧
        EnvMatches assignment' mergedSpec.outSymEnv env' := by
  have hgsub := encodeCond_vars_subset symEnv cond g hg
  simp only [evalIfStmt] at hif
  cases hcond : evalCond env cond with
  | error e => rw [hcond] at hif; simp at hif
  | ok condVal =>
    rw [hcond] at hif
    cases condVal with
    | true =>
        simp only [if_true] at hif
        obtain ⟨assignment1, a1_ff, a1_ffframe, a1_boolframe, a1_eval, a1_match⟩ :=
          h_tb_sound env assignment hmatch env' hif
        have htbEnvFresh : varSetBelow (symEnvVars tbSpec.outSymEnv)
            (max tbSpec.nextVarId ebSpec.nextVarId) :=
          varSetBelow_mono (le_max_left _ _) h_tb_out_below
        obtain ⟨a', mergedEnv, nv, tbE, ebE, hmerge_eq, hnvMono, ha'_range, ha'_bool, ha'_frame,
            ha'_match, ha'_extra⟩ :=
          mergeSymEnv_extend_tb gconf (specs.map (·.f))
            (max tbSpec.nextVarId ebSpec.nextVarId) tbSpec.outSymEnv ebSpec.outSymEnv htbEnvFresh
            hdom hshape assignment1 env' (fun id sv hsv => a1_match.2 id sv hsv)
        let mergedSpec : CmdsSpec c :=
          { inSymEnv := symEnv, outSymEnv := mergedEnv,
            f := FFFormula.ite g (FFFormula.and tbSpec.f tbE) (FFFormula.and ebSpec.f ebE),
            nextVarId := nv }
        refine ⟨mergedSpec, ?_, a', ?_, ?_, ?_, ?_, ?_⟩
        · simp only [mergeIfBranches, hg, hmerge_eq, mergedSpec]
        · intro n hn
          have hidx : varIndex (Var.ffv n) = n := rfl
          have hlt : n < max tbSpec.nextVarId ebSpec.nextVarId := by
            have h := hsymEnv_below (Var.ffv n) hn
            rw [hidx] at h
            exact lt_of_lt_of_le h (le_trans h_tb_mono (le_max_left _ _))
          exact (a1_ff n hn).trans (ha'_range n hlt).symm
        · intro n hn
          simp only [specVars, mergedSpec, ffVarsOfFormula, bVarsOfFormula, Std.TreeSet.mem_union_iff] at hn
          have hn1 : Var.ffv n ∉ specVars tbSpec := by
            simp only [specVars, Std.TreeSet.mem_union_iff]
            intro h; exact hn (by tauto)
          have hn2 : Var.ffv n ∉ (ffVarsOfFormula tbE ∪ bVarsOfFormula tbE) := by
            simp only [Std.TreeSet.mem_union_iff]
            intro h; exact hn (by tauto)
          exact (ha'_frame n hn2).trans (a1_ffframe n hn1)
        · intro n hn
          simp only [specVars, mergedSpec, ffVarsOfFormula, bVarsOfFormula, Std.TreeSet.mem_union_iff] at hn
          have hn1 : Var.boolv n ∉ specVars tbSpec := by
            simp only [specVars, Std.TreeSet.mem_union_iff]
            intro h; exact hn (by tauto)
          exact (ha'_bool n).trans (a1_boolframe n hn1)
        · have hgeval : evalFormula gconf a' g (specs.map (·.f)) = Except.ok true := by
            have hcongr1 : evalFormula gconf a' g (specs.map (·.f))
                = evalFormula gconf assignment1 g (specs.map (·.f)) := by
              apply evalFormula_congr
              · intro n hn
                have hidx : varIndex (Var.ffv n) = n := rfl
                have h := hsymEnv_below (Var.ffv n) (hgsub.1 (Var.ffv n) hn)
                rw [hidx] at h
                exact ha'_range n (lt_of_lt_of_le h (le_trans h_tb_mono (le_max_left _ _)))
              · intro n hn; exact absurd hn (hgsub.2 (Var.boolv n))
            have hcongr2 : evalFormula gconf assignment1 g (specs.map (·.f))
                = evalFormula gconf assignment g (specs.map (·.f)) := by
              apply evalFormula_congr
              · intro n hn; exact (a1_ff n (hgsub.1 (Var.ffv n) hn)).symm
              · intro n hn; exact absurd hn (hgsub.2 (Var.boolv n))
            have hgassign : evalFormula gconf assignment g (specs.map (·.f)) = Except.ok true :=
              encodeCond_sound gconf (specs.map (·.f)) symEnv cond g hg env assignment hmatch
                true hcond
            rw [hcongr1, hcongr2, hgassign]
          have htbfeval : evalFormula gconf a' tbSpec.f (specs.map (·.f)) = Except.ok true := by
            have hcongr : evalFormula gconf a' tbSpec.f (specs.map (·.f))
                = evalFormula gconf assignment1 tbSpec.f (specs.map (·.f)) := by
              apply evalFormula_congr
              · intro n hn
                exact ha'_range n (lt_of_lt_of_le (h_tb_below (Var.ffv n)
                  (Std.TreeSet.mem_union_of_left hn)) (le_max_left _ _))
              · intro n _hn; exact (ha'_bool n)
            rw [hcongr]; exact a1_eval
          have htbEeval : evalFormula gconf a' tbE (specs.map (·.f)) = Except.ok true := ha'_extra
          exact evalFormula_ite_intro_true gconf a' g (FFFormula.and tbSpec.f tbE)
            (FFFormula.and ebSpec.f ebE) (specs.map (·.f)) hgeval
            (evalFormula_and_intro gconf a' tbSpec.f tbE (specs.map (·.f)) htbfeval htbEeval)
        · refine ⟨fun id => ?_, fun id sv hsv =>
            mergedEnv_matches_of_side tbSpec.outSymEnv mergedEnv
              (fun id' => (mergeSymEnv_domain (max tbSpec.nextVarId ebSpec.nextVarId)
                tbSpec.outSymEnv ebSpec.outSymEnv mergedEnv nv tbE ebE hmerge_eq id'))
              assignment1 a' env' (fun id' sv' hsv' => a1_match.2 id' sv' hsv') ha'_match
              id sv hsv⟩
          exact (mergeSymEnv_domain (max tbSpec.nextVarId ebSpec.nextVarId) tbSpec.outSymEnv
            ebSpec.outSymEnv mergedEnv nv tbE ebE hmerge_eq id).trans (a1_match.1 id)
    | false =>
        simp only [if_false] at hif
        obtain ⟨assignment1, a1_ff, a1_ffframe, a1_boolframe, a1_eval, a1_match⟩ :=
          h_eb_sound env assignment hmatch env' hif
        have htbEnvFresh : varSetBelow (symEnvVars tbSpec.outSymEnv)
            (max tbSpec.nextVarId ebSpec.nextVarId) :=
          varSetBelow_mono (le_max_left _ _) h_tb_out_below
        have hebEnvFresh : varSetBelow (symEnvVars ebSpec.outSymEnv)
            (max tbSpec.nextVarId ebSpec.nextVarId) :=
          varSetBelow_mono (le_max_right _ _) h_eb_out_below
        obtain ⟨a', mergedEnv, nv, tbE, ebE, hmerge_eq, hnvMono, ha'_range, ha'_bool, ha'_frame,
            ha'_match, ha'_extra⟩ :=
          mergeSymEnv_extend_eb gconf (specs.map (·.f))
            (max tbSpec.nextVarId ebSpec.nextVarId) tbSpec.outSymEnv ebSpec.outSymEnv htbEnvFresh
            hebEnvFresh hdom hshape assignment1 env' (fun id sv hsv => a1_match.2 id sv hsv)
        let mergedSpec : CmdsSpec c :=
          { inSymEnv := symEnv, outSymEnv := mergedEnv,
            f := FFFormula.ite g (FFFormula.and tbSpec.f tbE) (FFFormula.and ebSpec.f ebE),
            nextVarId := nv }
        refine ⟨mergedSpec, ?_, a', ?_, ?_, ?_, ?_, ?_⟩
        · simp only [mergeIfBranches, hg, hmerge_eq, mergedSpec]
        · intro n hn
          have hidx : varIndex (Var.ffv n) = n := rfl
          have hlt : n < max tbSpec.nextVarId ebSpec.nextVarId := by
            have h := hsymEnv_below (Var.ffv n) hn
            rw [hidx] at h
            exact lt_of_lt_of_le h (le_trans h_eb_mono (le_max_right _ _))
          exact (a1_ff n hn).trans (ha'_range n hlt).symm
        · intro n hn
          simp only [specVars, mergedSpec, ffVarsOfFormula, bVarsOfFormula, Std.TreeSet.mem_union_iff] at hn
          have hn1 : Var.ffv n ∉ specVars ebSpec := by
            simp only [specVars, Std.TreeSet.mem_union_iff]
            intro h; exact hn (by tauto)
          have hn2 : Var.ffv n ∉ (ffVarsOfFormula ebE ∪ bVarsOfFormula ebE) := by
            simp only [Std.TreeSet.mem_union_iff]
            intro h; exact hn (by tauto)
          exact (ha'_frame n hn2).trans (a1_ffframe n hn1)
        · intro n hn
          simp only [specVars, mergedSpec, ffVarsOfFormula, bVarsOfFormula, Std.TreeSet.mem_union_iff] at hn
          have hn1 : Var.boolv n ∉ specVars ebSpec := by
            simp only [specVars, Std.TreeSet.mem_union_iff]
            intro h; exact hn (by tauto)
          exact (ha'_bool n).trans (a1_boolframe n hn1)
        · have hgeval : evalFormula gconf a' g (specs.map (·.f)) = Except.ok false := by
            have hcongr1 : evalFormula gconf a' g (specs.map (·.f))
                = evalFormula gconf assignment1 g (specs.map (·.f)) := by
              apply evalFormula_congr
              · intro n hn
                have hidx : varIndex (Var.ffv n) = n := rfl
                have h := hsymEnv_below (Var.ffv n) (hgsub.1 (Var.ffv n) hn)
                rw [hidx] at h
                exact ha'_range n (lt_of_lt_of_le h (le_trans h_eb_mono (le_max_right _ _)))
              · intro n hn; exact absurd hn (hgsub.2 (Var.boolv n))
            have hcongr2 : evalFormula gconf assignment1 g (specs.map (·.f))
                = evalFormula gconf assignment g (specs.map (·.f)) := by
              apply evalFormula_congr
              · intro n hn; exact (a1_ff n (hgsub.1 (Var.ffv n) hn)).symm
              · intro n hn; exact absurd hn (hgsub.2 (Var.boolv n))
            have hgassign : evalFormula gconf assignment g (specs.map (·.f)) = Except.ok false :=
              encodeCond_sound gconf (specs.map (·.f)) symEnv cond g hg env assignment hmatch
                false hcond
            rw [hcongr1, hcongr2, hgassign]
          have hebfeval : evalFormula gconf a' ebSpec.f (specs.map (·.f)) = Except.ok true := by
            have hcongr : evalFormula gconf a' ebSpec.f (specs.map (·.f))
                = evalFormula gconf assignment1 ebSpec.f (specs.map (·.f)) := by
              apply evalFormula_congr
              · intro n hn
                exact ha'_range n (lt_of_lt_of_le (h_eb_below (Var.ffv n)
                  (Std.TreeSet.mem_union_of_left hn)) (le_max_right _ _))
              · intro n _hn; exact (ha'_bool n)
            rw [hcongr]; exact a1_eval
          have hebEeval : evalFormula gconf a' ebE (specs.map (·.f)) = Except.ok true := ha'_extra
          exact evalFormula_ite_intro_false gconf a' g (FFFormula.and tbSpec.f tbE)
            (FFFormula.and ebSpec.f ebE) (specs.map (·.f)) hgeval
            (evalFormula_and_intro gconf a' ebSpec.f ebE (specs.map (·.f)) hebfeval hebEeval)
        · have hdom_contains : ∀ id, tbSpec.outSymEnv.contains id ↔ ebSpec.outSymEnv.contains id :=
            fun id => (contains_iff_get?_isSome tbSpec.outSymEnv id).trans
              ((hdom id).trans (contains_iff_get?_isSome ebSpec.outSymEnv id).symm)
          refine ⟨fun id => ?_, fun id sv hsv =>
            mergedEnv_matches_of_side ebSpec.outSymEnv mergedEnv
              (fun id' => (mergeSymEnv_domain (max tbSpec.nextVarId ebSpec.nextVarId)
                tbSpec.outSymEnv ebSpec.outSymEnv mergedEnv nv tbE ebE hmerge_eq id').trans
                (hdom_contains id'))
              assignment1 a' env' (fun id' sv' hsv' => a1_match.2 id' sv' hsv') ha'_match
              id sv hsv⟩
          exact ((mergeSymEnv_domain (max tbSpec.nextVarId ebSpec.nextVarId) tbSpec.outSymEnv
            ebSpec.outSymEnv mergedEnv nv tbE ebE hmerge_eq id).trans (hdom_contains id)).trans
            (a1_match.1 id)

-- ---------------------------------------------------------------------------
-- Completeness of `mergeIfBranches`
-- ---------------------------------------------------------------------------

/-- **Completeness** of `mergeIfBranches`: if the merged formula has a satisfying assignment
    extending a matching concrete input, the concrete `if`-statement succeeds with a matching
    output. Cases on the guard's value (`evalFormula_ite_elim`), recovers which concrete branch
    that corresponds to (`encodeCond_complete`), invokes that branch's own completeness
    (`h_tb_complete`/`h_eb_complete`), then transfers the match from the pre-merge symbolic
    environment to the merged one via the `mergeSymEnv_match_of_tb`/`_eb` chain (reusing
    `mergedEnv_matches_of_side` from the soundness proof, instantiated with the *same*
    assignment on both sides since nothing is being extended here). -/
theorem mergeIfBranches_complete {c : ZKConfig}
    (gconf : GlobalConfig c) (sconf : SymExecConfig c) (specs : List (FuncSpec c))
    (symEnv : SymEnv c) (md : CmdMD) (cond : Cond c)
    (tb eb : List (ComWithMD c)) (p : Prog c)
    (tbSpec ebSpec : CmdsSpec c)
    (hdom : ∀ id, (∃ sv, tbSpec.outSymEnv.get? id = some sv) ↔
        (∃ sv, ebSpec.outSymEnv.get? id = some sv))
    (g : FFFormula c) (hg : encodeCond symEnv cond = Except.ok g)
    (mergedSpec : CmdsSpec c)
    (hmerge_eq : mergeIfBranches gconf sconf symEnv specs md tbSpec ebSpec cond
      = Except.ok mergedSpec)
    (h_tb_complete : ∀ env assignment, EnvMatches assignment symEnv env →
        ∀ assignment', agreesOnFF (symEnvVars symEnv) assignment assignment' →
          evalFormula gconf assignment' tbSpec.f (specs.map (·.f)) = Except.ok true →
          ∃ env', evalCmds gconf p env tb = Except.ok env' ∧
            EnvMatches assignment' tbSpec.outSymEnv env')
    (h_eb_complete : ∀ env assignment, EnvMatches assignment symEnv env →
        ∀ assignment', agreesOnFF (symEnvVars symEnv) assignment assignment' →
          evalFormula gconf assignment' ebSpec.f (specs.map (·.f)) = Except.ok true →
          ∃ env', evalCmds gconf p env eb = Except.ok env' ∧
            EnvMatches assignment' ebSpec.outSymEnv env')
    (env : Env c) (assignment : Assignment c) (hmatch : EnvMatches assignment symEnv env)
    (assignment' : Assignment c)
    (h_ff_agree : agreesOnFF (symEnvVars symEnv) assignment assignment')
    (heval : evalFormula gconf assignment' mergedSpec.f (specs.map (·.f)) = Except.ok true) :
    ∃ env', evalIfStmt gconf p env md cond tb eb = Except.ok env' ∧
      EnvMatches assignment' mergedSpec.outSymEnv env' := by
  have hgsub := encodeCond_vars_subset symEnv cond g hg
  simp only [mergeIfBranches, hg] at hmerge_eq
  cases hmerge : mergeSymEnv (max tbSpec.nextVarId ebSpec.nextVarId) tbSpec.outSymEnv
      ebSpec.outSymEnv with
  | error e => rw [hmerge] at hmerge_eq; simp at hmerge_eq
  | ok result =>
    obtain ⟨mergedEnv, nv', tbExtra', ebExtra'⟩ := result
    rw [hmerge] at hmerge_eq
    simp only [Except.ok.injEq] at hmerge_eq
    subst hmerge_eq
    simp only [evalIfStmt]
    have hdom_contains : ∀ id, tbSpec.outSymEnv.contains id ↔ ebSpec.outSymEnv.contains id :=
      fun id => (contains_iff_get?_isSome tbSpec.outSymEnv id).trans
        ((hdom id).trans (contains_iff_get?_isSome ebSpec.outSymEnv id).symm)
    rcases evalFormula_ite_elim gconf assignment' g (FFFormula.and tbSpec.f tbExtra')
        (FFFormula.and ebSpec.f ebExtra') (specs.map (·.f)) heval with
      ⟨hgtrue, hAtrue⟩ | ⟨hgfalse, hBtrue⟩
    · have hcond : evalCond env cond = Except.ok true :=
        encodeCond_complete gconf (specs.map (·.f)) symEnv cond g hg env assignment hmatch true
          (by
            have hcongr : evalFormula gconf assignment g (specs.map (·.f))
                = evalFormula gconf assignment' g (specs.map (·.f)) := by
              apply evalFormula_congr
              · intro n hn; exact h_ff_agree n (hgsub.1 (Var.ffv n) hn)
              · intro n hn; exact absurd hn (hgsub.2 (Var.boolv n))
            rw [hcongr]; exact hgtrue)
      simp only [hcond, if_true]
      obtain ⟨htbf, htbE⟩ := evalFormula_and_elim gconf assignment' tbSpec.f tbExtra'
        (specs.map (·.f)) hAtrue
      obtain ⟨env', hc_tb, hmatch_tb⟩ :=
        h_tb_complete env assignment hmatch assignment' h_ff_agree htbf
      refine ⟨env', hc_tb, fun id => ?_, fun id sv hsv =>
        mergedEnv_matches_of_side tbSpec.outSymEnv mergedEnv
          (mergeSymEnv_domain (max tbSpec.nextVarId ebSpec.nextVarId) tbSpec.outSymEnv
            ebSpec.outSymEnv mergedEnv nv' tbExtra' ebExtra' hmerge)
          assignment' assignment' env' hmatch_tb.2
          (mergeSymEnv_match_of_tb gconf (specs.map (·.f)) assignment'
            (max tbSpec.nextVarId ebSpec.nextVarId) tbSpec.outSymEnv ebSpec.outSymEnv
            mergedEnv nv' tbExtra' ebExtra' hmerge env' hmatch_tb.2 htbE)
          id sv hsv⟩
      exact (mergeSymEnv_domain (max tbSpec.nextVarId ebSpec.nextVarId) tbSpec.outSymEnv
        ebSpec.outSymEnv mergedEnv nv' tbExtra' ebExtra' hmerge id).trans (hmatch_tb.1 id)
    · have hcond : evalCond env cond = Except.ok false :=
        encodeCond_complete gconf (specs.map (·.f)) symEnv cond g hg env assignment hmatch false
          (by
            have hcongr : evalFormula gconf assignment g (specs.map (·.f))
                = evalFormula gconf assignment' g (specs.map (·.f)) := by
              apply evalFormula_congr
              · intro n hn; exact h_ff_agree n (hgsub.1 (Var.ffv n) hn)
              · intro n hn; exact absurd hn (hgsub.2 (Var.boolv n))
            rw [hcongr]; exact hgfalse)
      simp only [hcond, if_false]
      obtain ⟨hebf, hebE⟩ := evalFormula_and_elim gconf assignment' ebSpec.f ebExtra'
        (specs.map (·.f)) hBtrue
      obtain ⟨env', hc_eb, hmatch_eb⟩ :=
        h_eb_complete env assignment hmatch assignment' h_ff_agree hebf
      refine ⟨env', hc_eb, fun id => ?_, fun id sv hsv =>
        mergedEnv_matches_of_side ebSpec.outSymEnv mergedEnv
          (fun id' => (mergeSymEnv_domain (max tbSpec.nextVarId ebSpec.nextVarId)
            tbSpec.outSymEnv ebSpec.outSymEnv mergedEnv nv' tbExtra' ebExtra' hmerge id').trans
            (hdom_contains id'))
          assignment' assignment' env' hmatch_eb.2
          (mergeSymEnv_match_of_eb gconf (specs.map (·.f)) assignment'
            (max tbSpec.nextVarId ebSpec.nextVarId) tbSpec.outSymEnv ebSpec.outSymEnv hdom
            mergedEnv nv' tbExtra' ebExtra' hmerge env' hmatch_eb.2 hebE)
          id sv hsv⟩
      exact ((mergeSymEnv_domain (max tbSpec.nextVarId ebSpec.nextVarId) tbSpec.outSymEnv
        ebSpec.outSymEnv mergedEnv nv' tbExtra' ebExtra' hmerge id).trans
        (hdom_contains id)).trans (hmatch_eb.1 id)

/-- `specVars` of a `seqComposition`-produced spec is exactly the union of the two halves'
    `specVars` (`ffVarsOfFormula`/`bVarsOfFormula` both distribute over `.and`, and pass
    straight through the `.anno` wrapper `seqComposition` puts around `cmdSpec1.f`). -/
theorem specVars_seqComposition {c : ZKConfig} (gconf : GlobalConfig c) (sconf : SymExecConfig c)
    (cmd : ComWithMD c) (spec1 spec2 specComposed : CmdsSpec c)
    (heq : seqComposition gconf sconf cmd spec1 spec2 = Except.ok specComposed) (v : Var) :
    v ∈ specVars specComposed ↔ v ∈ specVars spec1 ∨ v ∈ specVars spec2 := by
  simp only [seqComposition, Except.ok.injEq] at heq
  simp only [specVars, ← heq, ffVarsOfFormula, bVarsOfFormula, Std.TreeSet.mem_union_iff]
  tauto

-- ---------------------------------------------------------------------------
-- Soundness of `seqComposition`
-- ---------------------------------------------------------------------------

/-- **Soundness** half of composing two already-sound specs via `seqComposition`: if the
    sequenced concrete computation succeeds, the conjoined formula has a matching satisfying
    extension. Mirrors `functionalCompose` (`FFConstraints/FunctionalFormula.lean`): the
    disjointness side condition that lemma needs supplied externally is derived here instead
    from freshness (`h1_below`/`h2_fresh`) -- `spec2`'s "genuinely new" vars all sit at or
    above `spec1.nextVarId`, while every one of `spec1`'s vars sits below it, so the two can
    only ever share vars that `spec2` declares as carried-over inputs.

    (This is the sound-only half of the eventual `seqComposition_correct`; the converse
    -- completeness -- additionally needs a "a matching concrete env always exists for any
    `SymEnv`/`Assignment` pair" lemma that hasn't been built yet, so it's deferred.) -/
theorem seqComposition_sound {c : ZKConfig}
    (gconf : GlobalConfig c) (sconf : SymExecConfig c) (specs : List (FuncSpec c))
    (spec1 spec2 : CmdsSpec c)
    (concrete1 concrete2 : Env c → Except String (Env c))
    (hin1_below : varSetBelow (symEnvVars spec1.inSymEnv) sconf.nextVarId)
    (h1_mono : sconf.nextVarId ≤ spec1.nextVarId)
    (h1_below : varSetBelow (specVars spec1) spec1.nextVarId)
    (h1_sound : ∀ env assignment, EnvMatches assignment spec1.inSymEnv env →
        ∀ env', concrete1 env = Except.ok env' →
          ∃ assignment',
            agreesOnFF (symEnvVars spec1.inSymEnv) assignment assignment' ∧
            (∀ n, Var.ffv n ∉ specVars spec1 → assignment'.ff n = assignment.ff n) ∧
            (∀ n, Var.boolv n ∉ specVars spec1 → assignment'.bool n = assignment.bool n) ∧
            evalFormula gconf assignment' spec1.f (specs.map (·.f)) = Except.ok true ∧
            EnvMatches assignment' spec1.outSymEnv env')
    (h2_fresh : ∀ v ∈ specVars spec2, v ∈ symEnvVars spec2.inSymEnv ∨ spec1.nextVarId ≤ varIndex v)
    (h2_sound : ∀ env assignment, EnvMatches assignment spec2.inSymEnv env →
        ∀ env', concrete2 env = Except.ok env' →
          ∃ assignment',
            agreesOnFF (symEnvVars spec2.inSymEnv) assignment assignment' ∧
            (∀ n, Var.ffv n ∉ specVars spec2 → assignment'.ff n = assignment.ff n) ∧
            (∀ n, Var.boolv n ∉ specVars spec2 → assignment'.bool n = assignment.bool n) ∧
            evalFormula gconf assignment' spec2.f (specs.map (·.f)) = Except.ok true ∧
            EnvMatches assignment' spec2.outSymEnv env')
    (hlink : spec2.inSymEnv = spec1.outSymEnv)
    (env : Env c) (assignment : Assignment c) (hmatch : EnvMatches assignment spec1.inSymEnv env)
    (env' : Env c) (hbind : (concrete1 env).bind concrete2 = Except.ok env') :
    ∃ assignment',
      agreesOnFF (symEnvVars spec1.inSymEnv) assignment assignment' ∧
      (∀ n, Var.ffv n ∉ (specVars spec1 ∪ specVars spec2) → assignment'.ff n = assignment.ff n) ∧
      (∀ n, Var.boolv n ∉ (specVars spec1 ∪ specVars spec2) → assignment'.bool n = assignment.bool n) ∧
      evalFormula gconf assignment' (.and (.anno spec1.f "") spec2.f) (specs.map (·.f)) =
        Except.ok true ∧
      EnvMatches assignment' spec2.outSymEnv env' := by
  cases hc1 : concrete1 env with
  | error e =>
      rw [hc1] at hbind
      simp [Except.bind] at hbind
  | ok envMid =>
    rw [hc1] at hbind
    simp only [Except.bind] at hbind
    obtain ⟨assignment1, a1_ff, a1_ffframe, a1_boolframe, a1_eval, a1_match⟩ :=
      h1_sound env assignment hmatch envMid hc1
    have hmatch2 : EnvMatches assignment1 spec2.inSymEnv envMid := by rw [hlink]; exact a1_match
    obtain ⟨assignment2, a2_ff, a2_ffframe, a2_boolframe, a2_eval, a2_match⟩ :=
      h2_sound envMid assignment1 hmatch2 env' hbind
    -- disjointness, derived from freshness: a var in both footprints must be one of spec2's
    -- declared inputs (ff), and no bool var of spec1 can ever be one of spec2's vars at all.
    have hdisj_ff : ∀ n, Var.ffv n ∈ specVars spec1 → Var.ffv n ∈ specVars spec2 →
        Var.ffv n ∈ symEnvVars spec2.inSymEnv := by
      intro n hn1 hn2
      rcases h2_fresh (Var.ffv n) hn2 with hin | hfresh
      · exact hin
      · exfalso
        have h1' := h1_below (Var.ffv n) hn1
        have hidx : varIndex (Var.ffv n) = n := rfl
        rw [hidx] at h1' hfresh
        omega
    have hdisj_bool : ∀ n, Var.boolv n ∈ specVars spec1 → Var.boolv n ∉ specVars spec2 := by
      intro n hn1 hn2
      rcases h2_fresh (Var.boolv n) hn2 with hin | hfresh
      · obtain ⟨m, hm⟩ := symEnvVars_isFF spec2.inSymEnv (Var.boolv n) hin
        rw [show compare (Var.ffv m) (Var.boolv n) = Ordering.lt from rfl] at hm
        exact absurd hm (by decide)
      · exfalso
        have h1' := h1_below (Var.boolv n) hn1
        have hidx : varIndex (Var.boolv n) = n := rfl
        rw [hidx] at h1' hfresh
        omega
    -- a var of spec1's own input: shared with spec2's declared inputs (agree keeps it) or
    -- private to spec2 (frame keeps it) -- either way assignment1 = assignment2 there
    have hcarry_ff : ∀ n, Var.ffv n ∈ symEnvVars spec1.inSymEnv →
        assignment1.ff n = assignment2.ff n := by
      intro n hn
      by_cases hn2 : Var.ffv n ∈ specVars spec2
      · have hn2in : Var.ffv n ∈ symEnvVars spec2.inSymEnv := by
          rcases h2_fresh (Var.ffv n) hn2 with hin | hfresh
          · exact hin
          · exfalso
            have h1' := hin1_below (Var.ffv n) hn
            have hidx : varIndex (Var.ffv n) = n := rfl
            rw [hidx] at h1' hfresh
            omega
        exact a2_ff n hn2in
      · exact (a2_ffframe n hn2).symm
    -- same argument, this time for spec1's own formula footprint
    have hown_ff : ∀ n, Var.ffv n ∈ specVars spec1 → assignment1.ff n = assignment2.ff n := by
      intro n hn
      by_cases hn2 : Var.ffv n ∈ specVars spec2
      · exact a2_ff n (hdisj_ff n hn hn2)
      · exact (a2_ffframe n hn2).symm
    have hown_bool : ∀ n, Var.boolv n ∈ specVars spec1 → assignment1.bool n = assignment2.bool n :=
      fun n hn => (a2_boolframe n (hdisj_bool n hn)).symm
    have h_f1_assignment2 :
        evalFormula gconf assignment2 spec1.f (specs.map (·.f)) = Except.ok true := by
      rw [← evalFormula_congr gconf (specs.map (·.f)) spec1.f assignment1 assignment2
            (fun n hn => hown_ff n (Std.TreeSet.mem_union_of_left hn))
            (fun n hn => hown_bool n (Std.TreeSet.mem_union_of_right hn))]
      exact a1_eval
    refine ⟨assignment2, ?_, ?_, ?_, ?_, a2_match⟩
    · exact fun n hn => (a1_ff n hn).trans (hcarry_ff n hn)
    · intro n hn
      have hn1 : Var.ffv n ∉ specVars spec1 := fun h => hn (Std.TreeSet.mem_union_of_left h)
      have hn2 : Var.ffv n ∉ specVars spec2 := fun h => hn (Std.TreeSet.mem_union_of_right h)
      exact (a2_ffframe n hn2).trans (a1_ffframe n hn1)
    · intro n hn
      have hn1 : Var.boolv n ∉ specVars spec1 := fun h => hn (Std.TreeSet.mem_union_of_left h)
      have hn2 : Var.boolv n ∉ specVars spec2 := fun h => hn (Std.TreeSet.mem_union_of_right h)
      exact (a2_boolframe n hn2).trans (a1_boolframe n hn1)
    · exact evalFormula_and_intro gconf assignment2 (.anno spec1.f "") spec2.f (specs.map (·.f))
        (by rw [evalFormula_anno]; exact h_f1_assignment2) a2_eval

-- ---------------------------------------------------------------------------
-- Completeness of `seqComposition`
-- ---------------------------------------------------------------------------

/-- **Completeness** half of composing two specs via `seqComposition`: if the conjoined
    formula has a satisfying assignment extending a matching concrete input, the sequenced
    concrete computation succeeds with a matching output.

    Unlike `seqComposition_sound`, this needs no freshness/disjointness argument at all --
    `h1_complete`/`h2_complete` each only need `assignment'` to agree with their own starting
    assignment on their own declared inputs (`symEnvVars _.inSymEnv`) and to make their own
    formula true; no "outside my footprint" frame precondition is needed, since a spec's own
    formula, by `evalFormula_congr`, never cares what `assignment'` does outside its own
    footprint anyway. In particular this needs no "decode-existence" step (`decode_exists`) --
    every concrete `Env` involved (`env`, then `env1`) is produced constructively by chaining
    `h1_complete` into `h2_complete`, never conjured from bare symbolic/assignment data alone. -/
theorem seqComposition_complete {c : ZKConfig}
    (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (spec1 spec2 : CmdsSpec c)
    (concrete1 concrete2 : Env c → Except String (Env c))
    (hlink : spec2.inSymEnv = spec1.outSymEnv)
    (h1_complete : ∀ env assignment, EnvMatches assignment spec1.inSymEnv env →
        ∀ assignment', agreesOnFF (symEnvVars spec1.inSymEnv) assignment assignment' →
          evalFormula gconf assignment' spec1.f (specs.map (·.f)) = Except.ok true →
          ∃ env1, concrete1 env = Except.ok env1 ∧ EnvMatches assignment' spec1.outSymEnv env1)
    (h2_complete : ∀ env assignment, EnvMatches assignment spec2.inSymEnv env →
        ∀ assignment', agreesOnFF (symEnvVars spec2.inSymEnv) assignment assignment' →
          evalFormula gconf assignment' spec2.f (specs.map (·.f)) = Except.ok true →
          ∃ env2, concrete2 env = Except.ok env2 ∧ EnvMatches assignment' spec2.outSymEnv env2)
    (env : Env c) (assignment : Assignment c) (hmatch : EnvMatches assignment spec1.inSymEnv env)
    (assignment' : Assignment c)
    (h_ff_agree : agreesOnFF (symEnvVars spec1.inSymEnv) assignment assignment')
    (heval : evalFormula gconf assignment' (.and (.anno spec1.f "") spec2.f) (specs.map (·.f)) =
      Except.ok true) :
    ∃ env', (concrete1 env).bind concrete2 = Except.ok env' ∧
      EnvMatches assignment' spec2.outSymEnv env' := by
  obtain ⟨heval1, heval2⟩ := evalFormula_and_elim gconf assignment' (.anno spec1.f "") spec2.f
    (specs.map (·.f)) heval
  rw [evalFormula_anno] at heval1
  obtain ⟨env1, hc1, hmatch1⟩ := h1_complete env assignment hmatch assignment' h_ff_agree heval1
  have hmatch1' : EnvMatches assignment' spec2.inSymEnv env1 := by rw [hlink]; exact hmatch1
  obtain ⟨env2, hc2, hmatch2⟩ :=
    h2_complete env1 assignment' hmatch1' assignment' (fun _ _ => rfl) heval2
  refine ⟨env2, ?_, hmatch2⟩
  simp only [Except.bind, hc1, hc2]

-- ---------------------------------------------------------------------------
-- `encodeCond` always succeeds when `evalCond` does, for every concrete environment
-- ---------------------------------------------------------------------------

/-- If `evalSimpleExprToFFValue` succeeds on a concrete environment matching `symEnv`,
    `resolveSimpleExpr` succeeds on `symEnv` itself -- success only depends on a variable's
    *shape* (scalar vs. array), which `EnvMatches` ties directly to its concrete counterpart's
    shape (`symValMatches`'s `.simple`/`.scalar` vs. `.array`/`.array` cases). -/
theorem resolveSimpleExpr_defined_of_evalSimpleExprToFFValue {c : ZKConfig}
    (symEnv : SymEnv c) (s : SimpleExpr c) (env : Env c) (assignment : Assignment c)
    (hmatch : EnvMatches assignment symEnv env) (v : FF c)
    (heval : evalSimpleExprToFFValue env s = Except.ok v) :
    ∃ sv, resolveSimpleExpr symEnv s = Except.ok sv := by
  cases s with
  | val v' => exact ⟨.const v', rfl⟩
  | var id =>
      simp only [evalSimpleExprToFFValue] at heval
      cases hg : Corellzk2smt.Language.Core.Semantics.Basic.getVar env id with
      | error e => rw [hg] at heval; simp at heval
      | ok val' =>
        rw [hg] at heval
        cases val' with
        | array _ => simp at heval
        | scalar v' =>
          have henvget : env.get? id = some (Value.scalar v') := (getVarEnv_eq_ok_iff env id _).mp hg
          have hcontains : env.contains id := contains_iff_get?_isSome env id |>.mpr ⟨_, henvget⟩
          have hsymcontains : symEnv.contains id := (hmatch.1 id).mpr hcontains
          obtain ⟨sv, hsv⟩ := contains_iff_get?_isSome symEnv id |>.mp hsymcontains
          obtain ⟨v'', henv'', hsvm⟩ := hmatch.2 id sv hsv
          rw [henvget] at henv''
          injection henv'' with henv''
          cases sv with
          | array _ => rw [← henv''] at hsvm; simp only [symValMatches] at hsvm
          | simple s' =>
              refine ⟨s', ?_⟩
              have hgetVar : Corellzk2smt.SymExec.Basic.getVar symEnv id =
                  Except.ok (SymValue.simple s') := (getVar_eq_ok_iff symEnv id (.simple s')).mpr hsv
              simp only [resolveSimpleExpr, hgetVar]

/-- If `evalCond` succeeds on every concrete environment, `encodeCond` succeeds on every
    matching symbolic environment (via `EnvMatches_decodeSymEnv`, which manufactures a
    matching concrete `Env` for any `SymEnv`/`Assignment` pair) -- so a program-level
    guarantee that a condition is always well-defined transfers straight from the concrete
    to the symbolic side. -/
theorem encodeCond_defined {c : ZKConfig} (symEnv : SymEnv c) (cond : Cond c)
    (hdef : ∀ (env : Env c), ∃ b, evalCond env cond = Except.ok b) :
    ∃ g, encodeCond symEnv cond = Except.ok g := by
  cases cond with
  | eq s1 s2 =>
      set env := decodeSymEnv (default : Assignment c) symEnv with henv
      have hmatch := EnvMatches_decodeSymEnv (default : Assignment c) symEnv
      obtain ⟨b, hb⟩ := hdef env
      simp only [evalCond] at hb
      cases hc1 : evalSimpleExprToFFValue env s1 with
      | error e => rw [hc1] at hb; simp at hb
      | ok val1 =>
        rw [hc1] at hb
        cases hc2 : evalSimpleExprToFFValue env s2 with
        | error e => rw [hc2] at hb; simp at hb
        | ok val2 =>
          obtain ⟨sv1, hsv1⟩ :=
            resolveSimpleExpr_defined_of_evalSimpleExprToFFValue symEnv s1 env
              (default : Assignment c) hmatch val1 hc1
          obtain ⟨sv2, hsv2⟩ :=
            resolveSimpleExpr_defined_of_evalSimpleExprToFFValue symEnv s2 env
              (default : Assignment c) hmatch val2 hc2
          refine ⟨FFFormula.eq (simpleSymValToTerm sv1) (simpleSymValToTerm sv2), ?_⟩
          simp only [encodeCond, hsv1, hsv2]

-- ---------------------------------------------------------------------------
-- `H_domain` is not vacuous the way `H_shape` was: `seFuncCall`'s `setVars` call can grow
-- a symbolic environment's domain (nothing rules that out from `seCmds` succeeding alone). But
-- given every variable a command could ever write is already in the environment's domain before
-- execution starts (`definedVarsCom`/`definedVarsCmds`, `Language/Core/Analysis/DefinedVars.lean`
-- -- exactly what `seFunc_correct`'s `inSymEnv` construction already guarantees), the domain
-- genuinely never changes. This mirrors `seCmd_correct`/`seCmds_correct`/`seIfStmt_correct`'s own
-- mutual recursion/termination measure exactly (same case structure, same decreasing proofs --
-- copied verbatim), but proves a much narrower fact (no `EnvMatches`/soundness/completeness
-- bookkeeping needed) so it stands alone rather than reusing that induction.
--
-- NOT YET WIRED IN: `H_domain` in `PartialCorrectness/Correctness.lean`/`FuncCorrectness.lean`/
-- `ProgCorrectness.lean` still remains a permanently-assumed hypothesis, unchanged. Actually
-- replacing it would mean threading a `vars`/precondition parameter (mirroring this theorem's
-- own `vars`/`hpre`) through `seCmd_correct`/`seCmds_correct`/`seIfStmt_correct`'s *existing*
-- recursion (interleaved with their `EnvMatches`/soundness/completeness bookkeeping), then
-- supplying the actual witness at `seFunc_correct`'s level from how `inSymEnv` is built
-- (`definedVarsOfFunc`-based pre-population) -- a comparable-sized follow-up, deferred for now.
-- ---------------------------------------------------------------------------

mutual

theorem seIfStmt_domain_of_defined {c : ZKConfig} (gconf : GlobalConfig c) (sconf : SymExecConfig c)
    (symEnv : SymEnv c) (specs : List (FuncSpec c)) (vars : VarIDSet) (md : CmdMD) (cond : Cond c)
    (tb eb : List (ComWithMD c))
    (hpre : ∀ id, id ∈ definedVarsCmds (definedVarsCmds vars tb) eb → symEnv.contains id)
    (spec : CmdsSpec c)
    (heq : seIfStmt gconf sconf symEnv specs md cond tb eb = Except.ok spec) :
    ∀ id, symEnv.contains id ↔ spec.outSymEnv.contains id := by
  have htb_pre : ∀ id, id ∈ definedVarsCmds vars tb → symEnv.contains id :=
    fun id hid => hpre id (definedVarsCmds_mono eb (definedVarsCmds vars tb) id hid)
  have heb_pre : ∀ id, id ∈ definedVarsCmds vars eb → symEnv.contains id :=
    fun id hid => hpre id
      (definedVarsCmds_subset_mono eb vars (definedVarsCmds vars tb)
        (fun id' hid' => definedVarsCmds_mono tb vars id' hid') id hid)
  cases htry : tryEvalCondToConcreteValue gconf sconf symEnv md cond with
  | ok condVal =>
      cases condVal with
      | true =>
          have h : seIfStmt gconf sconf symEnv specs md cond tb eb =
              seCmds gconf sconf symEnv specs tb := by simp only [seIfStmt, htry, if_true]
          rw [h] at heq
          exact seCmds_domain_of_defined gconf sconf symEnv specs vars tb htb_pre spec heq
      | false =>
          have h : seIfStmt gconf sconf symEnv specs md cond tb eb =
              seCmds gconf sconf symEnv specs eb := by
            simp only [seIfStmt, htry, Bool.false_eq_true, if_false]
          rw [h] at heq
          exact seCmds_domain_of_defined gconf sconf symEnv specs vars eb heb_pre spec heq
  | error e =>
      cases htbSpec_eq : seCmds gconf sconf symEnv specs tb with
      | error e2 => simp [seIfStmt, htry, htbSpec_eq] at heq
      | ok tbSpec =>
      cases hebSpec_eq : seCmds gconf sconf symEnv specs eb with
      | error e2 => simp [seIfStmt, htry, htbSpec_eq, hebSpec_eq] at heq
      | ok ebSpec =>
      have htbDom := seCmds_domain_of_defined gconf sconf symEnv specs vars tb htb_pre tbSpec
        htbSpec_eq
      have hmerge_eq : mergeIfBranches gconf sconf symEnv specs md tbSpec ebSpec cond =
          Except.ok spec := by
        have h : seIfStmt gconf sconf symEnv specs md cond tb eb =
            mergeIfBranches gconf sconf symEnv specs md tbSpec ebSpec cond := by
          simp only [seIfStmt, htry, htbSpec_eq, hebSpec_eq]
        rw [← h]; exact heq
      intro id
      rw [htbDom id]
      simp only [mergeIfBranches] at hmerge_eq
      cases hg : encodeCond symEnv cond with
      | error e2 => rw [hg] at hmerge_eq; simp at hmerge_eq
      | ok g =>
        rw [hg] at hmerge_eq
        simp only [] at hmerge_eq
        cases hms : mergeSymEnv (max tbSpec.nextVarId ebSpec.nextVarId) tbSpec.outSymEnv
            ebSpec.outSymEnv with
        | error e2 => rw [hms] at hmerge_eq; simp at hmerge_eq
        | ok result =>
          obtain ⟨mergedEnv, nv', tbE', ebE'⟩ := result
          rw [hms] at hmerge_eq
          simp only [Except.ok.injEq] at hmerge_eq
          have hspec_out : spec.outSymEnv = mergedEnv := by rw [← hmerge_eq]
          rw [hspec_out]
          exact (mergeSymEnv_domain (max tbSpec.nextVarId ebSpec.nextVarId) tbSpec.outSymEnv
            ebSpec.outSymEnv mergedEnv nv' tbE' ebE' hms id).symm
termination_by (numOfLoopExpComs tb + numOfLoopExpComs eb, sizeOfComs tb + sizeOfComs eb)
decreasing_by
  all_goals first
  | (have h1 : numOfLoopExpComs tb ≤ numOfLoopExpComs tb + numOfLoopExpComs eb := by grind
     rcases Nat.lt_or_eq_of_le h1 with h_less | h_equal
     · apply Prod.Lex.left
       exact h_less
     · rw [← h_equal]
       apply Prod.Lex.right
       exact sizeOfComs_a_lt_a_plus_b tb eb)
  | (have h1 : numOfLoopExpComs eb ≤ numOfLoopExpComs tb + numOfLoopExpComs eb := by grind
     rcases Nat.lt_or_eq_of_le h1 with h_less | h_equal
     · apply Prod.Lex.left
       exact h_less
     · rw [← h_equal]
       apply Prod.Lex.right
       rw [← Nat.add_comm]
       exact sizeOfComs_a_lt_a_plus_b eb tb)

theorem seCmd_domain_of_defined {c : ZKConfig} (gconf : GlobalConfig c) (sconf : SymExecConfig c)
    (symEnv : SymEnv c) (specs : List (FuncSpec c)) (vars : VarIDSet) (md : CmdMD) (cmd : Com c)
    (hpre : ∀ id, id ∈ definedVarsCom vars cmd → symEnv.contains id)
    (spec : CmdsSpec c)
    (heq : seCmd gconf sconf symEnv specs (ComWithMD.mk md cmd) = Except.ok spec) :
    ∀ id, symEnv.contains id ↔ spec.outSymEnv.contains id := by
  match cmd, hpre with
  | .if_stmt cond tb eb, hpre =>
      have h : seCmd gconf sconf symEnv specs (ComWithMD.mk md (Com.if_stmt cond tb eb)) =
          seIfStmt gconf sconf symEnv specs md cond tb eb := by simp only [seCmd]
      rw [h] at heq
      have hpre' : ∀ id, id ∈ definedVarsCmds (definedVarsCmds vars tb) eb → symEnv.contains id :=
        fun id hid => hpre id (by simp only [definedVarsCom]; exact hid)
      exact seIfStmt_domain_of_defined gconf sconf symEnv specs vars md cond tb eb hpre' spec heq
  | .loop_exp repSExp body, hpre =>
      cases htry : tryEvalSimpleExprToFFValue symEnv repSExp with
      | error e => simp [seCmd, htry] at heq
      | ok repVal =>
          have h : seCmd gconf sconf symEnv specs (ComWithMD.mk md (Com.loop_exp repSExp body)) =
              seCmd gconf sconf symEnv specs (ComWithMD.mk md (Com.loop repVal.val body)) := by
            simp only [seCmd, htry]
          rw [h] at heq
          have hpre' : ∀ id, id ∈ definedVarsCom vars (Com.loop repVal.val body) →
              symEnv.contains id :=
            fun id hid => hpre id (by simp only [definedVarsCom] at hid ⊢; exact hid)
          exact seCmd_domain_of_defined gconf sconf symEnv specs vars md (Com.loop repVal.val body)
            hpre' spec heq
  | .loop (rep+1) body, hpre =>
      cases hfirstSpec_eq : seCmds gconf { nextVarId := sconf.nextVarId } symEnv specs body with
      | error e => simp [seCmd, hfirstSpec_eq] at heq
      | ok firstSpec =>
      have hbody_pre : ∀ id, id ∈ definedVarsCmds vars body → symEnv.contains id :=
        fun id hid => hpre id (by simp only [definedVarsCom] at hid ⊢; exact hid)
      have hfirstDom := seCmds_domain_of_defined gconf { nextVarId := sconf.nextVarId } symEnv specs
        vars body hbody_pre firstSpec hfirstSpec_eq
      cases hrestSpec_eq : seCmd gconf { sconf with nextVarId := firstSpec.nextVarId }
          firstSpec.outSymEnv specs (ComWithMD.mk md (Com.loop rep body)) with
      | error e => simp [seCmd, hfirstSpec_eq, hrestSpec_eq] at heq
      | ok restSpec =>
      have hrest_pre : ∀ id, id ∈ definedVarsCom vars (Com.loop rep body) →
          firstSpec.outSymEnv.contains id := by
        intro id hid
        rw [← hfirstDom id]
        exact hbody_pre id (by simp only [definedVarsCom] at hid; exact hid)
      have hrestDom := seCmd_domain_of_defined gconf { sconf with nextVarId := firstSpec.nextVarId }
        firstSpec.outSymEnv specs vars md (Com.loop rep body) hrest_pre restSpec hrestSpec_eq
      have hspecComposed_eq :
          seqComposition gconf sconf (ComWithMD.mk md (Com.loop (rep+1) body)) firstSpec
            restSpec = Except.ok spec := by
        have h : seCmd gconf sconf symEnv specs (ComWithMD.mk md (Com.loop (rep+1) body)) =
            seqComposition gconf sconf (ComWithMD.mk md (Com.loop (rep+1) body)) firstSpec
              restSpec := by
          simp only [seCmd, hfirstSpec_eq, hrestSpec_eq]
        rw [← h]; exact heq
      simp only [seqComposition, Except.ok.injEq] at hspecComposed_eq
      have hout_eq : spec.outSymEnv = restSpec.outSymEnv := by rw [← hspecComposed_eq]
      intro id
      rw [hfirstDom id, hrestDom id, hout_eq]
  | .loop 0 _body, _hpre =>
      simp only [seCmd, Except.ok.injEq] at heq
      intro id
      rw [← heq]
  | .func_call outs fname args, hpre =>
      have h : seCmd gconf sconf symEnv specs (ComWithMD.mk md (Com.func_call outs fname args)) =
          seFuncCall gconf sconf symEnv specs fname args outs := by simp only [seCmd]
      rw [h] at heq
      simp only [seFuncCall] at heq
      cases hfs : fetchFuncSpec specs fname with
      | error e => rw [hfs] at heq; simp at heq
      | ok fspec =>
      rw [hfs] at heq
      simp only [] at heq
      cases hargs : resolveSimpleExprsToSymValue symEnv args with
      | error e => rw [hargs] at heq; simp at heq
      | ok argVals =>
      rw [hargs] at heq
      simp only [] at heq
      cases hflat : flattenArgVals fspec.params argVals with
      | error e => rw [hflat] at heq; simp at heq
      | ok inputParams =>
      rw [hflat] at heq
      simp only [] at heq
      cases hsv : Corellzk2smt.SymExec.Basic.setVars symEnv outs
          (mintFreshRets sconf.nextVarId fspec.rets).2.2 with
      | error e => rw [hsv] at heq; simp at heq
      | ok outSymEnv' =>
      rw [hsv] at heq
      simp only [Except.ok.injEq] at heq
      have hspec_out : spec.outSymEnv = outSymEnv' := by rw [← heq]
      intro id
      rw [hspec_out, setVars_contains_iff symEnv outs _ outSymEnv' hsv id]
      constructor
      · intro h; exact Or.inr h
      · rintro (hout | hsymc)
        · exact hpre id (by
            simp only [definedVarsCom]
            exact mem_foldl_insert_var outs vars id hout)
        · exact hsymc
  | .assign out e, _hpre =>
      simp [seCmd, seSimpleCmd] at heq
  | .new_array out size, _hpre =>
      simp [seCmd, seSimpleCmd] at heq
  | .read_array out arr idx, _hpre =>
      simp [seCmd, seSimpleCmd] at heq
  | .write_array arr idx value, _hpre =>
      simp [seCmd, seSimpleCmd] at heq
  | .copy_array out arr, _hpre =>
      simp [seCmd, seSimpleCmd] at heq
termination_by (numOfLoopExpCom (ComWithMD.mk md cmd), sizeOfCom (ComWithMD.mk md cmd))
decreasing_by
  all_goals first
    | (simp only [numOfLoopExpCom]; apply Prod.Lex.left; grind)
    | (apply Prod.Lex.right; simp only [sizeOfCom]; grind)

theorem seCmds_domain_of_defined {c : ZKConfig} (gconf : GlobalConfig c) (sconf : SymExecConfig c)
    (symEnv : SymEnv c) (specs : List (FuncSpec c)) (vars : VarIDSet) (cmds : List (ComWithMD c))
    (hpre : ∀ id, id ∈ definedVarsCmds vars cmds → symEnv.contains id)
    (spec : CmdsSpec c)
    (heq : seCmds gconf sconf symEnv specs cmds = Except.ok spec) :
    ∀ id, symEnv.contains id ↔ spec.outSymEnv.contains id := by
  cases cmds with
  | nil =>
      simp only [seCmds] at heq
      injection heq with heq'
      intro id
      rw [← heq']
  | cons cmd rest =>
      cases cmd with
      | mk md cmd' =>
        have hcmd_pre : ∀ id, id ∈ definedVarsCom vars cmd' → symEnv.contains id :=
          fun id hid => hpre id (by
            simp only [definedVarsCmds]
            exact definedVarsCmds_mono rest (definedVarsCom vars cmd') id hid)
        cases hcmdSpec_eq : seCmd gconf sconf symEnv specs (ComWithMD.mk md cmd') with
        | error e => simp [seCmds, hcmdSpec_eq] at heq
        | ok cmdSpec =>
        have hcmdDom := seCmd_domain_of_defined gconf sconf symEnv specs vars md cmd' hcmd_pre
          cmdSpec hcmdSpec_eq
        have hrest_pre : ∀ id, id ∈ definedVarsCmds vars rest → cmdSpec.outSymEnv.contains id := by
          intro id hid
          rw [← hcmdDom id]
          exact hpre id (by
            simp only [definedVarsCmds]
            exact definedVarsCmds_subset_mono rest vars (definedVarsCom vars cmd')
              (fun id' hid' => definedVarsCom_mono cmd' vars id' hid') id hid)
        cases hcmdsSpec_eq : seCmds gconf { sconf with nextVarId := cmdSpec.nextVarId }
            cmdSpec.outSymEnv specs rest with
        | error e => simp [seCmds, hcmdSpec_eq, hcmdsSpec_eq] at heq
        | ok cmdsSpec =>
        have hrestDom := seCmds_domain_of_defined gconf
          { sconf with nextVarId := cmdSpec.nextVarId } cmdSpec.outSymEnv specs vars rest
          hrest_pre cmdsSpec hcmdsSpec_eq
        have hspecComposed_eq :
            seqComposition gconf sconf (ComWithMD.mk md cmd') cmdSpec cmdsSpec =
              Except.ok spec := by
          have h : seCmds gconf sconf symEnv specs (ComWithMD.mk md cmd' :: rest) =
              seqComposition gconf sconf (ComWithMD.mk md cmd') cmdSpec cmdsSpec := by
            simp only [seCmds, hcmdSpec_eq, hcmdsSpec_eq]
          rw [← h]; exact heq
        simp only [seqComposition, Except.ok.injEq] at hspecComposed_eq
        have hout_eq : spec.outSymEnv = cmdsSpec.outSymEnv := by rw [← hspecComposed_eq]
        intro id
        rw [hcmdDom id, hrestDom id, hout_eq]
termination_by (numOfLoopExpComs cmds, sizeOfComs cmds)
decreasing_by
  -- cross-call into seCmd_domain_of_defined, on the head `cmd'`
  · have hcmds_eq : cmds = ComWithMD.mk md cmd' :: rest := by
      rw [‹cmds = cmd :: rest›, ‹cmd = ComWithMD.mk md cmd'›]
    rw [hcmds_eq]
    have h1 : numOfLoopExpCom (ComWithMD.mk md cmd') ≤
        numOfLoopExpCom (ComWithMD.mk md cmd') + numOfLoopExpComs rest := by grind
    rcases Nat.lt_or_eq_of_le h1 with h_less | h_equal
    · apply Prod.Lex.left
      simp only [numOfLoopExpComs]
      exact h_less
    · simp only [numOfLoopExpComs]
      rw [← h_equal]
      apply Prod.Lex.right
      simp only [sizeOfComs]
      grind
  -- recursive call into seCmds_domain_of_defined itself, on `rest`
  · have hcmds_eq : cmds = ComWithMD.mk md cmd' :: rest := by
      rw [‹cmds = cmd :: rest›, ‹cmd = ComWithMD.mk md cmd'›]
    have h1 : numOfLoopExpComs rest ≤
        numOfLoopExpCom (ComWithMD.mk md cmd') + numOfLoopExpComs rest := by grind
    rcases Nat.lt_or_eq_of_le h1 with h_less | h_equal
    · apply Prod.Lex.left
      rw [hcmds_eq]
      simp only [numOfLoopExpComs]
      exact h_less
    · rw [hcmds_eq]
      simp only [numOfLoopExpComs]
      rw [← h_equal]
      apply Prod.Lex.right
      simp only [sizeOfComs]
      grind

end

end Corellzk2smt.SymExec.Lemmas
