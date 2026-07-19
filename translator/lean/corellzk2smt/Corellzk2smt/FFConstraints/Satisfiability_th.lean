import Corellzk2smt.Basic
import Corellzk2smt.Config
import Corellzk2smt.FFConstraints.Basic
import Corellzk2smt.FFConstraints.Satisfiability

/- Theorems about the executable semantics defined in `FFConstraints/Satisfiability.lean`. -/

namespace Corellzk2smt.FFConstraints.Satisfiability_th

open Corellzk2smt.Config (GlobalConfig)
open Corellzk2smt.FFConstraints.Basic
open Corellzk2smt.FFConstraints.Satisfiability

-- ---------------------------------------------------------------------------
-- Agreement relations on assignments
-- ---------------------------------------------------------------------------

/-- Two assignments agree on all FF vars in vs -/
def agreesOnFF {c : ZKConfig} (vs : VarSet) (a b : Assignment c) : Prop :=
  ∀ n, Var.ffv n ∈ vs → a.ff n = b.ff n

/-- Two assignments agree on all bool vars in vs -/
def agreesOnBool {c : ZKConfig} (vs : VarSet) (a b : Assignment c) : Prop :=
  ∀ n, Var.boolv n ∈ vs → a.bool n = b.bool n


-- ---------------------------------------------------------------------------
-- Congruence for evalFormula
-- ---------------------------------------------------------------------------

/-- Monotonicity of `agreesOnFF`/`agreesOnBool`: agreement on a bigger var set
    implies agreement on any subset. Used to restrict a congruence hypothesis
    from a compound term/formula down to one of its subterms. -/
theorem agreesOnFF_mono {c : ZKConfig} {s t : VarSet} {a b : Assignment c}
    (h_sub : s ⊆ t) (h : agreesOnFF t a b) : agreesOnFF s a b :=
  fun n hn => h n (h_sub (Var.ffv n) hn)

theorem agreesOnBool_mono {c : ZKConfig} {s t : VarSet} {a b : Assignment c}
    (h_sub : s ⊆ t) (h : agreesOnBool t a b) : agreesOnBool s a b :=
  fun n hn => h n (h_sub (Var.boolv n) hn)

/-- Folding `(fun acc p => match p with | .var (.ffv n) => acc.insert (Var.ffv n) | _ => acc)`
    (the fold used by `ffVarsOfFormula` on `.call` arguments) never removes vars already in
    the accumulator. -/
theorem foldl_ffFold_mono {c : ZKConfig} (args : List (MacroCallParam c)) (acc : VarSet)
    (x : Var) (hx : x ∈ acc) :
    x ∈ args.foldl (fun acc p => match p with
        | .var (.ffv n) => acc.insert (Var.ffv n)
        | _             => acc) acc := by
  induction args generalizing acc with
  | nil => simpa using hx
  | cons p tl ih =>
      simp only [List.foldl_cons]
      cases p with
      | var v =>
          cases v with
          | ffv n   => exact ih _ (Std.TreeSet.mem_insert.mpr (Or.inr hx))
          | boolv n => exact ih _ hx
      | const v => exact ih _ hx

theorem foldl_bFold_mono {c : ZKConfig} (args : List (MacroCallParam c)) (acc : VarSet)
    (x : Var) (hx : x ∈ acc) :
    x ∈ args.foldl (fun acc p => match p with
        | .var (.boolv n) => acc.insert (Var.boolv n)
        | _               => acc) acc := by
  induction args generalizing acc with
  | nil => simpa using hx
  | cons p tl ih =>
      simp only [List.foldl_cons]
      cases p with
      | var v =>
          cases v with
          | ffv n   => exact ih _ hx
          | boolv n => exact ih _ (Std.TreeSet.mem_insert.mpr (Or.inr hx))
      | const v => exact ih _ hx

/-- If `n` occurs as a FF-var argument somewhere in `args`, it belongs to the folded
    var set, no matter the starting accumulator. -/
theorem foldl_ffFold_complete {c : ZKConfig} (args : List (MacroCallParam c)) (n : FFVar)
    (acc : VarSet) (h : MacroCallParam.var (Var.ffv n) ∈ args) :
    Var.ffv n ∈ args.foldl (fun acc p => match p with
        | .var (.ffv n) => acc.insert (Var.ffv n)
        | _             => acc) acc := by
  induction args generalizing acc with
  | nil => simp at h
  | cons p tl ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp h with heq | hmem
      · subst heq
        exact foldl_ffFold_mono tl (acc.insert (Var.ffv n)) (Var.ffv n)
          Std.TreeSet.mem_insert_self
      · exact ih _ hmem

theorem foldl_bFold_complete {c : ZKConfig} (args : List (MacroCallParam c)) (n : BoolVar)
    (acc : VarSet) (h : MacroCallParam.var (Var.boolv n) ∈ args) :
    Var.boolv n ∈ args.foldl (fun acc p => match p with
        | .var (.boolv n) => acc.insert (Var.boolv n)
        | _               => acc) acc := by
  induction args generalizing acc with
  | nil => simp at h
  | cons p tl ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp h with heq | hmem
      · subst heq
        exact foldl_bFold_mono tl (acc.insert (Var.boolv n)) (Var.boolv n)
          Std.TreeSet.mem_insert_self
      · exact ih _ hmem

/-- If `n` is passed as a FF-var argument in a macro call `.call name args`, then
    `Var.ffv n` belongs to `ffVarsOfFormula (.call name args)`. -/
theorem mem_ffVars_call_of_mem_args {c : ZKConfig} (name : String)
    (args : List (MacroCallParam c)) (n : FFVar)
    (h : MacroCallParam.var (Var.ffv n) ∈ args) :
    Var.ffv n ∈ ffVarsOfFormula (FFFormula.call name args) :=
  foldl_ffFold_complete args n emptyVarSet h

theorem mem_bVars_call_of_mem_args {c : ZKConfig} (name : String)
    (args : List (MacroCallParam c)) (n : BoolVar)
    (h : MacroCallParam.var (Var.boolv n) ∈ args) :
    Var.boolv n ∈ bVarsOfFormula (FFFormula.call name args) :=
  foldl_bFold_complete args n emptyVarSet h

/-- `newAssignment'` only reads `assign` at the FF/bool vars that are actually passed
    as arguments, so two assignments agreeing there build the very same assignment. -/
theorem newAssignment'_congr {c : ZKConfig} (a b : Assignment c)
    (args : List (MacroCallParam c)) (params : List Var)
    (ffMap : FFVar → FF c) (boolMap : BoolVar → Bool)
    (h_ff : ∀ n, MacroCallParam.var (Var.ffv n) ∈ args → a.ff n = b.ff n)
    (h_bool : ∀ n, MacroCallParam.var (Var.boolv n) ∈ args → a.bool n = b.bool n) :
    newAssignment' a args params ffMap boolMap = newAssignment' b args params ffMap boolMap := by
  match params, args with
  | [], [] => rfl
  | (Var.ffv _p) :: params', (MacroCallParam.var (Var.ffv n)) :: args' =>
      simp only [newAssignment']
      rw [h_ff n (List.mem_cons_self ..)]
      exact newAssignment'_congr a b args' params' _ boolMap
        (fun m hm => h_ff m (List.mem_cons_of_mem _ hm))
        (fun m hm => h_bool m (List.mem_cons_of_mem _ hm))
  | (Var.ffv _p) :: params', (MacroCallParam.const (Const.ffc _t)) :: args' =>
      simp only [newAssignment']
      exact newAssignment'_congr a b args' params' _ boolMap
        (fun m hm => h_ff m (List.mem_cons_of_mem _ hm))
        (fun m hm => h_bool m (List.mem_cons_of_mem _ hm))
  | (Var.boolv _p) :: params', (MacroCallParam.var (Var.boolv n)) :: args' =>
      simp only [newAssignment']
      rw [h_bool n (List.mem_cons_self ..)]
      exact newAssignment'_congr a b args' params' ffMap _
        (fun m hm => h_ff m (List.mem_cons_of_mem _ hm))
        (fun m hm => h_bool m (List.mem_cons_of_mem _ hm))
  | (Var.boolv _p) :: params', (MacroCallParam.const (Const.boolc _t)) :: args' =>
      simp only [newAssignment']
      exact newAssignment'_congr a b args' params' ffMap _
        (fun m hm => h_ff m (List.mem_cons_of_mem _ hm))
        (fun m hm => h_bool m (List.mem_cons_of_mem _ hm))
  | [], (MacroCallParam.var (Var.ffv _)) :: _ => rfl
  | [], (MacroCallParam.var (Var.boolv _)) :: _ => rfl
  | [], (MacroCallParam.const (Const.ffc _)) :: _ => rfl
  | [], (MacroCallParam.const (Const.boolc _)) :: _ => rfl
  | (Var.ffv _) :: _, [] => rfl
  | (Var.boolv _) :: _, [] => rfl
  | (Var.ffv _) :: _, (MacroCallParam.var (Var.boolv _)) :: _ => rfl
  | (Var.boolv _) :: _, (MacroCallParam.var (Var.ffv _)) :: _ => rfl
  | (Var.ffv _) :: _, (MacroCallParam.const (Const.boolc _)) :: _ => rfl
  | (Var.boolv _) :: _, (MacroCallParam.const (Const.ffc _)) :: _ => rfl

theorem newAssignment_congr {c : ZKConfig} (a b : Assignment c)
    (args : List (MacroCallParam c)) (params : List Var)
    (h_ff : ∀ n, MacroCallParam.var (Var.ffv n) ∈ args → a.ff n = b.ff n)
    (h_bool : ∀ n, MacroCallParam.var (Var.boolv n) ∈ args → a.bool n = b.bool n) :
    newAssignment a args params = newAssignment b args params :=
  newAssignment'_congr a b args params _ _ h_ff h_bool

-- `evalFormula`/`evalTerm` depend only on the vars that actually appear in the
-- term/formula being evaluated. If two assignments agree on all FF vars in
-- `ffVarsOfTerm`/`ffVarsOfFormula` and all bool vars in `bVarsOfTerm`/`bVarsOfFormula`,
-- evaluation is the same. Proved by mutual structural induction on the term/formula;
-- the `.call` case needs no induction into the macro body, since the renamed
-- assignment built for the call is *literally* the same for `a` and `b`
-- (via `newAssignment_congr`).
mutual
theorem evalTerm_congr {c : ZKConfig}
    (gconf : GlobalConfig c) (ms : List (FFMacro c)) (t : FFTerm c) (a b : Assignment c)
    (h_ff : agreesOnFF (ffVarsOfTerm t) a b)
    (h_bool : agreesOnBool (bVarsOfTerm t) a b)
    : evalTerm gconf a t ms = evalTerm gconf b t ms := by
  match t with
  | .val _ => simp only [evalTerm]
  | .var v =>
      simp only [evalTerm]
      rw [h_ff v Std.TreeSet.mem_insert_self]
  | .add t1 t2 =>
      have ih1 := evalTerm_congr gconf ms t1 a b
        (agreesOnFF_mono (fun x hx => Std.TreeSet.mem_union_of_left  hx) h_ff)
        (agreesOnBool_mono (fun x hx => Std.TreeSet.mem_union_of_left  hx) h_bool)
      have ih2 := evalTerm_congr gconf ms t2 a b
        (agreesOnFF_mono (fun x hx => Std.TreeSet.mem_union_of_right hx) h_ff)
        (agreesOnBool_mono (fun x hx => Std.TreeSet.mem_union_of_right hx) h_bool)
      simp only [evalTerm, ih1, ih2]
  | .sub t1 t2 =>
      have ih1 := evalTerm_congr gconf ms t1 a b
        (agreesOnFF_mono (fun x hx => Std.TreeSet.mem_union_of_left  hx) h_ff)
        (agreesOnBool_mono (fun x hx => Std.TreeSet.mem_union_of_left  hx) h_bool)
      have ih2 := evalTerm_congr gconf ms t2 a b
        (agreesOnFF_mono (fun x hx => Std.TreeSet.mem_union_of_right hx) h_ff)
        (agreesOnBool_mono (fun x hx => Std.TreeSet.mem_union_of_right hx) h_bool)
      simp only [evalTerm, ih1, ih2]
  | .mul t1 t2 =>
      have ih1 := evalTerm_congr gconf ms t1 a b
        (agreesOnFF_mono (fun x hx => Std.TreeSet.mem_union_of_left  hx) h_ff)
        (agreesOnBool_mono (fun x hx => Std.TreeSet.mem_union_of_left  hx) h_bool)
      have ih2 := evalTerm_congr gconf ms t2 a b
        (agreesOnFF_mono (fun x hx => Std.TreeSet.mem_union_of_right hx) h_ff)
        (agreesOnBool_mono (fun x hx => Std.TreeSet.mem_union_of_right hx) h_bool)
      simp only [evalTerm, ih1, ih2]
  | .neg t1 =>
      have ih1 := evalTerm_congr gconf ms t1 a b h_ff h_bool
      simp only [evalTerm, ih1]
  | .ite g t1 t2 =>
      have ihg := evalFormula_congr gconf ms g a b
        (agreesOnFF_mono (fun x hx => Std.TreeSet.mem_union_of_left
            (Std.TreeSet.mem_union_of_left hx)) h_ff)
        (agreesOnBool_mono (fun x hx => Std.TreeSet.mem_union_of_left
            (Std.TreeSet.mem_union_of_left hx)) h_bool)
      simp only [evalTerm, ihg]
      cases hgv : evalFormula gconf b g ms with
      | error e => rfl
      | ok vc =>
          cases vc with
          | true =>
              exact evalTerm_congr gconf ms t1 a b
                (agreesOnFF_mono (fun x hx => Std.TreeSet.mem_union_of_left
                    (Std.TreeSet.mem_union_of_right hx)) h_ff)
                (agreesOnBool_mono (fun x hx => Std.TreeSet.mem_union_of_left
                    (Std.TreeSet.mem_union_of_right hx)) h_bool)
          | false =>
              exact evalTerm_congr gconf ms t2 a b
                (agreesOnFF_mono (fun x hx => Std.TreeSet.mem_union_of_right hx) h_ff)
                (agreesOnBool_mono (fun x hx => Std.TreeSet.mem_union_of_right hx) h_bool)
termination_by sizeOfTerm t
decreasing_by all_goals (simp only [sizeOfTerm]; omega)

theorem evalFormula_congr {c : ZKConfig}
    (gconf : GlobalConfig c) (ms : List (FFMacro c)) (f : FFFormula c) (a b : Assignment c)
    (h_ff : agreesOnFF (ffVarsOfFormula f) a b)
    (h_bool : agreesOnBool (bVarsOfFormula f) a b)
    : evalFormula gconf a f ms = evalFormula gconf b f ms := by
  match f with
  | .true => simp only [evalFormula]
  | .false => simp only [evalFormula]
  | .range t _l _u =>
      have iht := evalTerm_congr gconf ms t a b h_ff h_bool
      simp only [evalFormula, iht]
  | .bool v =>
      simp only [evalFormula]
      rw [h_bool v Std.TreeSet.mem_insert_self]
  | .eq t1 t2 =>
      have ih1 := evalTerm_congr gconf ms t1 a b
        (agreesOnFF_mono   (fun x hx => Std.TreeSet.mem_union_of_left  hx) h_ff)
        (agreesOnBool_mono (fun x hx => Std.TreeSet.mem_union_of_left  hx) h_bool)
      have ih2 := evalTerm_congr gconf ms t2 a b
        (agreesOnFF_mono   (fun x hx => Std.TreeSet.mem_union_of_right hx) h_ff)
        (agreesOnBool_mono (fun x hx => Std.TreeSet.mem_union_of_right hx) h_bool)
      simp only [evalFormula, ih1, ih2]
  | .and f1 f2 =>
      have ih1 := evalFormula_congr gconf ms f1 a b
        (agreesOnFF_mono   (fun x hx => Std.TreeSet.mem_union_of_left  hx) h_ff)
        (agreesOnBool_mono (fun x hx => Std.TreeSet.mem_union_of_left  hx) h_bool)
      have ih2 := evalFormula_congr gconf ms f2 a b
        (agreesOnFF_mono   (fun x hx => Std.TreeSet.mem_union_of_right hx) h_ff)
        (agreesOnBool_mono (fun x hx => Std.TreeSet.mem_union_of_right hx) h_bool)
      simp only [evalFormula, ih1, ih2]
  | .or f1 f2 =>
      have ih1 := evalFormula_congr gconf ms f1 a b
        (agreesOnFF_mono   (fun x hx => Std.TreeSet.mem_union_of_left  hx) h_ff)
        (agreesOnBool_mono (fun x hx => Std.TreeSet.mem_union_of_left  hx) h_bool)
      have ih2 := evalFormula_congr gconf ms f2 a b
        (agreesOnFF_mono   (fun x hx => Std.TreeSet.mem_union_of_right hx) h_ff)
        (agreesOnBool_mono (fun x hx => Std.TreeSet.mem_union_of_right hx) h_bool)
      simp only [evalFormula, ih1, ih2]
  | .not f1 =>
      have ih1 := evalFormula_congr gconf ms f1 a b h_ff h_bool
      simp only [evalFormula, ih1]
  | .ite g f1 f2 =>
      have ihg := evalFormula_congr gconf ms g a b
        (agreesOnFF_mono   (fun x hx => Std.TreeSet.mem_union_of_left
            (Std.TreeSet.mem_union_of_left hx)) h_ff)
        (agreesOnBool_mono (fun x hx => Std.TreeSet.mem_union_of_left
            (Std.TreeSet.mem_union_of_left hx)) h_bool)
      simp only [evalFormula, ihg]
      cases hgv : evalFormula gconf b g ms with
      | error e => rfl
      | ok vc =>
          cases vc with
          | true =>
              exact evalFormula_congr gconf ms f1 a b
                (agreesOnFF_mono   (fun x hx => Std.TreeSet.mem_union_of_left
                    (Std.TreeSet.mem_union_of_right hx)) h_ff)
                (agreesOnBool_mono (fun x hx => Std.TreeSet.mem_union_of_left
                    (Std.TreeSet.mem_union_of_right hx)) h_bool)
          | false =>
              exact evalFormula_congr gconf ms f2 a b
                (agreesOnFF_mono   (fun x hx => Std.TreeSet.mem_union_of_right hx) h_ff)
                (agreesOnBool_mono (fun x hx => Std.TreeSet.mem_union_of_right hx) h_bool)
  | .imply f1 f2 =>
      have ih1 := evalFormula_congr gconf ms f1 a b
        (agreesOnFF_mono   (fun x hx => Std.TreeSet.mem_union_of_left  hx) h_ff)
        (agreesOnBool_mono (fun x hx => Std.TreeSet.mem_union_of_left  hx) h_bool)
      have ih2 := evalFormula_congr gconf ms f2 a b
        (agreesOnFF_mono   (fun x hx => Std.TreeSet.mem_union_of_right hx) h_ff)
        (agreesOnBool_mono (fun x hx => Std.TreeSet.mem_union_of_right hx) h_bool)
      simp only [evalFormula, ih1, ih2]
  | .iff f1 f2 =>
      have ih1 := evalFormula_congr gconf ms f1 a b
        (agreesOnFF_mono   (fun x hx => Std.TreeSet.mem_union_of_left  hx) h_ff)
        (agreesOnBool_mono (fun x hx => Std.TreeSet.mem_union_of_left  hx) h_bool)
      have ih2 := evalFormula_congr gconf ms f2 a b
        (agreesOnFF_mono   (fun x hx => Std.TreeSet.mem_union_of_right hx) h_ff)
        (agreesOnBool_mono (fun x hx => Std.TreeSet.mem_union_of_right hx) h_bool)
      simp only [evalFormula, ih1, ih2]
  | .call name args =>
      have h_ff'   : ∀ n, MacroCallParam.var (Var.ffv n) ∈ args → a.ff n   = b.ff n :=
        fun n hn => h_ff n (mem_ffVars_call_of_mem_args name args n hn)
      have h_bool' : ∀ n, MacroCallParam.var (Var.boolv n) ∈ args → a.bool n = b.bool n :=
        fun n hn => h_bool n (mem_bVars_call_of_mem_args name args n hn)
      simp only [evalFormula]
      split
      · rfl
      · rename_i m ms' _
        rw [newAssignment_congr a b args m.params h_ff' h_bool']
  | .anno f1 _ =>
      have ih1 := evalFormula_congr gconf ms f1 a b h_ff h_bool
      simp only [evalFormula, ih1]
termination_by sizeOfFormula f
decreasing_by all_goals (simp only [sizeOfFormula]; omega)
end

-- ---------------------------------------------------------------------------
-- Prepending name-disjoint macros doesn't change a successful evaluation
-- ---------------------------------------------------------------------------

/-- If `fetchMacro` succeeds, the found macro's own name matches, it's a member of the searched
    list, and its remainder (`ms'`) is a sub-list (mirrors `fetchMacroLT`'s own induction shape,
    giving the membership/name facts `fetchMacroLT` doesn't). -/
theorem fetchMacro_sound {c : ZKConfig} (gconf : GlobalConfig c) :
    ∀ (ms ms' : List (FFMacro c)) (name : String) (m : FFMacro c),
      fetchMacro gconf ms name = Except.ok (m, ms') →
      m.name = name ∧ m ∈ ms ∧ ∀ x ∈ ms', x ∈ ms := by
  intro ms
  induction ms with
  | nil => intro ms' name m h; simp [fetchMacro] at h
  | cons head tail ih =>
      intro ms' name m h
      simp only [fetchMacro] at h
      by_cases hc : head.name = name
      · simp only [hc, BEq.rfl, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        refine ⟨h1 ▸ hc, ?_, fun x hx => List.mem_cons_of_mem _ (h2 ▸ hx)⟩
        rw [← h1]; exact List.mem_cons_self ..
      · simp only [hc, beq_iff_eq, ↓reduceIte] at h
        obtain ⟨hname, hmem, hsub⟩ := ih ms' name m h
        exact ⟨hname, List.mem_cons_of_mem _ hmem, fun x hx => List.mem_cons_of_mem _ (hsub x hx)⟩

/-- If `fetchMacro` finds `name` in `ms`, searching `extra ++ ms` instead gives exactly the same
    result, provided none of `extra`'s own macros are named `name` -- `fetchMacro`'s recursion
    skips straight past every non-matching entry, so once past `extra` (all of which fail to
    match, by hypothesis) the search continues exactly as `fetchMacro gconf ms name` would, with
    no leftover trace of `extra` in the returned remainder. -/
theorem fetchMacro_prepend_indep {c : ZKConfig} (gconf : GlobalConfig c) :
    ∀ (extra ms : List (FFMacro c)) (name : String),
      (∀ m ∈ extra, m.name ≠ name) →
      fetchMacro gconf (extra ++ ms) name = fetchMacro gconf ms name := by
  intro extra
  induction extra with
  | nil => intro ms name _; rfl
  | cons m extra ih =>
      intro ms name hdisj
      have hne : m.name ≠ name := hdisj m (List.mem_cons_self ..)
      have hbeq : (m.name == name) = false := by simpa using hne
      simp only [List.cons_append, fetchMacro, hbeq, Bool.false_eq_true, ↓reduceIte]
      exact ih ms name (fun m' hm' => hdisj m' (List.mem_cons_of_mem _ hm'))

-- `evalTerm`/`evalFormula`'s successful results are unaffected by prepending macros to the
-- macro list, as long as none of the prepended macros share a name with anything in the
-- original list -- needed for the whole-program correctness argument (`seExecFuncs_correct`):
-- a function's own `TranslatesCorrectly` fact, proven using only the specs of functions *after*
-- it, still holds once more functions get prepended to the front of the final specs list.
-- Phrased as "given a successful evaluation against `ms`, the same evaluation against
-- `extra ++ ms` succeeds with the same result" (not a full bidirectional equality) because that
-- asymmetric form is all `TranslatesCorrectly`-style facts ever need, and it sidesteps having
-- to reason about *unsuccessful* lookups (where `extra`'s disjointness-from-`ms` alone wouldn't
-- rule out an accidental name collision with whatever `fetchMacro` was actually searching for).
-- Every actual `fetchMacro` call encountered along a *successful* evaluation path necessarily
-- finds its target within `ms` (or a shrinking suffix of it), so `fetchMacro_prepend_indep`
-- applies validly at every step.
mutual
theorem evalTerm_prepend_indep {c : ZKConfig} (gconf : GlobalConfig c) (extra : List (FFMacro c))
    (assign : Assignment c) (t : FFTerm c) (ms : List (FFMacro c)) (v : FF c)
    (hdisj : ∀ m ∈ extra, ∀ m' ∈ ms, m.name ≠ m'.name)
    (heval : evalTerm gconf assign t ms = Except.ok v) :
    evalTerm gconf assign t (extra ++ ms) = Except.ok v := by
  match t with
  | .val v' => simp only [evalTerm] at heval ⊢; exact heval
  | .var v' => simp only [evalTerm] at heval ⊢; exact heval
  | .add t1 t2 =>
      simp only [evalTerm] at heval
      cases h1 : evalTerm gconf assign t1 ms with
      | error e => rw [h1] at heval; simp at heval
      | ok v1 =>
          rw [h1] at heval
          cases h2 : evalTerm gconf assign t2 ms with
          | error e => rw [h2] at heval; simp at heval
          | ok v2 =>
              rw [h2] at heval
              injection heval with heval
              have ih1 := evalTerm_prepend_indep gconf extra assign t1 ms v1 hdisj h1
              have ih2 := evalTerm_prepend_indep gconf extra assign t2 ms v2 hdisj h2
              simp only [evalTerm, ih1, ih2, ← heval]
  | .sub t1 t2 =>
      simp only [evalTerm] at heval
      cases h1 : evalTerm gconf assign t1 ms with
      | error e => rw [h1] at heval; simp at heval
      | ok v1 =>
          rw [h1] at heval
          cases h2 : evalTerm gconf assign t2 ms with
          | error e => rw [h2] at heval; simp at heval
          | ok v2 =>
              rw [h2] at heval
              injection heval with heval
              have ih1 := evalTerm_prepend_indep gconf extra assign t1 ms v1 hdisj h1
              have ih2 := evalTerm_prepend_indep gconf extra assign t2 ms v2 hdisj h2
              simp only [evalTerm, ih1, ih2, ← heval]
  | .mul t1 t2 =>
      simp only [evalTerm] at heval
      cases h1 : evalTerm gconf assign t1 ms with
      | error e => rw [h1] at heval; simp at heval
      | ok v1 =>
          rw [h1] at heval
          cases h2 : evalTerm gconf assign t2 ms with
          | error e => rw [h2] at heval; simp at heval
          | ok v2 =>
              rw [h2] at heval
              injection heval with heval
              have ih1 := evalTerm_prepend_indep gconf extra assign t1 ms v1 hdisj h1
              have ih2 := evalTerm_prepend_indep gconf extra assign t2 ms v2 hdisj h2
              simp only [evalTerm, ih1, ih2, ← heval]
  | .neg t1 =>
      simp only [evalTerm] at heval
      cases h1 : evalTerm gconf assign t1 ms with
      | error e => rw [h1] at heval; simp at heval
      | ok v1 =>
          rw [h1] at heval
          injection heval with heval
          have ih1 := evalTerm_prepend_indep gconf extra assign t1 ms v1 hdisj h1
          simp only [evalTerm, ih1, ← heval]
  | .ite g t1 t2 =>
      simp only [evalTerm] at heval
      cases hg : evalFormula gconf assign g ms with
      | error e => rw [hg] at heval; simp at heval
      | ok vc =>
          rw [hg] at heval
          have ihg := evalFormula_prepend_indep gconf extra assign g ms vc hdisj hg
          simp only [evalTerm, ihg]
          cases vc with
          | true => exact evalTerm_prepend_indep gconf extra assign t1 ms v hdisj heval
          | false => exact evalTerm_prepend_indep gconf extra assign t2 ms v hdisj heval
termination_by sizeOfTerm t
decreasing_by all_goals (simp only [sizeOfTerm]; grind)

theorem evalFormula_prepend_indep {c : ZKConfig} (gconf : GlobalConfig c) (extra : List (FFMacro c))
    (assign : Assignment c) (f : FFFormula c) (ms : List (FFMacro c)) (v : Bool)
    (hdisj : ∀ m ∈ extra, ∀ m' ∈ ms, m.name ≠ m'.name)
    (heval : evalFormula gconf assign f ms = Except.ok v) :
    evalFormula gconf assign f (extra ++ ms) = Except.ok v := by
  match f with
  | .true => simp only [evalFormula] at heval ⊢; exact heval
  | .false => simp only [evalFormula] at heval ⊢; exact heval
  | .range t l u =>
      simp only [evalFormula] at heval
      cases ht : evalTerm gconf assign t ms with
      | error e => rw [ht] at heval; simp at heval
      | ok vt =>
          rw [ht] at heval
          have iht := evalTerm_prepend_indep gconf extra assign t ms vt hdisj ht
          simp only [evalFormula, iht]
          exact heval
  | .bool v' => simp only [evalFormula] at heval ⊢; exact heval
  | .eq t1 t2 =>
      simp only [evalFormula] at heval
      cases h1 : evalTerm gconf assign t1 ms with
      | error e => rw [h1] at heval; simp at heval
      | ok v1 =>
          rw [h1] at heval
          cases h2 : evalTerm gconf assign t2 ms with
          | error e => rw [h2] at heval; simp at heval
          | ok v2 =>
              rw [h2] at heval
              have ih1 := evalTerm_prepend_indep gconf extra assign t1 ms v1 hdisj h1
              have ih2 := evalTerm_prepend_indep gconf extra assign t2 ms v2 hdisj h2
              simp only [evalFormula, ih1, ih2]
              exact heval
  | .and f1 f2 =>
      simp only [evalFormula] at heval
      cases h1 : evalFormula gconf assign f1 ms with
      | error e => rw [h1] at heval; simp at heval
      | ok v1 =>
          rw [h1] at heval
          cases h2 : evalFormula gconf assign f2 ms with
          | error e => rw [h2] at heval; simp at heval
          | ok v2 =>
              rw [h2] at heval
              injection heval with heval
              have ih1 := evalFormula_prepend_indep gconf extra assign f1 ms v1 hdisj h1
              have ih2 := evalFormula_prepend_indep gconf extra assign f2 ms v2 hdisj h2
              simp only [evalFormula, ih1, ih2, ← heval]
  | .or f1 f2 =>
      simp only [evalFormula] at heval
      cases h1 : evalFormula gconf assign f1 ms with
      | error e => rw [h1] at heval; simp at heval
      | ok v1 =>
          rw [h1] at heval
          cases h2 : evalFormula gconf assign f2 ms with
          | error e => rw [h2] at heval; simp at heval
          | ok v2 =>
              rw [h2] at heval
              injection heval with heval
              have ih1 := evalFormula_prepend_indep gconf extra assign f1 ms v1 hdisj h1
              have ih2 := evalFormula_prepend_indep gconf extra assign f2 ms v2 hdisj h2
              simp only [evalFormula, ih1, ih2, ← heval]
  | .not f1 =>
      simp only [evalFormula] at heval
      cases h1 : evalFormula gconf assign f1 ms with
      | error e => rw [h1] at heval; simp at heval
      | ok v1 =>
          rw [h1] at heval
          injection heval with heval
          have ih1 := evalFormula_prepend_indep gconf extra assign f1 ms v1 hdisj h1
          simp only [evalFormula, ih1, ← heval]
  | .ite g f1 f2 =>
      simp only [evalFormula] at heval
      cases hg : evalFormula gconf assign g ms with
      | error e => rw [hg] at heval; simp at heval
      | ok vc =>
          rw [hg] at heval
          have ihg := evalFormula_prepend_indep gconf extra assign g ms vc hdisj hg
          simp only [evalFormula, ihg]
          cases vc with
          | true => exact evalFormula_prepend_indep gconf extra assign f1 ms v hdisj heval
          | false => exact evalFormula_prepend_indep gconf extra assign f2 ms v hdisj heval
  | .imply f1 f2 =>
      simp only [evalFormula] at heval
      cases h1 : evalFormula gconf assign f1 ms with
      | error e => rw [h1] at heval; simp at heval
      | ok v1 =>
          rw [h1] at heval
          cases h2 : evalFormula gconf assign f2 ms with
          | error e => rw [h2] at heval; simp at heval
          | ok v2 =>
              rw [h2] at heval
              have ih1 := evalFormula_prepend_indep gconf extra assign f1 ms v1 hdisj h1
              have ih2 := evalFormula_prepend_indep gconf extra assign f2 ms v2 hdisj h2
              simp only [evalFormula, ih1, ih2]
              exact heval
  | .iff f1 f2 =>
      simp only [evalFormula] at heval
      cases h1 : evalFormula gconf assign f1 ms with
      | error e => rw [h1] at heval; simp at heval
      | ok v1 =>
          rw [h1] at heval
          cases h2 : evalFormula gconf assign f2 ms with
          | error e => rw [h2] at heval; simp at heval
          | ok v2 =>
              rw [h2] at heval
              have ih1 := evalFormula_prepend_indep gconf extra assign f1 ms v1 hdisj h1
              have ih2 := evalFormula_prepend_indep gconf extra assign f2 ms v2 hdisj h2
              simp only [evalFormula, ih1, ih2]
              exact heval
  | .call name args =>
      simp only [evalFormula] at heval
      cases hfm : fetchMacro gconf ms name with
      | error e => rw [hfm] at heval; simp only [] at heval; exact absurd heval (by simp)
      | ok result =>
          obtain ⟨m, ms'⟩ := result
          rw [hfm] at heval
          simp only [] at heval
          obtain ⟨hname, hmem, hsub⟩ := fetchMacro_sound gconf ms ms' name m hfm
          have hdisj_name : ∀ m' ∈ extra, m'.name ≠ name := by
            intro m' hm' heq
            exact hdisj m' hm' m hmem (heq.trans hname.symm)
          have hfm' : fetchMacro gconf (extra ++ ms) name = Except.ok (m, ms') := by
            rw [fetchMacro_prepend_indep gconf extra ms name hdisj_name, hfm]
          simp only [evalFormula]
          rw [hfm']
          simp only []
          cases hna : newAssignment assign args m.params with
          | error e =>
              rw [hna] at heval
              simp only [] at heval
              exact absurd heval (by simp)
          | ok newAssign =>
              rw [hna] at heval
              simp only [] at heval
              simp only []
              exact heval
  | .anno f1 _ =>
      simp only [evalFormula] at heval
      have ih1 := evalFormula_prepend_indep gconf extra assign f1 ms v hdisj heval
      simp only [evalFormula, ih1]
termination_by sizeOfFormula f
decreasing_by all_goals (simp only [sizeOfFormula]; grind)
end

-- ---------------------------------------------------------------------------
-- Dropping a name-disjoint macro from the *front* of the macro list
-- ---------------------------------------------------------------------------

/-- `fetchMacro`'s search skips straight past a prepended macro that doesn't match the name being
    searched for -- the single-macro specialization of `fetchMacro_prepend_indep`'s hypothesis
    direction, phrased for `::` instead of `++` since every actual use only ever prepends one
    macro at a time. -/
theorem fetchMacro_skip_ne {c : ZKConfig} (gconf : GlobalConfig c) (badMacro : FFMacro c)
    (ms : List (FFMacro c)) (name : String) (hne : badMacro.name ≠ name) :
    fetchMacro gconf (badMacro :: ms) name = fetchMacro gconf ms name := by
  have hbeq : (badMacro.name == name) = false := by simpa using hne
  simp only [fetchMacro, hbeq, Bool.false_eq_true, ↓reduceIte]

-- `t`/`f` never directly calls a macro named `badName`, on any branch (including untaken `.ite`
-- arms) -- unlike `wellFormedTerm`/`wellFormedFormula`, this does *not* recurse into a called
-- macro's own body. It doesn't need to: `evalFormula`'s `.call` case always looks the callee up
-- in whatever macro list `.call` is itself evaluated against, so once that lookup is shown to
-- skip straight past a name-disjoint prepended macro (`fetchMacro_skip_ne`), the *remainder*
-- list handed down to evaluate the callee's body is identical whether or not the extra macro
-- was ever prepended -- the callee's body never sees it, so nothing about what's inside the
-- callee needs to be known here.
mutual
def TermNamesBelow {c : ZKConfig} (t : FFTerm c) (badName : String) : Prop :=
  match t with
  | .val _ | .var _ => True
  | .add a b | .sub a b | .mul a b => TermNamesBelow a badName ∧ TermNamesBelow b badName
  | .neg a => TermNamesBelow a badName
  | .ite f a b => FormulaNamesBelow f badName ∧ TermNamesBelow a badName ∧ TermNamesBelow b badName

def FormulaNamesBelow {c : ZKConfig} (f : FFFormula c) (badName : String) : Prop :=
  match f with
  | .true | .false | .bool _ => True
  | .range t _ _ => TermNamesBelow t badName
  | .eq a b => TermNamesBelow a badName ∧ TermNamesBelow b badName
  | .and a b | .or a b | .imply a b | .iff a b =>
      FormulaNamesBelow a badName ∧ FormulaNamesBelow b badName
  | .not a => FormulaNamesBelow a badName
  | .ite g a b =>
      FormulaNamesBelow g badName ∧ FormulaNamesBelow a badName ∧ FormulaNamesBelow b badName
  | .call name _args => name ≠ badName
  | .anno f1 _ => FormulaNamesBelow f1 badName
end

-- If `t`/`f` never directly calls `badMacro.name`, a successful evaluation against
-- `badMacro :: ms` is also a successful evaluation (with the same result) against `ms` alone --
-- the converse direction `evalTerm_prepend_indep`/`evalFormula_prepend_indep` don't give (those
-- only go small-list-succeeds → big-list-succeeds, which is genuinely one-directional: a `.call`
-- naming the prepended macro would only ever resolve given its presence). Needed for the
-- whole-program correctness argument: shrinking a `TranslatesCorrectly` completeness hypothesis
-- (stated over the *bigger*, already-extended `specs` list) back down to the smaller list a
-- single function's own proof was built against.
mutual
theorem evalTerm_names_below_indep {c : ZKConfig} (gconf : GlobalConfig c) (badMacro : FFMacro c)
    (ms : List (FFMacro c)) (assign : Assignment c) (t : FFTerm c) (v : FF c)
    (hbelow : TermNamesBelow t badMacro.name)
    (heval : evalTerm gconf assign t (badMacro :: ms) = Except.ok v) :
    evalTerm gconf assign t ms = Except.ok v := by
  match t with
  | .val v' => simp only [evalTerm] at heval ⊢; exact heval
  | .var v' => simp only [evalTerm] at heval ⊢; exact heval
  | .add t1 t2 =>
      simp only [TermNamesBelow] at hbelow
      obtain ⟨hb1, hb2⟩ := hbelow
      simp only [evalTerm] at heval
      cases h1 : evalTerm gconf assign t1 (badMacro :: ms) with
      | error e => rw [h1] at heval; simp at heval
      | ok v1 =>
          rw [h1] at heval
          cases h2 : evalTerm gconf assign t2 (badMacro :: ms) with
          | error e => rw [h2] at heval; simp at heval
          | ok v2 =>
              rw [h2] at heval
              injection heval with heval
              have ih1 := evalTerm_names_below_indep gconf badMacro ms assign t1 v1 hb1 h1
              have ih2 := evalTerm_names_below_indep gconf badMacro ms assign t2 v2 hb2 h2
              simp only [evalTerm, ih1, ih2, ← heval]
  | .sub t1 t2 =>
      simp only [TermNamesBelow] at hbelow
      obtain ⟨hb1, hb2⟩ := hbelow
      simp only [evalTerm] at heval
      cases h1 : evalTerm gconf assign t1 (badMacro :: ms) with
      | error e => rw [h1] at heval; simp at heval
      | ok v1 =>
          rw [h1] at heval
          cases h2 : evalTerm gconf assign t2 (badMacro :: ms) with
          | error e => rw [h2] at heval; simp at heval
          | ok v2 =>
              rw [h2] at heval
              injection heval with heval
              have ih1 := evalTerm_names_below_indep gconf badMacro ms assign t1 v1 hb1 h1
              have ih2 := evalTerm_names_below_indep gconf badMacro ms assign t2 v2 hb2 h2
              simp only [evalTerm, ih1, ih2, ← heval]
  | .mul t1 t2 =>
      simp only [TermNamesBelow] at hbelow
      obtain ⟨hb1, hb2⟩ := hbelow
      simp only [evalTerm] at heval
      cases h1 : evalTerm gconf assign t1 (badMacro :: ms) with
      | error e => rw [h1] at heval; simp at heval
      | ok v1 =>
          rw [h1] at heval
          cases h2 : evalTerm gconf assign t2 (badMacro :: ms) with
          | error e => rw [h2] at heval; simp at heval
          | ok v2 =>
              rw [h2] at heval
              injection heval with heval
              have ih1 := evalTerm_names_below_indep gconf badMacro ms assign t1 v1 hb1 h1
              have ih2 := evalTerm_names_below_indep gconf badMacro ms assign t2 v2 hb2 h2
              simp only [evalTerm, ih1, ih2, ← heval]
  | .neg t1 =>
      simp only [TermNamesBelow] at hbelow
      simp only [evalTerm] at heval
      cases h1 : evalTerm gconf assign t1 (badMacro :: ms) with
      | error e => rw [h1] at heval; simp at heval
      | ok v1 =>
          rw [h1] at heval
          injection heval with heval
          have ih1 := evalTerm_names_below_indep gconf badMacro ms assign t1 v1 hbelow h1
          simp only [evalTerm, ih1, ← heval]
  | .ite g t1 t2 =>
      simp only [TermNamesBelow] at hbelow
      obtain ⟨hbg, hb1, hb2⟩ := hbelow
      simp only [evalTerm] at heval
      cases hg : evalFormula gconf assign g (badMacro :: ms) with
      | error e => rw [hg] at heval; simp at heval
      | ok vc =>
          rw [hg] at heval
          have ihg := evalFormula_names_below_indep gconf badMacro ms assign g vc hbg hg
          simp only [evalTerm, ihg]
          cases vc with
          | true => exact evalTerm_names_below_indep gconf badMacro ms assign t1 v hb1 heval
          | false => exact evalTerm_names_below_indep gconf badMacro ms assign t2 v hb2 heval
termination_by sizeOfTerm t
decreasing_by all_goals (simp only [sizeOfTerm]; grind)

theorem evalFormula_names_below_indep {c : ZKConfig} (gconf : GlobalConfig c)
    (badMacro : FFMacro c) (ms : List (FFMacro c)) (assign : Assignment c) (f : FFFormula c)
    (v : Bool) (hbelow : FormulaNamesBelow f badMacro.name)
    (heval : evalFormula gconf assign f (badMacro :: ms) = Except.ok v) :
    evalFormula gconf assign f ms = Except.ok v := by
  match f with
  | .true => simp only [evalFormula] at heval ⊢; exact heval
  | .false => simp only [evalFormula] at heval ⊢; exact heval
  | .range t l u =>
      simp only [FormulaNamesBelow] at hbelow
      simp only [evalFormula] at heval
      cases ht : evalTerm gconf assign t (badMacro :: ms) with
      | error e => rw [ht] at heval; simp at heval
      | ok vt =>
          rw [ht] at heval
          have iht := evalTerm_names_below_indep gconf badMacro ms assign t vt hbelow ht
          simp only [evalFormula, iht]
          exact heval
  | .bool v' => simp only [evalFormula] at heval ⊢; exact heval
  | .eq t1 t2 =>
      simp only [FormulaNamesBelow] at hbelow
      obtain ⟨hb1, hb2⟩ := hbelow
      simp only [evalFormula] at heval
      cases h1 : evalTerm gconf assign t1 (badMacro :: ms) with
      | error e => rw [h1] at heval; simp at heval
      | ok v1 =>
          rw [h1] at heval
          cases h2 : evalTerm gconf assign t2 (badMacro :: ms) with
          | error e => rw [h2] at heval; simp at heval
          | ok v2 =>
              rw [h2] at heval
              have ih1 := evalTerm_names_below_indep gconf badMacro ms assign t1 v1 hb1 h1
              have ih2 := evalTerm_names_below_indep gconf badMacro ms assign t2 v2 hb2 h2
              simp only [evalFormula, ih1, ih2]
              exact heval
  | .and f1 f2 =>
      simp only [FormulaNamesBelow] at hbelow
      obtain ⟨hb1, hb2⟩ := hbelow
      simp only [evalFormula] at heval
      cases h1 : evalFormula gconf assign f1 (badMacro :: ms) with
      | error e => rw [h1] at heval; simp at heval
      | ok v1 =>
          rw [h1] at heval
          cases h2 : evalFormula gconf assign f2 (badMacro :: ms) with
          | error e => rw [h2] at heval; simp at heval
          | ok v2 =>
              rw [h2] at heval
              injection heval with heval
              have ih1 := evalFormula_names_below_indep gconf badMacro ms assign f1 v1 hb1 h1
              have ih2 := evalFormula_names_below_indep gconf badMacro ms assign f2 v2 hb2 h2
              simp only [evalFormula, ih1, ih2, ← heval]
  | .or f1 f2 =>
      simp only [FormulaNamesBelow] at hbelow
      obtain ⟨hb1, hb2⟩ := hbelow
      simp only [evalFormula] at heval
      cases h1 : evalFormula gconf assign f1 (badMacro :: ms) with
      | error e => rw [h1] at heval; simp at heval
      | ok v1 =>
          rw [h1] at heval
          cases h2 : evalFormula gconf assign f2 (badMacro :: ms) with
          | error e => rw [h2] at heval; simp at heval
          | ok v2 =>
              rw [h2] at heval
              injection heval with heval
              have ih1 := evalFormula_names_below_indep gconf badMacro ms assign f1 v1 hb1 h1
              have ih2 := evalFormula_names_below_indep gconf badMacro ms assign f2 v2 hb2 h2
              simp only [evalFormula, ih1, ih2, ← heval]
  | .not f1 =>
      simp only [FormulaNamesBelow] at hbelow
      simp only [evalFormula] at heval
      cases h1 : evalFormula gconf assign f1 (badMacro :: ms) with
      | error e => rw [h1] at heval; simp at heval
      | ok v1 =>
          rw [h1] at heval
          injection heval with heval
          have ih1 := evalFormula_names_below_indep gconf badMacro ms assign f1 v1 hbelow h1
          simp only [evalFormula, ih1, ← heval]
  | .ite g f1 f2 =>
      simp only [FormulaNamesBelow] at hbelow
      obtain ⟨hbg, hb1, hb2⟩ := hbelow
      simp only [evalFormula] at heval
      cases hg : evalFormula gconf assign g (badMacro :: ms) with
      | error e => rw [hg] at heval; simp at heval
      | ok vc =>
          rw [hg] at heval
          have ihg := evalFormula_names_below_indep gconf badMacro ms assign g vc hbg hg
          simp only [evalFormula, ihg]
          cases vc with
          | true => exact evalFormula_names_below_indep gconf badMacro ms assign f1 v hb1 heval
          | false => exact evalFormula_names_below_indep gconf badMacro ms assign f2 v hb2 heval
  | .imply f1 f2 =>
      simp only [FormulaNamesBelow] at hbelow
      obtain ⟨hb1, hb2⟩ := hbelow
      simp only [evalFormula] at heval
      cases h1 : evalFormula gconf assign f1 (badMacro :: ms) with
      | error e => rw [h1] at heval; simp at heval
      | ok v1 =>
          rw [h1] at heval
          cases h2 : evalFormula gconf assign f2 (badMacro :: ms) with
          | error e => rw [h2] at heval; simp at heval
          | ok v2 =>
              rw [h2] at heval
              have ih1 := evalFormula_names_below_indep gconf badMacro ms assign f1 v1 hb1 h1
              have ih2 := evalFormula_names_below_indep gconf badMacro ms assign f2 v2 hb2 h2
              simp only [evalFormula, ih1, ih2]
              exact heval
  | .iff f1 f2 =>
      simp only [FormulaNamesBelow] at hbelow
      obtain ⟨hb1, hb2⟩ := hbelow
      simp only [evalFormula] at heval
      cases h1 : evalFormula gconf assign f1 (badMacro :: ms) with
      | error e => rw [h1] at heval; simp at heval
      | ok v1 =>
          rw [h1] at heval
          cases h2 : evalFormula gconf assign f2 (badMacro :: ms) with
          | error e => rw [h2] at heval; simp at heval
          | ok v2 =>
              rw [h2] at heval
              have ih1 := evalFormula_names_below_indep gconf badMacro ms assign f1 v1 hb1 h1
              have ih2 := evalFormula_names_below_indep gconf badMacro ms assign f2 v2 hb2 h2
              simp only [evalFormula, ih1, ih2]
              exact heval
  | .call name args =>
      simp only [FormulaNamesBelow] at hbelow
      have hne : badMacro.name ≠ name := hbelow.symm
      simp only [evalFormula] at heval
      cases hfm : fetchMacro gconf (badMacro :: ms) name with
      | error e => rw [hfm] at heval; simp at heval
      | ok result =>
          obtain ⟨m, ms'⟩ := result
          rw [hfm] at heval
          simp only [] at heval
          have hfm' : fetchMacro gconf ms name = Except.ok (m, ms') := by
            rw [← fetchMacro_skip_ne gconf badMacro ms name hne, hfm]
          simp only [evalFormula]
          rw [hfm']
          simp only []
          exact heval
  | .anno f1 _ =>
      simp only [FormulaNamesBelow] at hbelow
      simp only [evalFormula] at heval ⊢
      exact evalFormula_names_below_indep gconf badMacro ms assign f1 v hbelow heval
termination_by sizeOfFormula f
decreasing_by all_goals (simp only [sizeOfFormula]; grind)
end

-- ---------------------------------------------------------------------------
-- Well-formedness (a syntactic condition sufficient for totality)
-- ---------------------------------------------------------------------------

/-- `args` and `params` have matching shapes for a macro call: same length,
    and each position pairs an FF/bool parameter with an FF/bool argument
    (variable or constant) of the same kind. This is exactly the condition
    under which `newAssignment'` never hits its "Mismatched variable lists"
    fallback, independent of any assignment. -/
def argsMatchParams {c : ZKConfig} (args : List (MacroCallParam c)) (params : List Var) : Prop :=
  match params, args with
  | [], [] => True
  | (Var.ffv _) :: params', (MacroCallParam.var (Var.ffv _)) :: args' =>
      argsMatchParams args' params'
  | (Var.ffv _) :: params', (MacroCallParam.const (Const.ffc _)) :: args' =>
      argsMatchParams args' params'
  | (Var.boolv _) :: params', (MacroCallParam.var (Var.boolv _)) :: args' =>
      argsMatchParams args' params'
  | (Var.boolv _) :: params', (MacroCallParam.const (Const.boolc _)) :: args' =>
      argsMatchParams args' params'
  | _, _ => False

mutual
/-- `t` is well-formed w.r.t. the macro list `ms`: every macro call occurring
    anywhere in `t` — on every branch of every `.ite`, whether or not that
    branch is ever selected by any assignment — resolves to a macro in `ms`
    whose parameters match the call's arguments in shape. This is a purely
    syntactic condition, independent of any assignment; it's what lets us
    later conclude `evalTerm`/`evalFormula` never error, for *any* assignment,
    without needing to reason about which branches get taken. -/
def wellFormedTerm {c : ZKConfig} (gconf : GlobalConfig c)
    (ms : List (FFMacro c)) (t : FFTerm c) : Prop :=
  match t with
  | .val _     => True
  | .var _     => True
  | .add a b
  | .sub a b
  | .mul a b   => wellFormedTerm gconf ms a ∧ wellFormedTerm gconf ms b
  | .neg a     => wellFormedTerm gconf ms a
  | .ite f a b => wellFormedFormula gconf ms f ∧ wellFormedTerm gconf ms a ∧
                  wellFormedTerm gconf ms b
termination_by (ms.length, sizeOfTerm t)
decreasing_by
  all_goals
    apply Prod.Lex.right
    simp only [sizeOfTerm]
    grind

/-- `f` is well-formed w.r.t. the macro list `ms`: same condition as
    `wellFormedTerm`, extended at `.call` to also require the called macro's
    own body to be well-formed (w.r.t. the remaining macro list, since
    macros are non-recursive — see `fetchMacro`/`fetchMacroLT`). -/
def wellFormedFormula {c : ZKConfig} (gconf : GlobalConfig c)
    (ms : List (FFMacro c)) (f : FFFormula c) : Prop :=
  match f with
  | .true | .false => True
  | .range t _ _    => wellFormedTerm gconf ms t
  | .bool _         => True
  | .eq a b         => wellFormedTerm gconf ms a ∧ wellFormedTerm gconf ms b
  | .and a b
  | .or a b
  | .imply a b
  | .iff a b        => wellFormedFormula gconf ms a ∧ wellFormedFormula gconf ms b
  | .not a          => wellFormedFormula gconf ms a
  | .ite c a b      => wellFormedFormula gconf ms c ∧ wellFormedFormula gconf ms a ∧
                        wellFormedFormula gconf ms b
  | .call name args =>
      match _h_fetchm : fetchMacro gconf ms name with
      | Except.error _ => False
      | Except.ok (m, ms') =>
          argsMatchParams args m.params ∧ wellFormedFormula gconf ms' m.body
  | .anno f1 _ => wellFormedFormula gconf ms f1
termination_by (ms.length, sizeOfFormula f)
decreasing_by
  any_goals
    apply Prod.Lex.right
    simp only [sizeOfFormula]
    grind
  · apply Prod.Lex.left
    apply fetchMacroLT gconf ms ms' name m _h_fetchm

end


-- ---------------------------------------------------------------------------
-- Well-formedness implies totality
-- ---------------------------------------------------------------------------

/-- If `argsMatchParams` holds, `newAssignment'` never hits its "Mismatched
    variable lists" fallback, for any assignment/accumulators. -/
theorem newAssignment'_total {c : ZKConfig} (assign : Assignment c)
    (args : List (MacroCallParam c)) (params : List Var)
    (ffMap : FFVar → FF c) (boolMap : BoolVar → Bool)
    (h : argsMatchParams args params) :
    ∃ res, newAssignment' assign args params ffMap boolMap = Except.ok res := by
  match params, args with
  | [], [] => exact ⟨_, rfl⟩
  | (Var.ffv _p) :: params', (MacroCallParam.var (Var.ffv _n)) :: args' =>
      simp only [newAssignment']
      exact newAssignment'_total assign args' params' _ boolMap h
  | (Var.ffv _p) :: params', (MacroCallParam.const (Const.ffc _t)) :: args' =>
      simp only [newAssignment']
      exact newAssignment'_total assign args' params' _ boolMap h
  | (Var.boolv _p) :: params', (MacroCallParam.var (Var.boolv _n)) :: args' =>
      simp only [newAssignment']
      exact newAssignment'_total assign args' params' ffMap _ h
  | (Var.boolv _p) :: params', (MacroCallParam.const (Const.boolc _t)) :: args' =>
      simp only [newAssignment']
      exact newAssignment'_total assign args' params' ffMap _ h
  | [], (MacroCallParam.var (Var.ffv _)) :: _ => simp only [argsMatchParams] at h
  | [], (MacroCallParam.var (Var.boolv _)) :: _ => simp only [argsMatchParams] at h
  | [], (MacroCallParam.const (Const.ffc _)) :: _ => simp only [argsMatchParams] at h
  | [], (MacroCallParam.const (Const.boolc _)) :: _ => simp only [argsMatchParams] at h
  | (Var.ffv _) :: _, [] => simp only [argsMatchParams] at h
  | (Var.boolv _) :: _, [] => simp only [argsMatchParams] at h
  | (Var.ffv _) :: _, (MacroCallParam.var (Var.boolv _)) :: _ => simp only [argsMatchParams] at h
  | (Var.boolv _) :: _, (MacroCallParam.var (Var.ffv _)) :: _ => simp only [argsMatchParams] at h
  | (Var.ffv _) :: _, (MacroCallParam.const (Const.boolc _)) :: _ =>
      simp only [argsMatchParams] at h
  | (Var.boolv _) :: _, (MacroCallParam.const (Const.ffc _)) :: _ =>
      simp only [argsMatchParams] at h

theorem newAssignment_total {c : ZKConfig} (assign : Assignment c)
    (args : List (MacroCallParam c)) (params : List Var)
    (h : argsMatchParams args params) :
    ∃ res, newAssignment assign args params = Except.ok res :=
  newAssignment'_total assign args params _ _ h

-- `evalTerm`/`evalFormula` never error on a well-formed term/formula, for
-- *any* assignment. Unlike `evalTerm_congr`/`evalFormula_congr`, the `.call`
-- case here genuinely has to recurse into the macro's body (the assignment
-- fed into it, `newAssign`, isn't literally forced to coincide with anything
-- already handled), so this reuses the same `(ms.length, sizeOf...)` +
-- `fetchMacroLT` termination technique as `evalTerm`/`evalFormula` themselves.
mutual
theorem evalTerm_total {c : ZKConfig}
    (gconf : GlobalConfig c) (ms : List (FFMacro c)) (t : FFTerm c)
    (hwf : wellFormedTerm gconf ms t) (rho : Assignment c) :
    ∃ v, evalTerm gconf rho t ms = Except.ok v := by
  match t with
  | .val v => exact ⟨v, by simp only [evalTerm]⟩
  | .var v => exact ⟨rho.ff v, by simp only [evalTerm]⟩
  | .add t1 t2 =>
      simp only [wellFormedTerm] at hwf
      obtain ⟨v1, hv1⟩ := evalTerm_total gconf ms t1 hwf.1 rho
      obtain ⟨v2, hv2⟩ := evalTerm_total gconf ms t2 hwf.2 rho
      exact ⟨v1 + v2, by simp only [evalTerm, hv1, hv2]⟩
  | .sub t1 t2 =>
      simp only [wellFormedTerm] at hwf
      obtain ⟨v1, hv1⟩ := evalTerm_total gconf ms t1 hwf.1 rho
      obtain ⟨v2, hv2⟩ := evalTerm_total gconf ms t2 hwf.2 rho
      exact ⟨v1 - v2, by simp only [evalTerm, hv1, hv2]⟩
  | .mul t1 t2 =>
      simp only [wellFormedTerm] at hwf
      obtain ⟨v1, hv1⟩ := evalTerm_total gconf ms t1 hwf.1 rho
      obtain ⟨v2, hv2⟩ := evalTerm_total gconf ms t2 hwf.2 rho
      exact ⟨v1 * v2, by simp only [evalTerm, hv1, hv2]⟩
  | .neg t1 =>
      simp only [wellFormedTerm] at hwf
      obtain ⟨v1, hv1⟩ := evalTerm_total gconf ms t1 hwf rho
      exact ⟨-v1, by simp only [evalTerm, hv1]⟩
  | .ite g t1 t2 =>
      simp only [wellFormedTerm] at hwf
      obtain ⟨hwfg, hwf1, hwf2⟩ := hwf
      obtain ⟨vg, hvg⟩ := evalFormula_total gconf ms g hwfg rho
      cases vg with
      | true =>
          simp only [evalTerm, hvg, if_true]
          exact evalTerm_total gconf ms t1 hwf1 rho
      | false =>
          simp only [evalTerm, hvg]
          exact evalTerm_total gconf ms t2 hwf2 rho
termination_by (ms.length, sizeOfTerm t)
decreasing_by
  all_goals
    apply Prod.Lex.right
    simp only [sizeOfTerm]
    omega

theorem evalFormula_total {c : ZKConfig}
    (gconf : GlobalConfig c) (ms : List (FFMacro c)) (f : FFFormula c)
    (hwf : wellFormedFormula gconf ms f) :
    isTotal gconf f ms := by
  intro rho
  match f with
  | .true  => exact ⟨true, by simp only [evalFormula]⟩
  | .false => exact ⟨false, by simp only [evalFormula]⟩
  | .range t _l _u =>
      simp only [wellFormedFormula] at hwf
      obtain ⟨v, hv⟩ := evalTerm_total gconf ms t hwf rho
      simp only [evalFormula, hv]
      exact ⟨_, rfl⟩
  | .bool v => exact ⟨rho.bool v, by simp only [evalFormula]⟩
  | .eq t1 t2 =>
      simp only [wellFormedFormula] at hwf
      obtain ⟨v1, hv1⟩ := evalTerm_total gconf ms t1 hwf.1 rho
      obtain ⟨v2, hv2⟩ := evalTerm_total gconf ms t2 hwf.2 rho
      simp only [evalFormula, hv1, hv2]
      exact ⟨_, rfl⟩
  | .and f1 f2 =>
      simp only [wellFormedFormula] at hwf
      obtain ⟨v1, hv1⟩ := evalFormula_total gconf ms f1 hwf.1 rho
      obtain ⟨v2, hv2⟩ := evalFormula_total gconf ms f2 hwf.2 rho
      exact ⟨v1 && v2, by simp only [evalFormula, hv1, hv2]⟩
  | .or f1 f2 =>
      simp only [wellFormedFormula] at hwf
      obtain ⟨v1, hv1⟩ := evalFormula_total gconf ms f1 hwf.1 rho
      obtain ⟨v2, hv2⟩ := evalFormula_total gconf ms f2 hwf.2 rho
      exact ⟨v1 || v2, by simp only [evalFormula, hv1, hv2]⟩
  | .not f1 =>
      simp only [wellFormedFormula] at hwf
      obtain ⟨v1, hv1⟩ := evalFormula_total gconf ms f1 hwf rho
      exact ⟨!v1, by simp only [evalFormula, hv1]⟩
  | .ite g f1 f2 =>
      simp only [wellFormedFormula] at hwf
      obtain ⟨hwfg, hwf1, hwf2⟩ := hwf
      obtain ⟨vg, hvg⟩ := evalFormula_total gconf ms g hwfg rho
      cases vg with
      | true =>
          simp only [evalFormula, hvg, if_true]
          exact evalFormula_total gconf ms f1 hwf1 rho
      | false =>
          simp only [evalFormula, hvg]
          exact evalFormula_total gconf ms f2 hwf2 rho
  | .imply f1 f2 =>
      simp only [wellFormedFormula] at hwf
      obtain ⟨v1, hv1⟩ := evalFormula_total gconf ms f1 hwf.1 rho
      obtain ⟨v2, hv2⟩ := evalFormula_total gconf ms f2 hwf.2 rho
      exact ⟨!v1 || v2, by simp only [evalFormula, hv1, hv2]⟩
  | .iff f1 f2 =>
      simp only [wellFormedFormula] at hwf
      obtain ⟨v1, hv1⟩ := evalFormula_total gconf ms f1 hwf.1 rho
      obtain ⟨v2, hv2⟩ := evalFormula_total gconf ms f2 hwf.2 rho
      exact ⟨v1 == v2, by simp only [evalFormula, hv1, hv2]⟩
  | .call name args =>
      simp only [wellFormedFormula] at hwf
      match hfm : fetchMacro gconf ms name with
      | Except.error e =>
          rw [hfm] at hwf
          exact absurd hwf (by simp)
      | Except.ok (m, ms') =>
          rw [hfm] at hwf
          dsimp only at hwf
          obtain ⟨hargs, hbody⟩ := hwf
          obtain ⟨newAssign, hna⟩ := newAssignment_total rho args m.params hargs
          obtain ⟨v, hv⟩ := evalFormula_total gconf ms' m.body hbody newAssign
          refine ⟨v, ?_⟩
          simp only [evalFormula]
          split
          · rename_i e heq2
            rw [hfm] at heq2
            cases heq2
          · rename_i m2 ms'2 heq2
            rw [hfm] at heq2
            obtain ⟨hm, hms'⟩ := Prod.mk.injEq .. |>.mp (Except.ok.injEq .. |>.mp heq2)
            subst hm; subst hms'
            simp only [hna, hv]
  | .anno f1 _ =>
      simp only [wellFormedFormula] at hwf
      obtain ⟨v1, hv1⟩ := evalFormula_total gconf ms f1 hwf rho
      exact ⟨v1, by simp only [evalFormula, hv1]⟩
termination_by (ms.length, sizeOfFormula f)
decreasing_by
  any_goals
    apply Prod.Lex.right
    simp only [sizeOfFormula]
    omega
  · apply Prod.Lex.left
    apply fetchMacroLT gconf ms ms' name m hfm
end

end Corellzk2smt.FFConstraints.Satisfiability_th
