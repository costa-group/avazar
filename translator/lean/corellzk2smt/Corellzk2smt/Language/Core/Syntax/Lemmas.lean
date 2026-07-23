import Corellzk2smt.Basic
import Corellzk2smt.Config
import Corellzk2smt.Language.Core.Syntax.AST

/-!
Proof-support lemmas about `AST.lean`'s definitions -- kept out of `AST.lean` itself since
`AST.lean` is imported by the parser/printer (hence part of the `corellzk2smt_cli` executable),
while these facts are only ever consumed by `SymExec/Correctness/*` and the concrete reference
semantics used to state correctness. `sizeOfComs_a_lt_a_plus_b` stayed behind in `AST.lean` despite
being a theorem, not a `def` -- it's genuinely used by `SymExec/BigStep.lean`'s own termination
proof (real computation, not just reasoning about it), so moving it here would just force the
implementation file to import this one instead, buying nothing.
-/

namespace Corellzk2smt.Language.Core.Syntax.Lemmas

open Corellzk2smt.Language.Core.Syntax.AST

/-- A name list with no duplicates still has none after dropping a prefix -- needed to carry a
    whole-program "no duplicate function names" fact down to a sub-program. -/
theorem hasDupNames_append_right (l1 l2 : List VarID) (h : hasDupNames (l1 ++ l2) = false) :
    hasDupNames l2 = false := by
  induction l1 with
  | nil => simpa using h
  | cons a l1' ih =>
      simp only [List.cons_append, hasDupNames, Bool.or_eq_false_iff] at h
      exact ih h.2

/-- `hasDupFuncNames`, for a sub-program at the end of a bigger one -- see
    `hasDupNames_append_right`. -/
theorem hasDupFuncNames_append_right {c : ZKConfig} (p1 p2 : Prog c)
    (h : hasDupFuncNames (p1 ++ p2) = false) : hasDupFuncNames p2 = false := by
  simp only [hasDupFuncNames, List.map_append] at h ⊢
  exact hasDupNames_append_right _ _ h

/-- A name list with no duplicates has its two halves (around any split point) pairwise
    disjoint -- the general form of what `hasDupFuncNames_cons_disjoint`-style reasoning needs,
    for an arbitrary prefix rather than just a single head element. -/
theorem hasDupNames_append_disjoint (l1 l2 : List VarID) (h : hasDupNames (l1 ++ l2) = false) :
    ∀ x ∈ l1, x ∉ l2 := by
  induction l1 with
  | nil => intro x hx; exact absurd hx List.not_mem_nil
  | cons a l1' ih =>
      simp only [List.cons_append, hasDupNames, Bool.or_eq_false_iff] at h
      intro x hx hxl2
      rcases List.mem_cons.mp hx with heq | hmem
      · subst heq
        have hmemapp : x ∈ l1' ++ l2 := List.mem_append_right _ hxl2
        have hcontains : (l1' ++ l2).contains x = true := List.contains_iff_mem.mpr hmemapp
        rw [h.1] at hcontains
        exact absurd hcontains (by simp)
      · exact ih h.2 x hmem hxl2

/-- `hasDupNames_append_disjoint`, lifted to whole-program function names. -/
theorem hasDupFuncNames_append_disjoint {c : ZKConfig} (p1 p2 : Prog c)
    (h : hasDupFuncNames (p1 ++ p2) = false) :
    ∀ f ∈ p1, funcWithMDName f ∉ p2.map funcWithMDName := by
  simp only [hasDupFuncNames, List.map_append] at h
  intro f hf
  exact hasDupNames_append_disjoint _ _ h (funcWithMDName f) (List.mem_map_of_mem hf)

/-- `hasDupFuncNames`, for the tail of a `::` -- the `p1 := [f]` case of
    `hasDupFuncNames_append_right`. -/
theorem hasDupFuncNames_cons_tail {c : ZKConfig} (f : FuncWithMD c) (p : Prog c)
    (h : hasDupFuncNames (f :: p) = false) : hasDupFuncNames p = false :=
  hasDupFuncNames_append_right [f] p h

/- fetchFunc returns a smaller program. It is used to prove termination
   of the functions representing the semantics.
-/
theorem fetchLT {c : ZKConfig}
  (p : Prog c) (fname : FName) (f : FuncWithMD c) (p' : Prog c) :
  fetchFunc p fname = Except.ok (f, p') → p'.length < p.length := by
  cases p with
  | nil => simp [fetchFunc]
  | cons func fs =>
    match func with
    | .mk _ f' =>
      match f' with
      | .mk name params rets body =>
        simp only [fetchFunc]
        by_cases hname : name = fname
        · simp only [hname]
          simp only [BEq.rfl, List.length_cons]
          simp only [if_true]
          intro h_eq
          injection h_eq with h_inner
          injection h_inner with h_func h_prog
          rw [h_prog]
          apply Nat.le_refl
        · simp only [beq_iff_eq, hname, List.length_cons]
          simp only [if_false]
          intro h1
          have h2 := fetchLT fs fname f p' h1
          apply Nat.lt_of_lt_of_le h2
          apply Nat.le_succ

/-- `fetchFunc` succeeds for any name actually present among the program's function names --
    the converse of what a success witness already gives (`fetchFunc`'s result is always *some*
    function named `fname`), needed to turn "`fname` is a name in this program" into an actual
    fetch witness without separately assuming the fetch succeeds. -/
theorem fetchFunc_of_mem {c : ZKConfig} (p : Prog c) (fname : FName)
    (h : fname ∈ p.map funcWithMDName) :
    ∃ (md : FuncMD) (func : Func c) (p' : Prog c),
      fetchFunc p fname = Except.ok (FuncWithMD.mk md func, p') := by
  induction p with
  | nil => simp at h
  | cons f fs ih =>
      obtain ⟨md, func⟩ := f
      cases func with
      | mk name params rets body =>
          simp only [fetchFunc]
          by_cases hcase : name = fname
          · subst hcase
            simp only [BEq.rfl, ↓reduceIte]
            exact ⟨md, Func.mk name params rets body, fs, rfl⟩
          · have hbeq : (name == fname) = false := by simpa using hcase
            simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
            apply ih
            simp only [List.map_cons, funcWithMDName] at h
            rcases List.mem_cons.mp h with h1 | h2
            · exact absurd h1.symm hcase
            · exact h2

theorem sizeOfCom_pos {c : ZKConfig} (cmd : ComWithMD c) :
  sizeOfCom cmd > 0 := by
  cases cmd with
  | mk _ info =>
    match info with
    | .if_stmt _ tb eb => simp only [sizeOfCom]; grind
    | .loop_exp _ body => simp only [sizeOfCom]; grind
    | .loop rep body => simp only [sizeOfCom]; grind
    | .assign _ _ => simp only [sizeOfCom]; grind
    | .new_array _ _ => simp only [sizeOfCom]; grind
    | .read_array _ _ _ => simp only [sizeOfCom]; grind
    | .write_array _ _ _ => simp only [sizeOfCom]; grind
    | .copy_array _ _ => simp only [sizeOfCom]; grind
    | .func_call _ _ _ => simp only [sizeOfCom]; grind

end Corellzk2smt.Language.Core.Syntax.Lemmas
