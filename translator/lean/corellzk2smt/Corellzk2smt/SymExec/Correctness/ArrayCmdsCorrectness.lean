import Corellzk2smt.SymExec.Correctness.Lemmas
import Corellzk2smt.SymExec.Correctness.FuncCallCorrectness
import Corellzk2smt.SymExec.Correctness.BinaryExpansionCorrectness

/-!
Correctness statements for the four array operations in `SymExec/ArrayCmds.lean`
(`seNewArray`/`seReadArray`/`seWriteArray`/`seCopyArray`) against their concrete counterparts in
`Language/Core/Semantics/Basic.lean`. `seReadArray`/`seWriteArray`/`seCopyArray` are currently
permanent `"TBD"` stubs, so those three are left as honest `sorry`s -- see
`SimpleCmdCorrectness.lean`, which composes these together with `AssignmentCorrectness.lean`'s
theorem into `H_simple_holds`. `seNewArray` is implemented and proved below.
-/

namespace Corellzk2smt.SymExec.Correctness.ArrayCmdsCorrectness

open Corellzk2smt.Config
open Corellzk2smt.Language.Core.Syntax.AST
open Corellzk2smt.Language.Core.Semantics.Basic
open Corellzk2smt.SymExec.Basic
open Corellzk2smt.SymExec.BigStep
open Corellzk2smt.FFConstraints.Basic
open Corellzk2smt.FFConstraints.Satisfiability
open Corellzk2smt.SymExec.Correctness.Lemmas
open Corellzk2smt.SymExec.Correctness.FuncCallCorrectness
open Corellzk2smt.SymExec.Correctness.BinaryExpansionCorrectness

/-- Every element of `List.replicate n a` is (definitionally) `a`. -/
private theorem eq_of_mem_replicate {α : Type} (n : Nat) (a x : α)
    (hx : x ∈ List.replicate n a) : x = a := by
  induction n with
  | zero => simp at hx
  | succ n ih =>
      rw [List.replicate_succ, List.mem_cons] at hx
      rcases hx with h | h
      · exact h
      · exact ih h

/-- A brand new all-zero-constant array (as built by both `seNewArray`/`evalNewArray`) never
    contributes any constraint variable -- every element is `.const 0`, and `simpleValVars` of a
    constant is empty. -/
private theorem symValVars_replicate_const_array {c : ZKConfig} (n : Nat) (v' : FF c) (var : Var)
    (hv : var ∈ symValVars (SymValue.array (List.replicate n (SimpleSymVal.const v')).toArray)) :
    False := by
  simp only [symValVars] at hv
  rw [← Array.foldl_toList, List.toList_toArray] at hv
  rcases foldl_union_mem_elim simpleValVars (List.replicate n (SimpleSymVal.const v'))
      emptyVarSet var hv with h | h
  · exact absurd h Std.TreeSet.not_mem_emptyc
  · obtain ⟨x, hx, hvx⟩ := h
    rw [eq_of_mem_replicate n (SimpleSymVal.const v') x hx] at hvx
    simp only [simpleValVars] at hvx
    exact absurd hvx Std.TreeSet.not_mem_emptyc

/-- The symbolic all-zero-constant array matches the concrete all-zero array, for any
    assignment: pointwise, every `.const 0` matches `(0 : FF c)` regardless of the assignment. -/
private theorem symValMatches_replicate_const_array {c : ZKConfig} (assignment : Assignment c)
    (n : Nat) (v : FF c) :
    symValMatches assignment
      (SymValue.array (List.replicate n (SimpleSymVal.const v)).toArray)
      (Value.array (List.replicate n v).toArray) := by
  simp only [symValMatches, List.toList_toArray]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, List.replicate_succ]
      exact List.Forall₂.cons (by simp [simpleValMatches]) ih

/-- `seNewArray` correctly translates `evalNewArray` -- both mint no fresh constraint variable and
    no formula content (`f := .true`): the only thing that happens is inserting a matching
    brand-new all-zero array (symbolic `.const 0`s, concrete `(0 : FF c)`s, same length, since both
    sides compute that length from `size` via `tryEvalSimpleExprToFFValue`/`evalSimpleExprToFFValue`
    and those agree under a matching environment). -/
theorem seNewArray_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD) (id : VarID) (size : SimpleExpr c) :
    TranslatesCorrectly gconf sconf specs ctx
      (fun env => evalNewArray md gconf env id size)
      (fun symEnv => seNewArray md gconf sconf symEnv specs id size) := by
  intro symEnv hbelow _hvalid spec hspec_eq
  cases hsize : tryEvalSimpleExprToFFValue symEnv size with
  | error msg => simp [seNewArray, hsize] at hspec_eq
  | ok sizeValue =>
      simp only [seNewArray, hsize] at hspec_eq
      injection hspec_eq with hspec_eq
      subst hspec_eq
      refine ⟨rfl, le_refl _, ?_, ?_, ?_, ?_, ValidBinRep_trivial gconf _ _, ?_, ?_⟩
      · intro v' hv'
        rcases Std.TreeSet.mem_union_iff.mp hv' with h | h <;>
          simp only [ffVarsOfFormula, bVarsOfFormula] at h <;>
          exact absurd h Std.TreeSet.not_mem_emptyc
      · intro v' hv'
        rcases Std.TreeSet.mem_union_iff.mp hv' with h | h <;>
          simp only [ffVarsOfFormula, bVarsOfFormula] at h <;>
          exact absurd h Std.TreeSet.not_mem_emptyc
      · intro v' hv'
        rcases symEnvVars_setVar_subset symEnv id
            (SymValue.array (List.replicate sizeValue.val (SimpleSymVal.const (0 : FF c))).toArray)
            v' hv' with h | h
        · exact hbelow v' h
        · exact (symValVars_replicate_const_array sizeValue.val (0 : FF c) v' h).elim
      · intro v' hv'
        rcases symEnvVars_setVar_subset symEnv id
            (SymValue.array (List.replicate sizeValue.val (SimpleSymVal.const (0 : FF c))).toArray)
            v' hv' with h | h
        · exact Or.inl h
        · exact (symValVars_replicate_const_array sizeValue.val (0 : FF c) v' h).elim
      · intro env assignment hmatch env' hc
        have hceval := tryEvalSimpleExprToFFValue_correct symEnv size env assignment sizeValue
          hmatch hsize
        simp only [evalNewArray, hceval] at hc
        injection hc with hc
        refine ⟨assignment, (fun n _ => rfl), (fun n _ => rfl), (fun n _ => rfl),
          (fun n _ => rfl), ?_, ?_⟩
        · simp only [evalFormula]
        · rw [← hc]
          exact EnvMatches_setVar assignment symEnv env id
            (SymValue.array (List.replicate sizeValue.val (SimpleSymVal.const (0 : FF c))).toArray)
            (Value.array (List.replicate sizeValue.val (0 : FF c)).toArray) hmatch
            (symValMatches_replicate_const_array assignment sizeValue.val 0)
      · intro env assignment hmatch assignment' hagree _heval_f
        have hmatch' := EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagree
          hmatch
        have hceval := tryEvalSimpleExprToFFValue_correct symEnv size env assignment' sizeValue
          hmatch' hsize
        refine ⟨Corellzk2smt.Language.Core.Semantics.Basic.setVar env id
          (Value.array (List.replicate sizeValue.val (0 : FF c)).toArray), ?_, ?_⟩
        · simp only [evalNewArray, hceval]
        · exact EnvMatches_setVar assignment' symEnv env id
            (SymValue.array (List.replicate sizeValue.val (SimpleSymVal.const (0 : FF c))).toArray)
            (Value.array (List.replicate sizeValue.val (0 : FF c)).toArray) hmatch'
            (symValMatches_replicate_const_array assignment' sizeValue.val 0)

/-- Pointwise access into `List.Forall₂`: if the relation holds between two lists, it holds
    between their elements at any shared valid index. -/
private theorem list_forall2_get {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 →
      ∀ (i : Nat) (h1 : i < l1.length) (h2 : i < l2.length), R (l1[i]'h1) (l2[i]'h2) := by
  intro l1 l2 h
  induction h with
  | nil => intro i h1 _; simp at h1
  | cons hd _tl ih =>
      intro i h1 h2
      cases i with
      | zero => exact hd
      | succ i => exact ih i (by simpa using h1) (by simpa using h2)

/-- `seReadArrayConstantIdx` correctly translates `evalReadArray`, when it succeeds -- it only
    ever succeeds when the index resolves to a constant and `a` is bound to an array with that
    index in bounds. The fresh binding at `out` copies whatever value is already stored at
    `a[indexValue.val]`, so `EnvMatches` for the new `outSymEnv` reduces to the pointwise match
    `EnvMatches` already gives for that array element (via `List.Forall₂`), not anything new. -/
theorem seReadArrayConstantIdx_correct {c : ZKConfig} (gconf : GlobalConfig c)
    (specs : List (FuncSpec c)) (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD)
    (out a : VarID) (index : SimpleExpr c) :
    TranslatesCorrectly gconf sconf specs ctx
      (fun env => evalReadArray md gconf env out a index)
      (fun symEnv => seReadArrayConstantIdx md gconf sconf symEnv specs out a index) := by
  intro symEnv hbelow _hvalid spec hspec_eq
  cases hidx : tryEvalSimpleExprToFFValue symEnv index with
  | error msg => simp [seReadArrayConstantIdx, hidx] at hspec_eq
  | ok indexValue =>
      cases hg : symEnv.get? a with
      | none =>
          simp [seReadArrayConstantIdx, hidx, Corellzk2smt.SymExec.Basic.getVar,
            ← Std.TreeMap.get?_eq_getElem?, hg] at hspec_eq
      | some symVal =>
          cases symVal with
          | simple sv =>
              simp [seReadArrayConstantIdx, hidx, Corellzk2smt.SymExec.Basic.getVar,
                ← Std.TreeMap.get?_eq_getElem?, hg] at hspec_eq
          | array arr =>
              by_cases h : indexValue.val < arr.size
              · simp only [seReadArrayConstantIdx, hidx, Corellzk2smt.SymExec.Basic.getVar,
                  ← Std.TreeMap.get?_eq_getElem?, hg, dif_pos h] at hspec_eq
                injection hspec_eq with hspec_eq
                subst hspec_eq
                have hsub_arr : symValVars (SymValue.array arr) ⊆ symEnvVars symEnv :=
                  symValVars_subset_symEnvVars symEnv a (SymValue.array arr) hg
                have hmemArr : arr[indexValue.val]'h ∈ arr.toList :=
                  Array.getElem_mem_toList h
                have hsub_val : simpleValVars (arr[indexValue.val]'h) ⊆ symEnvVars symEnv :=
                  symValVars_array_mem_below_subset arr (arr[indexValue.val]'h) hmemArr
                    (symEnvVars symEnv) hsub_arr
                refine ⟨rfl, le_refl _, ?_, ?_, ?_, ?_, ValidBinRep_trivial gconf _ _, ?_, ?_⟩
                · intro v' hv'
                  rcases Std.TreeSet.mem_union_iff.mp hv' with h' | h' <;>
                    simp only [ffVarsOfFormula, bVarsOfFormula] at h' <;>
                    exact absurd h' Std.TreeSet.not_mem_emptyc
                · intro v' hv'
                  rcases Std.TreeSet.mem_union_iff.mp hv' with h' | h' <;>
                    simp only [ffVarsOfFormula, bVarsOfFormula] at h' <;>
                    exact absurd h' Std.TreeSet.not_mem_emptyc
                · intro v' hv'
                  rcases symEnvVars_setVar_subset symEnv out
                      (SymValue.simple (arr[indexValue.val]'h)) v' hv' with h' | h'
                  · exact hbelow v' h'
                  · exact hbelow v' (hsub_val v' h')
                · intro v' hv'
                  rcases symEnvVars_setVar_subset symEnv out
                      (SymValue.simple (arr[indexValue.val]'h)) v' hv' with h' | h'
                  · exact Or.inl h'
                  · exact Or.inl (hsub_val v' h')
                · intro env assignment hmatch env' hc
                  have hpoint := hmatch.2
                  obtain ⟨v, henv, hvv⟩ := hpoint a (SymValue.array arr) hg
                  cases v with
                  | scalar _ => simp only [symValMatches] at hvv
                  | array varr =>
                      simp only [symValMatches] at hvv
                      have hlen : arr.toList.length = varr.toList.length := hvv.length_eq
                      simp only [Array.length_toList] at hlen
                      have h' : indexValue.val < varr.size := by omega
                      have hceval := tryEvalSimpleExprToFFValue_correct symEnv index env
                        assignment indexValue hmatch hidx
                      simp only [evalReadArray, Corellzk2smt.Language.Core.Semantics.Basic.getVar, hceval, henv,
                        ← Std.TreeMap.get?_eq_getElem?, dif_pos h'] at hc
                      injection hc with hc
                      have hmatchElem : simpleValMatches assignment (arr[indexValue.val]'h)
                          (varr[indexValue.val]'h') :=
                        list_forall2_get hvv indexValue.val
                          (by simp only [Array.length_toList]; exact h)
                          (by simp only [Array.length_toList]; exact h')
                      refine ⟨assignment, (fun n _ => rfl), (fun n _ => rfl), (fun n _ => rfl),
                        (fun n _ => rfl), ?_, ?_⟩
                      · simp only [evalFormula]
                      · rw [← hc]
                        exact EnvMatches_setVar assignment symEnv env out
                          (SymValue.simple (arr[indexValue.val]'h))
                          (Value.scalar (varr[indexValue.val]'h')) hmatch hmatchElem
                · intro env assignment hmatch assignment' hagree _heval_f
                  have hmatch' := EnvMatches_agreesOnFF_preserves assignment assignment' symEnv
                    env hagree hmatch
                  have hpoint := hmatch'.2
                  obtain ⟨v, henv, hvv⟩ := hpoint a (SymValue.array arr) hg
                  cases v with
                  | scalar _ => simp only [symValMatches] at hvv
                  | array varr =>
                      simp only [symValMatches] at hvv
                      have hlen : arr.toList.length = varr.toList.length := hvv.length_eq
                      simp only [Array.length_toList] at hlen
                      have h' : indexValue.val < varr.size := by omega
                      have hceval := tryEvalSimpleExprToFFValue_correct symEnv index env
                        assignment' indexValue hmatch' hidx
                      have hmatchElem : simpleValMatches assignment' (arr[indexValue.val]'h)
                          (varr[indexValue.val]'h') :=
                        list_forall2_get hvv indexValue.val
                          (by simp only [Array.length_toList]; exact h)
                          (by simp only [Array.length_toList]; exact h')
                      refine ⟨Corellzk2smt.Language.Core.Semantics.Basic.setVar env out
                        (Value.scalar (varr[indexValue.val]'h')), ?_, ?_⟩
                      · simp only [evalReadArray, Corellzk2smt.Language.Core.Semantics.Basic.getVar, hceval,
                          henv, ← Std.TreeMap.get?_eq_getElem?, dif_pos h']
                      · exact EnvMatches_setVar assignment' symEnv env out
                          (SymValue.simple (arr[indexValue.val]'h))
                          (Value.scalar (varr[indexValue.val]'h')) hmatch' hmatchElem
              · simp [seReadArrayConstantIdx, hidx, Corellzk2smt.SymExec.Basic.getVar,
                  ← Std.TreeMap.get?_eq_getElem?, hg, dif_neg h] at hspec_eq

/-- `seReadArray` correctly translates `evalReadArray` -- pure dispatch: `seReadArray` tries
    `seReadArrayConstantIdx` first and only ever falls back to `seReadArrayNonConstantIdx`, which
    is a permanent `"TBD"` stub, so `seReadArray`'s success cases coincide exactly with
    `seReadArrayConstantIdx`'s own. -/
theorem seReadArray_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD) (out a : VarID)
    (index : SimpleExpr c) :
    TranslatesCorrectly gconf sconf specs ctx
      (fun env => evalReadArray md gconf env out a index)
      (fun symEnv => seReadArray md gconf sconf symEnv specs out a index) := by
  intro symEnv hbelow hvalid spec hspec_eq
  simp only [seReadArray] at hspec_eq
  cases hconst : seReadArrayConstantIdx md gconf sconf symEnv specs out a index with
  | ok spec' =>
      rw [hconst] at hspec_eq
      injection hspec_eq with hspec_eq
      subst hspec_eq
      exact seReadArrayConstantIdx_correct gconf specs sconf ctx md out a index symEnv hbelow
        hvalid spec' hconst
  | error msg =>
      rw [hconst] at hspec_eq
      simp [seReadArrayNonConstantIdx] at hspec_eq

/-- `List.Forall₂` is preserved under simultaneously setting the same index on both lists, when
    the new elements are also `R`-related -- lets a symbolic array write's updated array stay
    matched with the concrete array's updated version. -/
private theorem list_forall2_set {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, List.Forall₂ R l1 l2 →
      ∀ (i : Nat) (x : α) (y : β), R x y → List.Forall₂ R (l1.set i x) (l2.set i y) := by
  intro l1 l2 h
  induction h with
  | nil => intro i x y _hxy; simp
  | cons hd tl ih =>
      intro i x y hxy
      cases i with
      | zero => exact List.Forall₂.cons hxy tl
      | succ i => exact List.Forall₂.cons hd (ih i x y hxy)

/-- `seWriteArrayConstantIdx` correctly translates `evalWriteArray`, when it succeeds -- it only
    ever succeeds when the index resolves to a constant, `a` is bound to an array with that index
    in bounds, and `value` resolves. The updated array (`arr.set indexValue.val v`) stays matched
    with the concrete updated array, since every untouched position keeps the match `EnvMatches`
    already gives (via `List.Forall₂`/`list_forall2_set`), and the touched position matches by
    `resolveSimpleExpr_correct`. -/
theorem seWriteArrayConstantIdx_correct {c : ZKConfig} (gconf : GlobalConfig c)
    (specs : List (FuncSpec c)) (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD)
    (a : VarID) (index value : SimpleExpr c) :
    TranslatesCorrectly gconf sconf specs ctx
      (fun env => evalWriteArray md gconf env a index value)
      (fun symEnv => seWriteArrayConstantIdx md gconf sconf symEnv specs a index value) := by
  intro symEnv hbelow _hvalid spec hspec_eq
  cases hidx : tryEvalSimpleExprToFFValue symEnv index with
  | error msg => simp [seWriteArrayConstantIdx, hidx] at hspec_eq
  | ok indexValue =>
      cases hg : symEnv.get? a with
      | none =>
          simp [seWriteArrayConstantIdx, hidx, Corellzk2smt.SymExec.Basic.getVar,
            ← Std.TreeMap.get?_eq_getElem?, hg] at hspec_eq
      | some symVal =>
          cases symVal with
          | simple sv =>
              simp [seWriteArrayConstantIdx, hidx, Corellzk2smt.SymExec.Basic.getVar,
                ← Std.TreeMap.get?_eq_getElem?, hg] at hspec_eq
          | array arr =>
              by_cases h : indexValue.val < arr.size
              · cases hval : resolveSimpleExpr symEnv value with
                | error msg =>
                    simp [seWriteArrayConstantIdx, hidx, Corellzk2smt.SymExec.Basic.getVar,
                      ← Std.TreeMap.get?_eq_getElem?, hg, dif_pos h, hval] at hspec_eq
                | ok v =>
                    simp only [seWriteArrayConstantIdx, hidx, Corellzk2smt.SymExec.Basic.getVar,
                      ← Std.TreeMap.get?_eq_getElem?, hg, dif_pos h, hval] at hspec_eq
                    injection hspec_eq with hspec_eq
                    subst hspec_eq
                    have hsub_arr : symValVars (SymValue.array arr) ⊆ symEnvVars symEnv :=
                      symValVars_subset_symEnvVars symEnv a (SymValue.array arr) hg
                    have hsub_v : simpleValVars v ⊆ symEnvVars symEnv :=
                      Corellzk2smt.SymExec.Correctness.Lemmas.resolveSimpleExpr_vars_subset symEnv
                        value v hval
                    have hsub_newArr : symValVars
                        (SymValue.array (arr.set indexValue.val v)) ⊆ symEnvVars symEnv := by
                      intro v' hv'
                      simp only [symValVars] at hv'
                      rw [← Array.foldl_toList] at hv'
                      rcases foldl_union_mem_elim simpleValVars
                          (arr.set indexValue.val v).toList emptyVarSet v' hv' with hh | hh
                      · exact absurd hh Std.TreeSet.not_mem_emptyc
                      · obtain ⟨x, hx, hvx⟩ := hh
                        rw [Array.toList_set] at hx
                        rcases List.mem_or_eq_of_mem_set hx with hx' | hx'
                        · exact symValVars_array_mem_below_subset arr x hx' (symEnvVars symEnv)
                            hsub_arr v' hvx
                        · rw [hx'] at hvx
                          exact hsub_v v' hvx
                    refine ⟨rfl, le_refl _, ?_, ?_, ?_, ?_, ValidBinRep_trivial gconf _ _, ?_, ?_⟩
                    · intro v' hv'
                      rcases Std.TreeSet.mem_union_iff.mp hv' with hh | hh <;>
                        simp only [ffVarsOfFormula, bVarsOfFormula] at hh <;>
                        exact absurd hh Std.TreeSet.not_mem_emptyc
                    · intro v' hv'
                      rcases Std.TreeSet.mem_union_iff.mp hv' with hh | hh <;>
                        simp only [ffVarsOfFormula, bVarsOfFormula] at hh <;>
                        exact absurd hh Std.TreeSet.not_mem_emptyc
                    · intro v' hv'
                      rcases symEnvVars_setVar_subset symEnv a
                          (SymValue.array (arr.set indexValue.val v)) v' hv' with hh | hh
                      · exact hbelow v' hh
                      · exact hbelow v' (hsub_newArr v' hh)
                    · intro v' hv'
                      rcases symEnvVars_setVar_subset symEnv a
                          (SymValue.array (arr.set indexValue.val v)) v' hv' with hh | hh
                      · exact Or.inl hh
                      · exact Or.inl (hsub_newArr v' hh)
                    · intro env assignment hmatch env' hc
                      have hpoint := hmatch.2
                      obtain ⟨vv, henv, hvv⟩ := hpoint a (SymValue.array arr) hg
                      cases vv with
                      | scalar _ => simp only [symValMatches] at hvv
                      | array varr =>
                          simp only [symValMatches] at hvv
                          have hlen : arr.toList.length = varr.toList.length := hvv.length_eq
                          simp only [Array.length_toList] at hlen
                          have h' : indexValue.val < varr.size := by omega
                          have hceval := tryEvalSimpleExprToFFValue_correct symEnv index env
                            assignment indexValue hmatch hidx
                          obtain ⟨valueVal, hvalceval, hvmatch⟩ :=
                            resolveSimpleExpr_correct symEnv value env assignment v hmatch hval
                          simp only [evalWriteArray, hceval, hvalceval,
                            Corellzk2smt.Language.Core.Semantics.Basic.getVar, henv,
                            ← Std.TreeMap.get?_eq_getElem?, dif_pos h'] at hc
                          injection hc with hc
                          have hmatchArr : List.Forall₂ (simpleValMatches assignment)
                              (arr.set indexValue.val v).toList
                              (varr.set indexValue.val valueVal).toList := by
                            rw [Array.toList_set, Array.toList_set]
                            exact list_forall2_set hvv indexValue.val v valueVal hvmatch
                          refine ⟨assignment, (fun n _ => rfl), (fun n _ => rfl),
                            (fun n _ => rfl), (fun n _ => rfl), ?_, ?_⟩
                          · simp only [evalFormula]
                          · rw [← hc]
                            exact EnvMatches_setVar assignment symEnv env a
                              (SymValue.array (arr.set indexValue.val v))
                              (Value.array (varr.set indexValue.val valueVal)) hmatch
                              (by simp only [symValMatches]; exact hmatchArr)
                    · intro env assignment hmatch assignment' hagree _heval_f
                      have hmatch' := EnvMatches_agreesOnFF_preserves assignment assignment'
                        symEnv env hagree hmatch
                      have hpoint := hmatch'.2
                      obtain ⟨vv, henv, hvv⟩ := hpoint a (SymValue.array arr) hg
                      cases vv with
                      | scalar _ => simp only [symValMatches] at hvv
                      | array varr =>
                          simp only [symValMatches] at hvv
                          have hlen : arr.toList.length = varr.toList.length := hvv.length_eq
                          simp only [Array.length_toList] at hlen
                          have h' : indexValue.val < varr.size := by omega
                          have hceval := tryEvalSimpleExprToFFValue_correct symEnv index env
                            assignment' indexValue hmatch' hidx
                          obtain ⟨valueVal, hvalceval, hvmatch⟩ :=
                            resolveSimpleExpr_correct symEnv value env assignment' v hmatch' hval
                          have hmatchArr : List.Forall₂ (simpleValMatches assignment')
                              (arr.set indexValue.val v).toList
                              (varr.set indexValue.val valueVal).toList := by
                            rw [Array.toList_set, Array.toList_set]
                            exact list_forall2_set hvv indexValue.val v valueVal hvmatch
                          refine ⟨Corellzk2smt.Language.Core.Semantics.Basic.setVar env a
                            (Value.array (varr.set indexValue.val valueVal)), ?_, ?_⟩
                          · simp only [evalWriteArray, hceval, hvalceval,
                              Corellzk2smt.Language.Core.Semantics.Basic.getVar, henv,
                              ← Std.TreeMap.get?_eq_getElem?, dif_pos h']
                          · exact EnvMatches_setVar assignment' symEnv env a
                              (SymValue.array (arr.set indexValue.val v))
                              (Value.array (varr.set indexValue.val valueVal)) hmatch'
                              (by simp only [symValMatches]; exact hmatchArr)
              · simp [seWriteArrayConstantIdx, hidx, Corellzk2smt.SymExec.Basic.getVar,
                  ← Std.TreeMap.get?_eq_getElem?, hg, dif_neg h] at hspec_eq

/-- `seWriteArray` correctly translates `evalWriteArray` -- pure dispatch: `seWriteArray` tries
    `seWriteArrayConstantIdx` first and only ever falls back to `seWriteArrayNonConstantIdx`,
    which is a permanent `"TBD"` stub, so `seWriteArray`'s success cases coincide exactly with
    `seWriteArrayConstantIdx`'s own. -/
theorem seWriteArray_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD) (a : VarID)
    (index value : SimpleExpr c) :
    TranslatesCorrectly gconf sconf specs ctx
      (fun env => evalWriteArray md gconf env a index value)
      (fun symEnv => seWriteArray md gconf sconf symEnv specs a index value) := by
  intro symEnv hbelow hvalid spec hspec_eq
  simp only [seWriteArray] at hspec_eq
  cases hconst : seWriteArrayConstantIdx md gconf sconf symEnv specs a index value with
  | ok spec' =>
      rw [hconst] at hspec_eq
      injection hspec_eq with hspec_eq
      subst hspec_eq
      exact seWriteArrayConstantIdx_correct gconf specs sconf ctx md a index value symEnv hbelow
        hvalid spec' hconst
  | error msg =>
      rw [hconst] at hspec_eq
      simp [seWriteArrayNonConstantIdx] at hspec_eq

/-- `seCopyArray` correctly translates `evalCopyArray`. Genuinely open, same reason as
    `seEvalAssignment_correct`. -/
theorem seCopyArray_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD) (out a : VarID) :
    TranslatesCorrectly gconf sconf specs ctx
      (fun env => evalCopyArray md gconf env out a)
      (fun symEnv => seCopyArray md gconf sconf symEnv specs out a) := by
  intro symEnv hbelow _hvalid spec hspec_eq
  cases hg : symEnv.get? a with
  | none =>
      simp [seCopyArray, Corellzk2smt.SymExec.Basic.getVar, ← Std.TreeMap.get?_eq_getElem?,
        hg] at hspec_eq
  | some v =>
      simp only [seCopyArray, Corellzk2smt.SymExec.Basic.getVar,
        ← Std.TreeMap.get?_eq_getElem?, hg] at hspec_eq
      injection hspec_eq with hspec_eq
      subst hspec_eq
      have hsub : symValVars v ⊆ symEnvVars symEnv := symValVars_subset_symEnvVars symEnv a v hg
      refine ⟨rfl, le_refl _, ?_, ?_, ?_, ?_, ValidBinRep_trivial gconf _ _, ?_, ?_⟩
      · intro v' hv'
        rcases Std.TreeSet.mem_union_iff.mp hv' with hh | hh <;>
          simp only [ffVarsOfFormula, bVarsOfFormula] at hh <;>
          exact absurd hh Std.TreeSet.not_mem_emptyc
      · intro v' hv'
        rcases Std.TreeSet.mem_union_iff.mp hv' with hh | hh <;>
          simp only [ffVarsOfFormula, bVarsOfFormula] at hh <;>
          exact absurd hh Std.TreeSet.not_mem_emptyc
      · intro v' hv'
        rcases symEnvVars_setVar_subset symEnv out v v' hv' with hh | hh
        · exact hbelow v' hh
        · exact hbelow v' (hsub v' hh)
      · intro v' hv'
        rcases symEnvVars_setVar_subset symEnv out v v' hv' with hh | hh
        · exact Or.inl hh
        · exact Or.inl (hsub v' hh)
      · intro env assignment hmatch env' hc
        have hpoint := hmatch.2
        obtain ⟨vv, henv, hvv⟩ := hpoint a v hg
        simp only [evalCopyArray, Corellzk2smt.Language.Core.Semantics.Basic.getVar, henv,
          ← Std.TreeMap.get?_eq_getElem?] at hc
        injection hc with hc
        refine ⟨assignment, (fun n _ => rfl), (fun n _ => rfl), (fun n _ => rfl),
          (fun n _ => rfl), ?_, ?_⟩
        · simp only [evalFormula]
        · rw [← hc]
          exact EnvMatches_setVar assignment symEnv env out v vv hmatch hvv
      · intro env assignment hmatch assignment' hagree _heval_f
        have hmatch' := EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagree
          hmatch
        have hpoint := hmatch'.2
        obtain ⟨vv, henv, hvv⟩ := hpoint a v hg
        refine ⟨Corellzk2smt.Language.Core.Semantics.Basic.setVar env out vv, ?_, ?_⟩
        · simp only [evalCopyArray, Corellzk2smt.Language.Core.Semantics.Basic.getVar, henv,
            ← Std.TreeMap.get?_eq_getElem?]
        · exact EnvMatches_setVar assignment' symEnv env out v vv hmatch' hvv

end Corellzk2smt.SymExec.Correctness.ArrayCmdsCorrectness
