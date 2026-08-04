import Corellzk2smt.SymExec.Correctness.Lemmas
import Corellzk2smt.SymExec.Correctness.FuncCallCorrectness
import Corellzk2smt.SymExec.Correctness.FuncCorrectness
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
open Corellzk2smt.FFConstraints.Lemmas
open Corellzk2smt.SymExec.Correctness.Lemmas
open Corellzk2smt.SymExec.Correctness.FuncCallCorrectness
open Corellzk2smt.SymExec.Correctness.FuncCorrectness
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

-- ---------------------------------------------------------------------------
-- Helpers for `seNewArray`'s `new_var_array_new` branch: `size` fresh vars, each tied to `0` via
-- its own equation, conjoined. All of these are stated over a plain `List.range size`-indexed
-- formula (`newArrayEqf`), then bridged back to `seNewArray`'s own "`elems.zip ids`" construction
-- (mirroring `mintFreshRetWithEq`'s array-branch shape) via `seNewArray_eqf_eq` -- the bridge is
-- needed since `elems` is always the same constant `SimpleSymVal.const 0` here, collapsing the
-- zip against a `List.range`-indexed list down to a single map.
-- ---------------------------------------------------------------------------

/-- The conjunction of `size` equations `var (nv+i) = 0`, `i < size`. -/
def newArrayEqf {c : ZKConfig} (nv size : Nat) : FFFormula c :=
  ((List.range size).map (fun i => FFFormula.eq (FFTerm.var (nv + i)) (FFTerm.val (0 : FF c)))).foldr
    FFFormula.and FFFormula.true

/-- Zipping a constant-valued list against a `List.range`-indexed one collapses to a single map --
    lets `seNewArray`'s own `elems.zip ids` construction (`elems` always `SimpleSymVal.const 0`
    here) be rewritten down to `newArrayEqf`'s simpler shape. -/
private theorem zip_range_replicate_const {c : ZKConfig} (v : FF c) :
    ∀ (size nv : Nat),
      ((List.replicate size (SimpleSymVal.const v)).zip
          ((List.range size).map (fun i => nv + i))) =
        (List.range size).map (fun i => (SimpleSymVal.const v, nv + i)) := by
  intro size
  induction size with
  | zero => intro nv; simp
  | succ size ih =>
      intro nv
      have hcongr1 : (List.range size).map ((fun i => nv + i) ∘ Nat.succ) =
          (List.range size).map (fun i => nv + 1 + i) := by
        apply List.map_congr_left; intro i _; show nv + (i + 1) = nv + 1 + i; omega
      have hcongr2 : (List.range size).map
          ((fun i => (SimpleSymVal.const v, nv + i)) ∘ Nat.succ) =
          (List.range size).map (fun i => (SimpleSymVal.const v, nv + 1 + i)) := by
        apply List.map_congr_left; intro i _
        show (SimpleSymVal.const v, nv + (i + 1)) = (SimpleSymVal.const v, nv + 1 + i)
        congr 1; omega
      rw [List.replicate_succ, List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, hcongr1, hcongr2]
      rw [List.zip_cons_cons, ih (nv + 1)]

/-- `seNewArray`'s `eqf` (the `new_var_array_new` branch's own construction) is `newArrayEqf`. -/
theorem seNewArray_eqf_eq {c : ZKConfig} (nv size : Nat) :
    (((List.replicate size (SimpleSymVal.const (0 : FF c))).zip
        ((List.range size).map (fun i => nv + i))).map
      (fun p => FFFormula.eq (FFTerm.var p.2) (simpleSymValToTerm p.1))).foldr
      FFFormula.and FFFormula.true = newArrayEqf nv size := by
  rw [zip_range_replicate_const 0 size nv]
  simp only [List.map_map, newArrayEqf]
  congr 1

/-- Soundness of `newArrayEqf`: if the assignment already reads back `0` on the whole block, the
    conjunction evaluates to `true`. -/
private theorem newArrayEqf_sound {c : ZKConfig} (gconf : GlobalConfig c) (ms : List (FFMacro c))
    (assign : Assignment c) :
    ∀ (nv size : Nat), (∀ i, i < size → assign.ff (nv + i) = 0) →
      evalFormula gconf assign (newArrayEqf (c := c) nv size) ms = Except.ok true := by
  intro nv size
  induction size generalizing nv with
  | zero => intro _; simp [newArrayEqf, evalFormula]
  | succ size ih =>
      intro hrange
      have h0 := hrange 0 (by omega)
      simp only [Nat.add_zero] at h0
      have hrange' : ∀ i, i < size → assign.ff (nv + 1 + i) = 0 := by
        intro i hi
        have h1 := hrange (i + 1) (by omega)
        have hnat : nv + (i + 1) = nv + 1 + i := by omega
        rwa [hnat] at h1
      have hih := ih (nv + 1) hrange'
      have hcongr : (List.range size).map
          ((fun i => FFFormula.eq (FFTerm.var (nv + i)) (FFTerm.val (0 : FF c))) ∘ Nat.succ) =
          (List.range size).map (fun i =>
            FFFormula.eq (FFTerm.var (nv + 1 + i)) (FFTerm.val (0 : FF c))) := by
        apply List.map_congr_left; intro i _
        show FFFormula.eq (FFTerm.var (nv + (i + 1))) (FFTerm.val (0 : FF c)) =
          FFFormula.eq (FFTerm.var (nv + 1 + i)) (FFTerm.val (0 : FF c))
        have hi_eq : nv + (i + 1) = nv + 1 + i := by omega
        rw [hi_eq]
      simp only [newArrayEqf, List.range_succ_eq_map, List.map_cons, List.map_map, hcongr,
        List.foldr_cons]
      simp only [newArrayEqf] at hih
      simp [evalFormula, evalTerm, Nat.add_zero, h0, hih]

/-- Converse of `newArrayEqf_sound`. -/
private theorem newArrayEqf_complete {c : ZKConfig} (gconf : GlobalConfig c)
    (ms : List (FFMacro c)) (assign : Assignment c) :
    ∀ (nv size : Nat),
      evalFormula gconf assign (newArrayEqf (c := c) nv size) ms = Except.ok true →
      ∀ i, i < size → assign.ff (nv + i) = 0 := by
  intro nv size
  induction size generalizing nv with
  | zero => intro _ i hi; omega
  | succ size ih =>
      intro heval i hi
      have hcongr : (List.range size).map
          ((fun i => FFFormula.eq (FFTerm.var (nv + i)) (FFTerm.val (0 : FF c))) ∘ Nat.succ) =
          (List.range size).map (fun i =>
            FFFormula.eq (FFTerm.var (nv + 1 + i)) (FFTerm.val (0 : FF c))) := by
        apply List.map_congr_left; intro i _
        show FFFormula.eq (FFTerm.var (nv + (i + 1))) (FFTerm.val (0 : FF c)) =
          FFFormula.eq (FFTerm.var (nv + 1 + i)) (FFTerm.val (0 : FF c))
        have hi_eq : nv + (i + 1) = nv + 1 + i := by omega
        rw [hi_eq]
      simp only [newArrayEqf, List.range_succ_eq_map, List.map_cons, List.map_map, hcongr,
        List.foldr_cons, Nat.add_zero] at heval
      set eqf : FFFormula c := FFFormula.eq (FFTerm.var nv) (FFTerm.val (0 : FF c))
        with heqf_def
      set restf : FFFormula c :=
        List.foldr FFFormula.and FFFormula.true
          (List.map (fun i => FFFormula.eq (FFTerm.var (nv + 1 + i)) (FFTerm.val (0 : FF c)))
            (List.range size))
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
          cases i with
          | zero =>
              simp only [Nat.add_zero]
              rw [heqf_def] at heq1
              simp only [evalFormula] at heq1
              cases ht1 : evalTerm gconf assign (FFTerm.var nv) ms with
              | error e3 => rw [ht1] at heq1; simp at heq1
              | ok ta =>
                rw [ht1] at heq1
                cases ht2 : evalTerm gconf assign (FFTerm.val (0 : FF c)) ms with
                | error e4 => rw [ht2] at heq1; simp at heq1
                | ok tb =>
                  rw [ht2] at heq1
                  simp only [Except.ok.injEq] at heq1
                  rw [hb1] at heq1
                  have htab' : ta = tb := by
                    have hsymm := heq1.symm
                    simpa using hsymm
                  have hta : assign.ff nv = ta := by
                    simp only [evalTerm] at ht1; injection ht1
                  have htb : (0 : FF c) = tb := by simp only [evalTerm] at ht2; injection ht2
                  rw [hta, htab', ← htb]
          | succ i =>
              have heval2 : evalFormula gconf assign restf ms = Except.ok true :=
                heq2.trans (congrArg Except.ok hb2)
              rw [hrestf_def] at heval2
              have hind := ih (nv + 1) heval2 i (by omega)
              have hnat : nv + 1 + i = nv + (i + 1) := by omega
              rwa [hnat] at hind

/-- Every var mentioned by `newArrayEqf nv size` is one of the `size` fresh tie-back vars
    themselves -- the constant `0` on the other side of each equation contributes no vars. -/
private theorem newArrayEqf_vars_range {c : ZKConfig} :
    ∀ (nv size : Nat) (v' : Var),
      v' ∈ (ffVarsOfFormula (newArrayEqf (c := c) nv size) ∪
            bVarsOfFormula (newArrayEqf (c := c) nv size)) →
      ∃ i, i < size ∧ v' = Var.ffv (nv + i) := by
  intro nv size
  induction size generalizing nv with
  | zero => intro v' hv'; simp [newArrayEqf, ffVarsOfFormula, bVarsOfFormula] at hv'
  | succ size ih =>
      intro v' hv'
      have hcongr : (List.range size).map
          ((fun i => FFFormula.eq (FFTerm.var (nv + i)) (FFTerm.val (0 : FF c))) ∘ Nat.succ) =
          (List.range size).map (fun i =>
            FFFormula.eq (FFTerm.var (nv + 1 + i)) (FFTerm.val (0 : FF c))) := by
        apply List.map_congr_left; intro i _
        show FFFormula.eq (FFTerm.var (nv + (i + 1))) (FFTerm.val (0 : FF c)) =
          FFFormula.eq (FFTerm.var (nv + 1 + i)) (FFTerm.val (0 : FF c))
        have hi_eq : nv + (i + 1) = nv + 1 + i := by omega
        rw [hi_eq]
      simp only [newArrayEqf, List.range_succ_eq_map, List.map_cons, List.map_map, hcongr,
        List.foldr_cons, ffVarsOfFormula, bVarsOfFormula, Std.TreeSet.mem_union_iff,
        Nat.add_zero] at hv'
      rcases hv' with (h1 | h1) | (h1 | h1)
      · simp only [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_union_iff] at h1
        rcases h1 with h1 | h1
        · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
          · exact ⟨0, by omega, by rw [← Var_compare_eq_iff_eq.mp heq, Nat.add_zero]⟩
          · exact absurd hmem Std.TreeSet.not_mem_emptyc
        · exact absurd h1 Std.TreeSet.not_mem_emptyc
      · have hih := ih (nv + 1) v'
        simp only [newArrayEqf] at hih
        obtain ⟨i, hi, hveq⟩ := hih (Std.TreeSet.mem_union_iff.mpr (Or.inl h1))
        refine ⟨i + 1, by omega, ?_⟩
        rw [hveq]
        have hnat : nv + 1 + i = nv + (i + 1) := by omega
        rw [hnat]
      · simp only [bVarsOfFormula, bVarsOfTerm, Std.TreeSet.mem_union_iff] at h1
        rcases h1 with h1 | h1 <;> exact absurd h1 Std.TreeSet.not_mem_emptyc
      · have hih := ih (nv + 1) v'
        simp only [newArrayEqf] at hih
        obtain ⟨i, hi, hveq⟩ := hih (Std.TreeSet.mem_union_iff.mpr (Or.inr h1))
        refine ⟨i + 1, by omega, ?_⟩
        rw [hveq]
        have hnat : nv + 1 + i = nv + (i + 1) := by omega
        rw [hnat]

/-- Forward direction / converse of `newArrayEqf_vars_range`: every one of the `size` fresh
    tie-back vars is actually mentioned by `newArrayEqf nv size`. -/
private theorem newArrayEqf_vars_mem {c : ZKConfig} :
    ∀ (nv size i : Nat), i < size →
      Var.ffv (nv + i) ∈ ffVarsOfFormula (newArrayEqf (c := c) nv size) := by
  intro nv size
  induction size generalizing nv with
  | zero => intro i hi; omega
  | succ size ih =>
      intro i hi
      have hcongr : (List.range size).map
          ((fun i => FFFormula.eq (FFTerm.var (nv + i)) (FFTerm.val (0 : FF c))) ∘ Nat.succ) =
          (List.range size).map (fun i =>
            FFFormula.eq (FFTerm.var (nv + 1 + i)) (FFTerm.val (0 : FF c))) := by
        apply List.map_congr_left; intro i _
        show FFFormula.eq (FFTerm.var (nv + (i + 1))) (FFTerm.val (0 : FF c)) =
          FFFormula.eq (FFTerm.var (nv + 1 + i)) (FFTerm.val (0 : FF c))
        have hi_eq : nv + (i + 1) = nv + 1 + i := by omega
        rw [hi_eq]
      simp only [newArrayEqf, List.range_succ_eq_map, List.map_cons, List.map_map, hcongr,
        List.foldr_cons, ffVarsOfFormula]
      cases i with
      | zero =>
          apply Std.TreeSet.mem_union_of_left
          simp only [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_union_iff]
          exact Or.inl (Std.TreeSet.mem_insert_self ..)
      | succ i =>
          apply Std.TreeSet.mem_union_of_right
          have hind := ih (nv + 1) i (by omega)
          simp only [newArrayEqf] at hind
          have hnat : nv + (i + 1) = nv + 1 + i := by omega
          rw [hnat]
          exact hind

/-- `newArrayEqf` never mentions a macro call -- built purely from `.eq`/`.and`/`.true`. -/
theorem newArrayEqf_names_below {c : ZKConfig} (nv size : Nat) (badName : String) :
    FormulaNamesBelow (newArrayEqf (c := c) nv size) badName := by
  induction size generalizing nv with
  | zero => simp only [newArrayEqf, List.range_zero, List.map_nil, List.foldr_nil]; trivial
  | succ size ih =>
      have hcongr : (List.range size).map
          ((fun i => FFFormula.eq (FFTerm.var (nv + i)) (FFTerm.val (0 : FF c))) ∘ Nat.succ) =
          (List.range size).map (fun i =>
            FFFormula.eq (FFTerm.var (nv + 1 + i)) (FFTerm.val (0 : FF c))) := by
        apply List.map_congr_left; intro i _
        show FFFormula.eq (FFTerm.var (nv + (i + 1))) (FFTerm.val (0 : FF c)) =
          FFFormula.eq (FFTerm.var (nv + 1 + i)) (FFTerm.val (0 : FF c))
        have hi_eq : nv + (i + 1) = nv + 1 + i := by omega
        rw [hi_eq]
      simp only [newArrayEqf, List.range_succ_eq_map, List.map_cons, List.map_map, hcongr,
        List.foldr_cons, FormulaNamesBelow]
      have hih := ih (nv + 1)
      simp only [newArrayEqf] at hih
      exact ⟨⟨trivial, trivial⟩, hih⟩

/-- `seNewArray` correctly translates `evalNewArray`. When `new_var_array_new` is off, both mint
    no fresh constraint variable and no formula content (`f := .true`): the only thing that happens
    is inserting a matching brand-new all-zero array (symbolic `.const 0`s, concrete `(0 : FF c)`s,
    same length). When it's on, `size` fresh constraint variables are minted instead, each tied to
    `0` via its own equation (`newArrayEqf`) -- the symbolic array is exactly `freshRetSymValue
    sconf.nextVarId (.array size)`, letting the fresh-block reasoning already established for
    `mintFreshRetWithEq`'s array branch (`FuncCorrectness.lean`/`FuncCallCorrectness.lean`) carry
    over directly. -/
theorem seNewArray_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD) (id : VarID) (size : SimpleExpr c) :
    TranslatesCorrectly gconf sconf specs ctx
      (fun env => evalNewArray md gconf env id size)
      (fun symEnv => seNewArray md gconf sconf symEnv specs id size) := by
  intro symEnv hbelow _hvalid spec hspec_eq
  cases hsize : tryEvalSimpleExprToFFValue symEnv size with
  | error msg => simp [seNewArray, hsize] at hspec_eq
  | ok sizeValue =>
      cases hnew : gconf.sym_exec.new_var_array_new with
      | true =>
          simp only [seNewArray, hsize, hnew] at hspec_eq
          injection hspec_eq with hspec_eq
          subst hspec_eq
          set nv := sconf.nextVarId with hnv_def
          set n := sizeValue.val with hn_def
          have heqf_eq : (((List.replicate n (SimpleSymVal.const (0 : FF c))).zip
                ((List.range n).map (fun i => nv + i))).map
              (fun p => FFFormula.eq (FFTerm.var p.2) (simpleSymValToTerm p.1))).foldr
              FFFormula.and FFFormula.true = newArrayEqf nv n := seNewArray_eqf_eq nv n
          have harr_eq : SymValue.array
              (((List.range n).map (fun i => nv + i)).map
                (fun v => SimpleSymVal.ffvar (⟨v, none⟩ : FFVarWithBinRep c))).toArray =
              freshRetSymValue (c := c) nv (VarType.array n) := by
            simp only [freshRetSymValue, List.map_map]
            rfl
          clear_value nv n
          refine ⟨rfl, Nat.le_add_right _ _, ?_, ?_, ?_, ?_, ValidBinRep_trivial gconf _ _, ?_, ?_⟩
          · intro v' hv'
            rw [heqf_eq] at hv'
            obtain ⟨i, hi, hveq⟩ := newArrayEqf_vars_range nv n v' hv'
            exact Or.inr (by rw [hveq]; simp only [varIndex]; omega)
          · intro v' hv'
            show varIndex v' < nv + n
            rw [heqf_eq] at hv'
            obtain ⟨i, hi, hveq⟩ := newArrayEqf_vars_range nv n v' hv'
            rw [hveq]; simp only [varIndex]; omega
          · intro v' hv'
            show varIndex v' < nv + n
            rw [harr_eq] at hv'
            rcases symEnvVars_setVar_subset symEnv id
                (freshRetSymValue (c := c) nv (VarType.array n)) v' hv' with h | h
            · have := hbelow v' h; omega
            · obtain ⟨m, hveq, hle, hlt⟩ := symValVars_freshRetSymValue_below nv (VarType.array n)
                v' h
              simp only [typeSize] at hlt
              rw [hveq]; simp only [varIndex]; omega
          · intro v' hv'
            rw [harr_eq] at hv'
            rcases symEnvVars_setVar_subset symEnv id
                (freshRetSymValue (c := c) nv (VarType.array n)) v' hv' with h | h
            · exact Or.inl h
            · obtain ⟨m, hveq, hle, _hlt⟩ := symValVars_freshRetSymValue_below nv
                (VarType.array n) v' h
              rw [hveq]; exact Or.inr hle
          · intro env assignment hmatch env' hc
            have hceval := tryEvalSimpleExprToFFValue_correct symEnv size env assignment
              sizeValue hmatch hsize
            simp only [evalNewArray, hceval] at hc
            injection hc with hc
            rw [← hn_def] at hc
            set assignment' : Assignment c :=
              { assignment with
                ff := fun m => if nv ≤ m ∧ m < nv + n then 0 else assignment.ff m }
              with hassignment'_def
            have hagreeff : agreesOnFF (symEnvVars symEnv) assignment assignment' := by
              intro m hm
              have hlt : m < nv := hbelow (Var.ffv m) hm
              -- `m : FFVar` (an abbrev for `Nat`) confuses `omega`'s atom detection when mixed
              -- directly with plain `Nat` terms -- bridge through a genuinely `Nat`-typed copy.
              let m2 : Nat := m
              have hlt2 : m2 < nv := hlt
              have hgoal : m2 = m := rfl
              clear_value m2
              have hcond : ¬(nv ≤ m ∧ m < nv + n) := by rw [← hgoal]; omega
              simp only [hassignment'_def, if_neg hcond]
            have hagreebool : agreesOnBool (symEnvVars symEnv) assignment assignment' :=
              fun _ _ => rfl
            have hrangeff : ∀ i, i < n → assignment'.ff (nv + i) = 0 := by
              intro i hi
              have hcond : nv ≤ nv + i ∧ nv + i < nv + n := by omega
              simp only [hassignment'_def, if_pos hcond]
            have hframeff : ∀ m, Var.ffv m ∉
                (ffVarsOfFormula (newArrayEqf (c := c) nv n) ∪
                  bVarsOfFormula (newArrayEqf (c := c) nv n)) →
                assignment'.ff m = assignment.ff m := by
              intro m hm
              have hcond : ¬(nv ≤ m ∧ m < nv + n) := by
                rintro ⟨hle, hlt⟩
                apply hm
                -- same `FFVar`/`omega` bridging as `hagreeff` above.
                let m2 : Nat := m
                have hle2 : nv ≤ m2 := hle
                have hlt2 : m2 < nv + n := hlt
                have hgoal : m2 = m := rfl
                clear_value m2
                have hi : m2 - nv < n := by omega
                have hnat : nv + (m2 - nv) = m2 := by omega
                have hmem := newArrayEqf_vars_mem (c := c) nv n (m2 - nv) hi
                rw [hnat, hgoal] at hmem
                exact Std.TreeSet.mem_union_of_left hmem
              simp only [hassignment'_def, if_neg hcond]
            have hframebool : ∀ m, Var.boolv m ∉
                (ffVarsOfFormula (newArrayEqf (c := c) nv n) ∪
                  bVarsOfFormula (newArrayEqf (c := c) nv n)) →
                assignment'.bool m = assignment.bool m := fun _ _ => rfl
            refine ⟨assignment', hagreeff, hagreebool, ?_, ?_, ?_, ?_⟩
            · rw [heqf_eq]; exact hframeff
            · rw [heqf_eq]; exact hframebool
            · rw [heqf_eq]; exact newArrayEqf_sound gconf (specs.map (·.f)) assignment' nv n
                hrangeff
            · rw [← hc]
              have hvalmatch : symValMatches assignment' (freshRetSymValue (c := c) nv
                  (VarType.array n)) (Value.array (List.replicate n (0 : FF c)).toArray) := by
                apply freshRetSymValue_symValMatches
                · simp only [ensureCorrectType]
                  simp
                · intro i hi
                  simp only [typeSize] at hi
                  simp only [flattenValueToFF, List.toList_toArray]
                  rw [hrangeff i hi]
                  simp [hi]
              rw [← harr_eq] at hvalmatch
              exact EnvMatches_setVar assignment' symEnv env id _ _
                (EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagreeff hmatch)
                hvalmatch
          · intro env assignment hmatch assignment' hagree heval_f
            rw [heqf_eq] at heval_f
            have hmatch' := EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env
              hagree hmatch
            have hceval := tryEvalSimpleExprToFFValue_correct symEnv size env assignment'
              sizeValue hmatch' hsize
            have hrangeff := newArrayEqf_complete gconf (specs.map (·.f)) assignment' nv n heval_f
            have hvalmatch : symValMatches assignment' (freshRetSymValue (c := c) nv
                (VarType.array n)) (Value.array (List.replicate n (0 : FF c)).toArray) := by
              apply freshRetSymValue_symValMatches
              · simp only [ensureCorrectType]
                simp
              · intro i hi
                simp only [typeSize] at hi
                simp only [flattenValueToFF, List.toList_toArray]
                rw [hrangeff i hi]
                simp [hi]
            rw [← harr_eq] at hvalmatch
            refine ⟨Corellzk2smt.Language.Core.Semantics.Basic.setVar env id
              (Value.array (List.replicate n (0 : FF c)).toArray), ?_, ?_⟩
            · simp only [evalNewArray, hceval, hn_def]
            · exact EnvMatches_setVar assignment' symEnv env id _ _ hmatch' hvalmatch
      | false =>
          simp only [seNewArray, hsize, hnew] at hspec_eq
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
                (SymValue.array
                  (List.replicate sizeValue.val (SimpleSymVal.const (0 : FF c))).toArray)
                v' hv' with h | h
            · exact hbelow v' h
            · exact (symValVars_replicate_const_array sizeValue.val (0 : FF c) v' h).elim
          · intro v' hv'
            rcases symEnvVars_setVar_subset symEnv id
                (SymValue.array
                  (List.replicate sizeValue.val (SimpleSymVal.const (0 : FF c))).toArray)
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
                (SymValue.array
                  (List.replicate sizeValue.val (SimpleSymVal.const (0 : FF c))).toArray)
                (Value.array (List.replicate sizeValue.val (0 : FF c)).toArray) hmatch
                (symValMatches_replicate_const_array assignment sizeValue.val 0)
          · intro env assignment hmatch assignment' hagree _heval_f
            have hmatch' := EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env
              hagree hmatch
            have hceval := tryEvalSimpleExprToFFValue_correct symEnv size env assignment'
              sizeValue hmatch' hsize
            refine ⟨Corellzk2smt.Language.Core.Semantics.Basic.setVar env id
              (Value.array (List.replicate sizeValue.val (0 : FF c)).toArray), ?_, ?_⟩
            · simp only [evalNewArray, hceval]
            · exact EnvMatches_setVar assignment' symEnv env id
                (SymValue.array
                  (List.replicate sizeValue.val (SimpleSymVal.const (0 : FF c))).toArray)
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
                have hsub_arr : symValVars (SymValue.array arr) ⊆ symEnvVars symEnv :=
                  symValVars_subset_symEnvVars symEnv a (SymValue.array arr) hg
                have hmemArr : arr[indexValue.val]'h ∈ arr.toList :=
                  Array.getElem_mem_toList h
                have hsub_val : simpleValVars (arr[indexValue.val]'h) ⊆ symEnvVars symEnv :=
                  symValVars_array_mem_below_subset arr (arr[indexValue.val]'h) hmemArr
                    (symEnvVars symEnv) hsub_arr
                cases hnew : gconf.sym_exec.new_var_array_read with
                | true =>
                    simp only [hnew] at hspec_eq
                    injection hspec_eq with hspec_eq
                    subst hspec_eq
                    have hmemF : Var.ffv sconf.nextVarId ∈
                        ffVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
                          (simpleSymValToTerm (arr[indexValue.val]'h))) := by
                      simp only [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_union_iff]
                      exact Or.inl (Std.TreeSet.mem_insert_self ..)
                    refine ⟨rfl, Nat.le_succ _, ?_, ?_, ?_, ?_, ValidBinRep_trivial gconf _ _,
                      ?_, ?_⟩
                    · intro v' hv'
                      rcases Std.TreeSet.mem_union_iff.mp hv' with hff | hb
                      · simp only [ffVarsOfFormula, ffVarsOfTerm, ffVarsOfTerm_simpleSymValToTerm,
                          Std.TreeSet.mem_union_iff] at hff
                        rcases hff with h1 | h2
                        · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
                          · rw [← Var_compare_eq_iff_eq.mp heq]
                            exact Or.inr (le_refl _)
                          · exact absurd hmem Std.TreeSet.not_mem_emptyc
                        · exact Or.inl (hsub_val v'
                            (simpleValOwnVars_subset_simpleValVars (arr[indexValue.val]'h) v' h2))
                      · simp only [bVarsOfFormula, bVarsOfTerm, bVarsOfTerm_simpleSymValToTerm,
                          Std.TreeSet.mem_union_iff] at hb
                        rcases hb with h' | h' <;> exact absurd h' Std.TreeSet.not_mem_emptyc
                    · intro v' hv'
                      show varIndex v' < sconf.nextVarId + 1
                      rcases Std.TreeSet.mem_union_iff.mp hv' with hff | hb
                      · simp only [ffVarsOfFormula, ffVarsOfTerm, ffVarsOfTerm_simpleSymValToTerm,
                          Std.TreeSet.mem_union_iff] at hff
                        rcases hff with h1 | h2
                        · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
                          · rw [← Var_compare_eq_iff_eq.mp heq]
                            simp only [varIndex]
                            omega
                          · exact absurd hmem Std.TreeSet.not_mem_emptyc
                        · have := hbelow v' (hsub_val v'
                            (simpleValOwnVars_subset_simpleValVars (arr[indexValue.val]'h) v' h2))
                          omega
                      · simp only [bVarsOfFormula, bVarsOfTerm, bVarsOfTerm_simpleSymValToTerm,
                          Std.TreeSet.mem_union_iff] at hb
                        rcases hb with h' | h' <;> exact absurd h' Std.TreeSet.not_mem_emptyc
                    · intro v' hv'
                      show varIndex v' < sconf.nextVarId + 1
                      rcases symEnvVars_setVar_subset symEnv out
                          (SymValue.simple (SimpleSymVal.ffvar ⟨sconf.nextVarId, none⟩)) v' hv'
                        with h' | h'
                      · have := hbelow v' h'; omega
                      · simp only [symValVars, simpleValVars, simpleValOwnVars, Option.map_none,
                          Option.getD_none, Std.TreeSet.mem_union_iff] at h'
                        rcases h' with h'' | h''
                        · rcases Std.TreeSet.mem_insert.mp h'' with heq | hmem
                          · rw [← Var_compare_eq_iff_eq.mp heq]; simp only [varIndex]; omega
                          · exact absurd hmem Std.TreeSet.not_mem_emptyc
                        · exact absurd h'' Std.TreeSet.not_mem_emptyc
                    · intro v' hv'
                      rcases symEnvVars_setVar_subset symEnv out
                          (SymValue.simple (SimpleSymVal.ffvar ⟨sconf.nextVarId, none⟩)) v' hv'
                        with h' | h'
                      · exact Or.inl h'
                      · simp only [symValVars, simpleValVars, simpleValOwnVars, Option.map_none,
                          Option.getD_none, Std.TreeSet.mem_union_iff] at h'
                        rcases h' with h'' | h''
                        · rcases Std.TreeSet.mem_insert.mp h'' with heq | hmem
                          · rw [← Var_compare_eq_iff_eq.mp heq]; exact Or.inr (le_refl _)
                          · exact absurd hmem Std.TreeSet.not_mem_emptyc
                        · exact absurd h'' Std.TreeSet.not_mem_emptyc
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
                          simp only [evalReadArray,
                            Corellzk2smt.Language.Core.Semantics.Basic.getVar, hceval, henv,
                            ← Std.TreeMap.get?_eq_getElem?, dif_pos h'] at hc
                          injection hc with hc
                          have hmatchElem : simpleValMatches assignment (arr[indexValue.val]'h)
                              (varr[indexValue.val]'h') :=
                            list_forall2_get hvv indexValue.val
                              (by simp only [Array.length_toList]; exact h)
                              (by simp only [Array.length_toList]; exact h')
                          set assignment' : Assignment c :=
                            { assignment with
                              ff := fun n => if n = sconf.nextVarId then varr[indexValue.val]'h'
                                else assignment.ff n }
                            with hassignment'_def
                          have hagreeff : agreesOnFF (symEnvVars symEnv) assignment assignment' :=
                            by
                              intro n hn
                              have hne : n ≠ sconf.nextVarId :=
                                Nat.ne_of_lt (hbelow (Var.ffv n) hn)
                              simp only [hassignment'_def, if_neg hne]
                          have hagreebool :
                              agreesOnBool (symEnvVars symEnv) assignment assignment' :=
                            fun n _ => rfl
                          have hframeff : ∀ n, Var.ffv n ∉
                              (ffVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
                                (simpleSymValToTerm (arr[indexValue.val]'h))) ∪
                               bVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
                                (simpleSymValToTerm (arr[indexValue.val]'h)))) →
                              assignment'.ff n = assignment.ff n := by
                            intro n hn
                            have hne : n ≠ sconf.nextVarId := by
                              intro heqn
                              apply hn
                              rw [heqn]
                              exact Std.TreeSet.mem_union_of_left hmemF
                            simp only [hassignment'_def, if_neg hne]
                          have hframebool : ∀ n, Var.boolv n ∉
                              (ffVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
                                (simpleSymValToTerm (arr[indexValue.val]'h))) ∪
                               bVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
                                (simpleSymValToTerm (arr[indexValue.val]'h)))) →
                              assignment'.bool n = assignment.bool n := fun n _ => rfl
                          have hmatchElem' : simpleValMatches assignment'
                              (arr[indexValue.val]'h) (varr[indexValue.val]'h') :=
                            simpleValMatches_agreesOnFF_preserves assignment assignment'
                              (arr[indexValue.val]'h) (varr[indexValue.val]'h')
                              (symEnvVars symEnv) hsub_val hagreeff hmatchElem
                          have hevalTerm' := evalTerm_simpleSymValToTerm gconf assignment'
                            (arr[indexValue.val]'h) (varr[indexValue.val]'h') (specs.map (·.f))
                            hmatchElem'
                          have hffeval : assignment'.ff sconf.nextVarId
                              = varr[indexValue.val]'h' := by simp [hassignment'_def]
                          refine ⟨assignment', hagreeff, hagreebool, hframeff, hframebool, ?_, ?_⟩
                          · simp [evalFormula, evalTerm, hevalTerm', hffeval]
                          · rw [← hc]
                            exact EnvMatches_setVar assignment' symEnv env out
                              (SymValue.simple (SimpleSymVal.ffvar ⟨sconf.nextVarId, none⟩))
                              (Value.scalar (varr[indexValue.val]'h'))
                              (EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env
                                hagreeff hmatch)
                              (by simp only [symValMatches, simpleValMatches, hffeval])
                    · intro env assignment hmatch assignment' hagree heval_f
                      have hmatch' : EnvMatches assignment' symEnv env :=
                        EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagree
                          hmatch
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
                          have hevalTerm' := evalTerm_simpleSymValToTerm gconf assignment'
                            (arr[indexValue.val]'h) (varr[indexValue.val]'h') (specs.map (·.f))
                            hmatchElem
                          simp only [evalFormula, evalTerm, hevalTerm', Except.ok.injEq]
                            at heval_f
                          have hffeq : assignment'.ff sconf.nextVarId = varr[indexValue.val]'h' :=
                            (beq_iff_eq ..).mp heval_f
                          refine ⟨Corellzk2smt.Language.Core.Semantics.Basic.setVar env out
                            (Value.scalar (varr[indexValue.val]'h')), ?_, ?_⟩
                          · simp only [evalReadArray,
                              Corellzk2smt.Language.Core.Semantics.Basic.getVar, hceval, henv,
                              ← Std.TreeMap.get?_eq_getElem?, dif_pos h']
                          · exact EnvMatches_setVar assignment' symEnv env out
                              (SymValue.simple (SimpleSymVal.ffvar ⟨sconf.nextVarId, none⟩))
                              (Value.scalar (varr[indexValue.val]'h')) hmatch'
                              (by simp only [symValMatches, simpleValMatches, hffeq])
                | false =>
                    simp only [hnew] at hspec_eq
                    injection hspec_eq with hspec_eq
                    subst hspec_eq
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
                          simp only [evalReadArray,
                            Corellzk2smt.Language.Core.Semantics.Basic.getVar, hceval, henv,
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
                      have hmatch' := EnvMatches_agreesOnFF_preserves assignment assignment'
                        symEnv env hagree hmatch
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
                          · simp only [evalReadArray,
                              Corellzk2smt.Language.Core.Semantics.Basic.getVar, hceval, henv,
                              ← Std.TreeMap.get?_eq_getElem?, dif_pos h']
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
                    have hsub_arr : symValVars (SymValue.array arr) ⊆ symEnvVars symEnv :=
                      symValVars_subset_symEnvVars symEnv a (SymValue.array arr) hg
                    have hsub_v : simpleValVars v ⊆ symEnvVars symEnv :=
                      Corellzk2smt.SymExec.Correctness.Lemmas.resolveSimpleExpr_vars_subset symEnv
                        value v hval
                    cases hnew : gconf.sym_exec.new_var_array_write with
                    | true =>
                        simp only [seWriteArrayConstantIdx, hidx,
                          Corellzk2smt.SymExec.Basic.getVar, ← Std.TreeMap.get?_eq_getElem?, hg,
                          dif_pos h, hval, hnew] at hspec_eq
                        injection hspec_eq with hspec_eq
                        subst hspec_eq
                        have hmemF : Var.ffv sconf.nextVarId ∈
                            ffVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
                              (simpleSymValToTerm v)) := by
                          simp only [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_union_iff]
                          exact Or.inl (Std.TreeSet.mem_insert_self ..)
                        have hsub_newArr : ∀ v', v' ∈ symValVars (SymValue.array
                              (arr.set indexValue.val
                                (SimpleSymVal.ffvar ⟨sconf.nextVarId, none⟩))) →
                            v' ∈ symEnvVars symEnv ∨ v' = Var.ffv sconf.nextVarId := by
                          intro v' hv'
                          simp only [symValVars] at hv'
                          rw [← Array.foldl_toList] at hv'
                          rcases foldl_union_mem_elim simpleValVars
                              (arr.set indexValue.val
                                (SimpleSymVal.ffvar ⟨sconf.nextVarId, none⟩)).toList emptyVarSet
                              v' hv' with hh | hh
                          · exact absurd hh Std.TreeSet.not_mem_emptyc
                          · obtain ⟨x, hx, hvx⟩ := hh
                            rw [Array.toList_set] at hx
                            rcases List.mem_or_eq_of_mem_set hx with hx' | hx'
                            · exact Or.inl (symValVars_array_mem_below_subset arr x hx'
                                (symEnvVars symEnv) hsub_arr v' hvx)
                            · rw [hx'] at hvx
                              simp only [simpleValVars, simpleValOwnVars, Option.map_none,
                                Option.getD_none, Std.TreeSet.mem_union_iff] at hvx
                              rcases hvx with hh' | hh'
                              · rcases Std.TreeSet.mem_insert.mp hh' with heq | hmem
                                · exact Or.inr (Var_compare_eq_iff_eq.mp heq).symm
                                · exact absurd hmem Std.TreeSet.not_mem_emptyc
                              · exact absurd hh' Std.TreeSet.not_mem_emptyc
                        refine ⟨rfl, Nat.le_succ _, ?_, ?_, ?_, ?_, ValidBinRep_trivial gconf _ _,
                          ?_, ?_⟩
                        · intro v' hv'
                          rcases Std.TreeSet.mem_union_iff.mp hv' with hff | hb
                          · simp only [ffVarsOfFormula, ffVarsOfTerm,
                              ffVarsOfTerm_simpleSymValToTerm, Std.TreeSet.mem_union_iff] at hff
                            rcases hff with h1 | h2
                            · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
                              · rw [← Var_compare_eq_iff_eq.mp heq]
                                exact Or.inr (le_refl _)
                              · exact absurd hmem Std.TreeSet.not_mem_emptyc
                            · exact Or.inl (hsub_v v'
                                (simpleValOwnVars_subset_simpleValVars v v' h2))
                          · simp only [bVarsOfFormula, bVarsOfTerm, bVarsOfTerm_simpleSymValToTerm,
                              Std.TreeSet.mem_union_iff] at hb
                            rcases hb with h' | h' <;> exact absurd h' Std.TreeSet.not_mem_emptyc
                        · intro v' hv'
                          show varIndex v' < sconf.nextVarId + 1
                          rcases Std.TreeSet.mem_union_iff.mp hv' with hff | hb
                          · simp only [ffVarsOfFormula, ffVarsOfTerm,
                              ffVarsOfTerm_simpleSymValToTerm, Std.TreeSet.mem_union_iff] at hff
                            rcases hff with h1 | h2
                            · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
                              · rw [← Var_compare_eq_iff_eq.mp heq]
                                simp only [varIndex]
                                omega
                              · exact absurd hmem Std.TreeSet.not_mem_emptyc
                            · have := hbelow v'
                                (hsub_v v' (simpleValOwnVars_subset_simpleValVars v v' h2))
                              omega
                          · simp only [bVarsOfFormula, bVarsOfTerm, bVarsOfTerm_simpleSymValToTerm,
                              Std.TreeSet.mem_union_iff] at hb
                            rcases hb with h' | h' <;> exact absurd h' Std.TreeSet.not_mem_emptyc
                        · intro v' hv'
                          show varIndex v' < sconf.nextVarId + 1
                          rcases symEnvVars_setVar_subset symEnv a (SymValue.array
                              (arr.set indexValue.val
                                (SimpleSymVal.ffvar ⟨sconf.nextVarId, none⟩))) v' hv'
                            with hh | hh
                          · have := hbelow v' hh; omega
                          · rcases hsub_newArr v' hh with hh' | hh'
                            · have := hbelow v' hh'; omega
                            · rw [hh']; simp only [varIndex]; omega
                        · intro v' hv'
                          rcases symEnvVars_setVar_subset symEnv a (SymValue.array
                              (arr.set indexValue.val
                                (SimpleSymVal.ffvar ⟨sconf.nextVarId, none⟩))) v' hv'
                            with hh | hh
                          · exact Or.inl hh
                          · rcases hsub_newArr v' hh with hh' | hh'
                            · exact Or.inl hh'
                            · rw [hh']; exact Or.inr (le_refl _)
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
                                resolveSimpleExpr_correct symEnv value env assignment v hmatch
                                  hval
                              simp only [evalWriteArray, hceval, hvalceval,
                                Corellzk2smt.Language.Core.Semantics.Basic.getVar, henv,
                                ← Std.TreeMap.get?_eq_getElem?, dif_pos h'] at hc
                              injection hc with hc
                              set assignment' : Assignment c :=
                                { assignment with
                                  ff := fun n => if n = sconf.nextVarId then valueVal
                                    else assignment.ff n }
                                with hassignment'_def
                              have hagreeff : agreesOnFF (symEnvVars symEnv) assignment
                                  assignment' := by
                                intro n hn
                                have hne : n ≠ sconf.nextVarId :=
                                  Nat.ne_of_lt (hbelow (Var.ffv n) hn)
                                simp only [hassignment'_def, if_neg hne]
                              have hagreebool :
                                  agreesOnBool (symEnvVars symEnv) assignment assignment' :=
                                fun n _ => rfl
                              have hframeff : ∀ n, Var.ffv n ∉
                                  (ffVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
                                    (simpleSymValToTerm v)) ∪
                                   bVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
                                    (simpleSymValToTerm v))) →
                                  assignment'.ff n = assignment.ff n := by
                                intro n hn
                                have hne : n ≠ sconf.nextVarId := by
                                  intro heqn
                                  apply hn
                                  rw [heqn]
                                  exact Std.TreeSet.mem_union_of_left hmemF
                                simp only [hassignment'_def, if_neg hne]
                              have hframebool : ∀ n, Var.boolv n ∉
                                  (ffVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
                                    (simpleSymValToTerm v)) ∪
                                   bVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
                                    (simpleSymValToTerm v))) →
                                  assignment'.bool n = assignment.bool n := fun n _ => rfl
                              have hsimpleMatchV' : simpleValMatches assignment' v valueVal :=
                                simpleValMatches_agreesOnFF_preserves assignment assignment' v
                                  valueVal (symEnvVars symEnv) hsub_v hagreeff hvmatch
                              have hevalTermV' : evalTerm gconf assignment'
                                  (simpleSymValToTerm v) (specs.map (·.f)) = Except.ok valueVal :=
                                evalTerm_simpleSymValToTerm gconf assignment' v valueVal
                                  (specs.map (·.f)) hsimpleMatchV'
                              have hffeval : assignment'.ff sconf.nextVarId = valueVal := by
                                simp [hassignment'_def]
                              have hsub_arr_elems : ∀ sv ∈ arr.toList,
                                  simpleValVars sv ⊆ symEnvVars symEnv :=
                                fun sv hsv => symValVars_array_mem_below_subset arr sv hsv
                                  (symEnvVars symEnv) hsub_arr
                              have hvv' : List.Forall₂ (simpleValMatches assignment') arr.toList
                                  varr.toList :=
                                forall2_simpleValMatches_agreesOnFF_preserves assignment
                                  assignment' arr.toList varr.toList (symEnvVars symEnv)
                                  hsub_arr_elems hagreeff hvv
                              have hnewElemMatch : simpleValMatches assignment'
                                  (SimpleSymVal.ffvar ⟨sconf.nextVarId, none⟩) valueVal := by
                                simp only [simpleValMatches, hffeval]
                              have hmatchArr : List.Forall₂ (simpleValMatches assignment')
                                  (arr.set indexValue.val
                                    (SimpleSymVal.ffvar ⟨sconf.nextVarId, none⟩)).toList
                                  (varr.set indexValue.val valueVal).toList := by
                                rw [Array.toList_set, Array.toList_set]
                                exact list_forall2_set hvv' indexValue.val
                                  (SimpleSymVal.ffvar ⟨sconf.nextVarId, none⟩) valueVal
                                  hnewElemMatch
                              refine ⟨assignment', hagreeff, hagreebool, hframeff, hframebool, ?_,
                                ?_⟩
                              · simp [evalFormula, evalTerm, hevalTermV', hffeval]
                              · rw [← hc]
                                exact EnvMatches_setVar assignment' symEnv env a
                                  (SymValue.array (arr.set indexValue.val
                                    (SimpleSymVal.ffvar ⟨sconf.nextVarId, none⟩)))
                                  (Value.array (varr.set indexValue.val valueVal))
                                  (EnvMatches_agreesOnFF_preserves assignment assignment' symEnv
                                    env hagreeff hmatch)
                                  (by simp only [symValMatches]; exact hmatchArr)
                        · intro env assignment hmatch assignment' hagree heval_f
                          have hmatch' : EnvMatches assignment' symEnv env :=
                            EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env
                              hagree hmatch
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
                                resolveSimpleExpr_correct symEnv value env assignment' v hmatch'
                                  hval
                              have hevalTermV' : evalTerm gconf assignment'
                                  (simpleSymValToTerm v) (specs.map (·.f)) = Except.ok valueVal :=
                                evalTerm_simpleSymValToTerm gconf assignment' v valueVal
                                  (specs.map (·.f)) hvmatch
                              simp only [evalFormula, evalTerm, hevalTermV', Except.ok.injEq]
                                at heval_f
                              have hffeq : assignment'.ff sconf.nextVarId = valueVal :=
                                (beq_iff_eq ..).mp heval_f
                              have hnewElemMatch : simpleValMatches assignment'
                                  (SimpleSymVal.ffvar ⟨sconf.nextVarId, none⟩) valueVal := by
                                simp only [simpleValMatches, hffeq]
                              have hmatchArr : List.Forall₂ (simpleValMatches assignment')
                                  (arr.set indexValue.val
                                    (SimpleSymVal.ffvar ⟨sconf.nextVarId, none⟩)).toList
                                  (varr.set indexValue.val valueVal).toList := by
                                rw [Array.toList_set, Array.toList_set]
                                exact list_forall2_set hvv indexValue.val
                                  (SimpleSymVal.ffvar ⟨sconf.nextVarId, none⟩) valueVal
                                  hnewElemMatch
                              refine ⟨Corellzk2smt.Language.Core.Semantics.Basic.setVar env a
                                (Value.array (varr.set indexValue.val valueVal)), ?_, ?_⟩
                              · simp only [evalWriteArray, hceval, hvalceval,
                                  Corellzk2smt.Language.Core.Semantics.Basic.getVar, henv,
                                  ← Std.TreeMap.get?_eq_getElem?, dif_pos h']
                              · exact EnvMatches_setVar assignment' symEnv env a
                                  (SymValue.array (arr.set indexValue.val
                                    (SimpleSymVal.ffvar ⟨sconf.nextVarId, none⟩)))
                                  (Value.array (varr.set indexValue.val valueVal)) hmatch'
                                  (by simp only [symValMatches]; exact hmatchArr)
                    | false =>
                        simp only [seWriteArrayConstantIdx, hidx,
                          Corellzk2smt.SymExec.Basic.getVar, ← Std.TreeMap.get?_eq_getElem?, hg,
                          dif_pos h, hval, hnew] at hspec_eq
                        injection hspec_eq with hspec_eq
                        subst hspec_eq
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
                        refine ⟨rfl, le_refl _, ?_, ?_, ?_, ?_, ValidBinRep_trivial gconf _ _, ?_,
                          ?_⟩
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
                                resolveSimpleExpr_correct symEnv value env assignment v hmatch
                                  hval
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
                                resolveSimpleExpr_correct symEnv value env assignment' v hmatch'
                                  hval
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
