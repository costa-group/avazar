import Corellzk2smt.SymExec.Correctness.Lemmas
import Corellzk2smt.SymExec.Correctness.FuncCallCorrectness
import Corellzk2smt.SymExec.Correctness.BinaryExpansionCorrectness
import Corellzk2smt.SymExec.BoolExpr

/-!
Correctness statements for the boolean-valued `seExprXXX` operations (`SymExec/BoolExpr.lean`)
against their concrete `Expr`-level counterparts. Every one of these is currently an honest
`sorry` -- each `seExprXXX` is a permanent `"Not implemented yet"` stub (`Except.error`), so its
`TranslatesExprCorrectly` obligation would be vacuously provable that way, but that proves the
wrong thing (see `AssignmentCorrectness.lean`'s `seEvalExpr_correct` docstring for the same
reasoning). Left open until each operator is actually implemented -- `seEvalExpr_correct`
dispatches to these by name, so discharging one of these `sorry`s is exactly what's needed to make
that operator's case of `seEvalExpr_correct` (and hence `seEvalAssignmentNonConst_correct`) real.
-/

namespace Corellzk2smt.SymExec.Correctness.BoolExprCorrectness

open Corellzk2smt.Config
open Corellzk2smt.Language.Core.Syntax.AST
open Corellzk2smt.Language.Core.Semantics.Basic
open Corellzk2smt.SymExec.Basic
open Corellzk2smt.SymExec.BigStep
open Corellzk2smt.FFConstraints.Basic
open Corellzk2smt.FFConstraints.Satisfiability
open Corellzk2smt.FFConstraints.Lemmas
open Corellzk2smt.SymExec.Correctness.Lemmas
open Corellzk2smt.SymExec.Correctness.BinaryExpansionCorrectness
open Corellzk2smt.SymExec.Correctness.FuncCallCorrectness
open Corellzk2smt.SymExec.BinaryExpansion

/-- `seExprBor` mints one fresh var `outFFVar`, tied down by a single equation to a term-level
    `ite` over the condition "both operands are `0`" -- `outFFVar = 0` when `v1Term = 0 ∧ v2Term =
    0`, `1` otherwise -- lining up exactly with `evalBor`'s own `if v1 = 0 && v2 = 0 then 0 else
    1`, plus the same `bool_ffterm` boolean tag as `seExprEq`. -/
theorem seExprBor_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD) (e1 e2 : SimpleExpr c) :
    TranslatesExprCorrectly gconf sconf specs ctx
      (fun env => Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env
        (Expr.bop BinOp.bor e1 e2))
      (fun symEnv => seExprBor md gconf sconf symEnv specs e1 e2) := by
  intro symEnv hbelow _hvalid espec hspec_eq
  simp only [seExprBor] at hspec_eq
  cases hres1 : resolveSimpleExpr symEnv e1 with
  | error msg => rw [hres1] at hspec_eq; simp at hspec_eq
  | ok v1 =>
      rw [hres1] at hspec_eq
      cases hres2 : resolveSimpleExpr symEnv e2 with
      | error msg => rw [hres2] at hspec_eq; simp at hspec_eq
      | ok v2 =>
          rw [hres2] at hspec_eq
          cases hbool : bool_ffterm gconf sconf (FFTerm.var sconf.nextVarId) with
          | error msg => rw [hbool] at hspec_eq; simp at hspec_eq
          | ok fbool =>
          rw [hbool] at hspec_eq
          injection hspec_eq with hspec_eq
          subst hspec_eq
          have hsub1 := Corellzk2smt.SymExec.Correctness.Lemmas.resolveSimpleExpr_vars_subset
            symEnv e1 v1 hres1
          have hsub2 := Corellzk2smt.SymExec.Correctness.Lemmas.resolveSimpleExpr_vars_subset
            symEnv e2 v2 hres2
          have hmemF_eq : Var.ffv sconf.nextVarId ∈
              ffVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
                (FFTerm.ite
                  (FFFormula.and (FFFormula.eq (simpleSymValToTerm v1) (FFTerm.val 0))
                    (FFFormula.eq (simpleSymValToTerm v2) (FFTerm.val 0)))
                  (FFTerm.val 0) (FFTerm.val 1))) := by
            simp only [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_union_iff]
            exact Or.inl (Std.TreeSet.mem_insert_self ..)
          have hmemF : Var.ffv sconf.nextVarId ∈
              ffVarsOfFormula (FFFormula.and
                (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (FFTerm.ite
                    (FFFormula.and (FFFormula.eq (simpleSymValToTerm v1) (FFTerm.val 0))
                      (FFFormula.eq (simpleSymValToTerm v2) (FFTerm.val 0)))
                    (FFTerm.val 0) (FFTerm.val 1)))
                fbool) := by
            simp only [ffVarsOfFormula]
            exact Std.TreeSet.mem_union_of_left hmemF_eq
          refine ⟨Nat.le_succ _, ?_, ?_, ?_, varSetBelow_mono (Nat.le_succ _) hbelow,
            fun v' hv' => Or.inl hv', ValidBinRep_trivial gconf _ _, ?_, ?_⟩
          · intro v' hv'
            simp only [simpleValVars, simpleValOwnVars, Option.map_none, Option.getD_none,
              Std.TreeSet.mem_union_iff] at hv'
            rcases hv' with h | h
            · rcases Std.TreeSet.mem_insert.mp h with heq | hmem
              · rw [← Var_compare_eq_iff_eq.mp heq]
                exact Or.inr (Std.TreeSet.mem_union_of_left hmemF)
              · exact absurd hmem Std.TreeSet.not_mem_emptyc
            · exact absurd h Std.TreeSet.not_mem_emptyc
          · intro v' hv'
            simp only [exprSpecVars] at hv'
            rcases Std.TreeSet.mem_union_iff.mp hv' with hff_top | hb_top
            · simp only [ffVarsOfFormula] at hff_top
              rcases Std.TreeSet.mem_union_iff.mp hff_top with hff | hfbool
              · simp only [ffVarsOfFormula, ffVarsOfTerm, ffVarsOfTerm_simpleSymValToTerm,
                  Std.TreeSet.mem_union_iff] at hff
                rcases hff with h1 | ((((h2 | h3) | (h4 | h5)) | h6) | h7)
                · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
                  · rw [← Var_compare_eq_iff_eq.mp heq]
                    exact Or.inr (le_refl _)
                  · exact absurd hmem Std.TreeSet.not_mem_emptyc
                · exact Or.inl (hsub1 v' (simpleValOwnVars_subset_simpleValVars v1 v' h2))
                · exact absurd h3 Std.TreeSet.not_mem_emptyc
                · exact Or.inl (hsub2 v' (simpleValOwnVars_subset_simpleValVars v2 v' h4))
                · exact absurd h5 Std.TreeSet.not_mem_emptyc
                · exact absurd h6 Std.TreeSet.not_mem_emptyc
                · exact absurd h7 Std.TreeSet.not_mem_emptyc
              · rw [mem_ffVarsOfFormula_bool_ffterm_var gconf sconf sconf.nextVarId fbool
                  hbool] at hfbool
                rw [← hfbool]
                exact Or.inr (le_refl _)
            · simp only [bVarsOfFormula] at hb_top
              rcases Std.TreeSet.mem_union_iff.mp hb_top with hb | hbbool
              · simp only [bVarsOfFormula, bVarsOfTerm, bVarsOfTerm_simpleSymValToTerm,
                  Std.TreeSet.mem_union_iff] at hb
                rcases hb with h | ((((h | h) | (h | h)) | h) | h) <;>
                  exact absurd h Std.TreeSet.not_mem_emptyc
              · exact absurd hbbool
                  (not_mem_bVarsOfFormula_bool_ffterm_var gconf sconf sconf.nextVarId fbool hbool
                    v')
          · intro v' hv'
            simp only [exprSpecVars] at hv'
            rcases Std.TreeSet.mem_union_iff.mp hv' with hff_top | hb_top
            · simp only [ffVarsOfFormula] at hff_top
              rcases Std.TreeSet.mem_union_iff.mp hff_top with hff | hfbool
              · simp only [ffVarsOfFormula, ffVarsOfTerm, ffVarsOfTerm_simpleSymValToTerm,
                  Std.TreeSet.mem_union_iff] at hff
                rcases hff with h1 | ((((h2 | h3) | (h4 | h5)) | h6) | h7)
                · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
                  · rw [← Var_compare_eq_iff_eq.mp heq]
                    simp only [varIndex]
                    omega
                  · exact absurd hmem Std.TreeSet.not_mem_emptyc
                · exact lt_of_lt_of_le
                    (hbelow v' (hsub1 v' (simpleValOwnVars_subset_simpleValVars v1 v' h2)))
                    (Nat.le_succ _)
                · exact absurd h3 Std.TreeSet.not_mem_emptyc
                · exact lt_of_lt_of_le
                    (hbelow v' (hsub2 v' (simpleValOwnVars_subset_simpleValVars v2 v' h4)))
                    (Nat.le_succ _)
                · exact absurd h5 Std.TreeSet.not_mem_emptyc
                · exact absurd h6 Std.TreeSet.not_mem_emptyc
                · exact absurd h7 Std.TreeSet.not_mem_emptyc
              · rw [mem_ffVarsOfFormula_bool_ffterm_var gconf sconf sconf.nextVarId fbool
                  hbool] at hfbool
                rw [← hfbool]
                simp only [varIndex]
                omega
            · simp only [bVarsOfFormula] at hb_top
              rcases Std.TreeSet.mem_union_iff.mp hb_top with hb | hbbool
              · simp only [bVarsOfFormula, bVarsOfTerm, bVarsOfTerm_simpleSymValToTerm,
                  Std.TreeSet.mem_union_iff] at hb
                rcases hb with h | ((((h | h) | (h | h)) | h) | h) <;>
                  exact absurd h Std.TreeSet.not_mem_emptyc
              · exact absurd hbbool
                  (not_mem_bVarsOfFormula_bool_ffterm_var gconf sconf sconf.nextVarId fbool hbool
                    v')
          · intro env assignment hmatch val hval
            obtain ⟨val1', hval1', hm1⟩ :=
              resolveSimpleExpr_correct symEnv e1 env assignment v1 hmatch hres1
            obtain ⟨val2', hval2', hm2⟩ :=
              resolveSimpleExpr_correct symEnv e2 env assignment v2 hmatch hres2
            simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval1',
              hval2'] at hval
            injection hval with hval
            subst hval
            set assignment' : Assignment c :=
              { assignment with
                ff := fun n => if n = sconf.nextVarId then evalBor val1' val2'
                    else assignment.ff n }
              with hassignment'_def
            have hagreeff : agreesOnFF (symEnvVars symEnv) assignment assignment' := by
              intro n hn
              have hne : n ≠ sconf.nextVarId := Nat.ne_of_lt (hbelow (Var.ffv n) hn)
              simp only [hassignment'_def, if_neg hne]
            have hagreebool : agreesOnBool (symEnvVars symEnv) assignment assignment' :=
              fun n _ => rfl
            have hframeff : ∀ n, Var.ffv n ∉
                (ffVarsOfFormula (FFFormula.and
                  (FFFormula.eq (FFTerm.var sconf.nextVarId)
                    (FFTerm.ite
                      (FFFormula.and (FFFormula.eq (simpleSymValToTerm v1) (FFTerm.val 0))
                        (FFFormula.eq (simpleSymValToTerm v2) (FFTerm.val 0)))
                      (FFTerm.val 0) (FFTerm.val 1)))
                  fbool) ∪
                 bVarsOfFormula (FFFormula.and
                  (FFFormula.eq (FFTerm.var sconf.nextVarId)
                    (FFTerm.ite
                      (FFFormula.and (FFFormula.eq (simpleSymValToTerm v1) (FFTerm.val 0))
                        (FFFormula.eq (simpleSymValToTerm v2) (FFTerm.val 0)))
                      (FFTerm.val 0) (FFTerm.val 1)))
                  fbool)) →
                assignment'.ff n = assignment.ff n := by
              intro n hn
              have hne : n ≠ sconf.nextVarId := by
                intro heqn
                apply hn
                rw [heqn]
                exact Std.TreeSet.mem_union_of_left hmemF
              simp only [hassignment'_def, if_neg hne]
            have hframebool : ∀ n, Var.boolv n ∉
                (ffVarsOfFormula (FFFormula.and
                  (FFFormula.eq (FFTerm.var sconf.nextVarId)
                    (FFTerm.ite
                      (FFFormula.and (FFFormula.eq (simpleSymValToTerm v1) (FFTerm.val 0))
                        (FFFormula.eq (simpleSymValToTerm v2) (FFTerm.val 0)))
                      (FFTerm.val 0) (FFTerm.val 1)))
                  fbool) ∪
                 bVarsOfFormula (FFFormula.and
                  (FFFormula.eq (FFTerm.var sconf.nextVarId)
                    (FFTerm.ite
                      (FFFormula.and (FFFormula.eq (simpleSymValToTerm v1) (FFTerm.val 0))
                        (FFFormula.eq (simpleSymValToTerm v2) (FFTerm.val 0)))
                      (FFTerm.val 0) (FFTerm.val 1)))
                  fbool)) →
                assignment'.bool n = assignment.bool n := fun n _ => rfl
            have hsimpleMatch1' : simpleValMatches assignment' v1 val1' :=
              simpleValMatches_agreesOnFF_preserves assignment assignment' v1 val1'
                (symEnvVars symEnv) hsub1 hagreeff hm1
            have hsimpleMatch2' : simpleValMatches assignment' v2 val2' :=
              simpleValMatches_agreesOnFF_preserves assignment assignment' v2 val2'
                (symEnvVars symEnv) hsub2 hagreeff hm2
            have hevalTerm1' : evalTerm gconf assignment' (simpleSymValToTerm v1)
                (specs.map (·.f)) = Except.ok val1' :=
              evalTerm_simpleSymValToTerm gconf assignment' v1 val1' (specs.map (·.f))
                hsimpleMatch1'
            have hevalTerm2' : evalTerm gconf assignment' (simpleSymValToTerm v2)
                (specs.map (·.f)) = Except.ok val2' :=
              evalTerm_simpleSymValToTerm gconf assignment' v2 val2' (specs.map (·.f))
                hsimpleMatch2'
            have hffeval : assignment'.ff sconf.nextVarId = evalBor val1' val2' := by
              simp [hassignment'_def]
            have hiteEval : evalTerm gconf assignment'
                (FFTerm.ite
                  (FFFormula.and (FFFormula.eq (simpleSymValToTerm v1) (FFTerm.val 0))
                    (FFFormula.eq (simpleSymValToTerm v2) (FFTerm.val 0)))
                  (FFTerm.val 0) (FFTerm.val 1)) (specs.map (·.f))
                = Except.ok (evalBor val1' val2') := by
              simp only [evalBor]
              by_cases h1 : val1' = 0 <;> by_cases h2 : val2' = 0 <;>
                simp [evalTerm, evalFormula, hevalTerm1', hevalTerm2', h1, h2]
            have hf_eq_true : evalFormula gconf assignment'
                (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (FFTerm.ite
                    (FFFormula.and (FFFormula.eq (simpleSymValToTerm v1) (FFTerm.val 0))
                      (FFFormula.eq (simpleSymValToTerm v2) (FFTerm.val 0)))
                    (FFTerm.val 0) (FFTerm.val 1))) (specs.map (·.f)) = Except.ok true := by
              simp [evalFormula, evalTerm, hiteEval, hffeval]
            have hf_bool_true : evalFormula gconf assignment'
                fbool (specs.map (·.f))
                = Except.ok true := by
              rw [evalFormula_bool_ffterm_var_iff gconf sconf assignment' (specs.map (·.f))
                sconf.nextVarId fbool hbool, hffeval]
              simp only [evalBor]
              by_cases h1 : val1' = 0 <;> by_cases h2 : val2' = 0 <;> simp [h1, h2]
            refine ⟨assignment', hagreeff, hagreebool, hframeff, hframebool, ?_,
              EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagreeff hmatch,
              ?_⟩
            · exact evalFormula_and_intro gconf assignment'
                (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (FFTerm.ite
                    (FFFormula.and (FFFormula.eq (simpleSymValToTerm v1) (FFTerm.val 0))
                      (FFFormula.eq (simpleSymValToTerm v2) (FFTerm.val 0)))
                    (FFTerm.val 0) (FFTerm.val 1)))
                fbool (specs.map (·.f))
                hf_eq_true hf_bool_true
            · simp only [simpleValMatches, hffeval]
          · intro env assignment hmatch assignment' hagree heval_f
            have hmatch' : EnvMatches assignment' symEnv env :=
              EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagree hmatch
            obtain ⟨val1', hval1', hm1'⟩ :=
              resolveSimpleExpr_correct symEnv e1 env assignment' v1 hmatch' hres1
            obtain ⟨val2', hval2', hm2'⟩ :=
              resolveSimpleExpr_correct symEnv e2 env assignment' v2 hmatch' hres2
            have hevalTerm1' : evalTerm gconf assignment' (simpleSymValToTerm v1)
                (specs.map (·.f)) = Except.ok val1' :=
              evalTerm_simpleSymValToTerm gconf assignment' v1 val1' (specs.map (·.f)) hm1'
            have hevalTerm2' : evalTerm gconf assignment' (simpleSymValToTerm v2)
                (specs.map (·.f)) = Except.ok val2' :=
              evalTerm_simpleSymValToTerm gconf assignment' v2 val2' (specs.map (·.f)) hm2'
            have hiteEval : evalTerm gconf assignment'
                (FFTerm.ite
                  (FFFormula.and (FFFormula.eq (simpleSymValToTerm v1) (FFTerm.val 0))
                    (FFFormula.eq (simpleSymValToTerm v2) (FFTerm.val 0)))
                  (FFTerm.val 0) (FFTerm.val 1)) (specs.map (·.f))
                = Except.ok (evalBor val1' val2') := by
              simp only [evalBor]
              by_cases h1 : val1' = 0 <;> by_cases h2 : val2' = 0 <;>
                simp [evalTerm, evalFormula, hevalTerm1', hevalTerm2', h1, h2]
            obtain ⟨heval_feq, _heval_fbool⟩ :=
              evalFormula_and_elim gconf assignment'
                (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (FFTerm.ite
                    (FFFormula.and (FFFormula.eq (simpleSymValToTerm v1) (FFTerm.val 0))
                      (FFFormula.eq (simpleSymValToTerm v2) (FFTerm.val 0)))
                    (FFTerm.val 0) (FFTerm.val 1)))
                fbool (specs.map (·.f)) heval_f
            simp only [evalFormula, evalTerm, hiteEval, Except.ok.injEq] at heval_feq
            have hffeq : assignment'.ff sconf.nextVarId = evalBor val1' val2' :=
              (beq_iff_eq ..).mp heval_feq
            refine ⟨evalBor val1' val2', ?_, hmatch', ?_⟩
            · simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval1', hval2',
                evalBor]
            · simp only [simpleValMatches, hffeq]

/-- `seExprBAnd` mints one fresh var `outFFVar`, tied down by a single equation to a term-level
    `ite` over the condition "either operand is `0`" -- `outFFVar = 0` when `v1Term = 0 ∨ v2Term =
    0`, `1` otherwise -- lining up exactly with `evalBand`'s own `if v1 = 0 || v2 = 0 then 0 else
    1`, plus the same `bool_ffterm` boolean tag as `seExprEq`. -/
theorem seExprBAnd_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD) (e1 e2 : SimpleExpr c) :
    TranslatesExprCorrectly gconf sconf specs ctx
      (fun env => Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env
        (Expr.bop BinOp.band e1 e2))
      (fun symEnv => seExprBAnd md gconf sconf symEnv specs e1 e2) := by
  intro symEnv hbelow _hvalid espec hspec_eq
  simp only [seExprBAnd] at hspec_eq
  cases hres1 : resolveSimpleExpr symEnv e1 with
  | error msg => rw [hres1] at hspec_eq; simp at hspec_eq
  | ok v1 =>
      rw [hres1] at hspec_eq
      cases hres2 : resolveSimpleExpr symEnv e2 with
      | error msg => rw [hres2] at hspec_eq; simp at hspec_eq
      | ok v2 =>
          rw [hres2] at hspec_eq
          cases hbool : bool_ffterm gconf sconf (FFTerm.var sconf.nextVarId) with
          | error msg => rw [hbool] at hspec_eq; simp at hspec_eq
          | ok fbool =>
          rw [hbool] at hspec_eq
          injection hspec_eq with hspec_eq
          subst hspec_eq
          have hsub1 := Corellzk2smt.SymExec.Correctness.Lemmas.resolveSimpleExpr_vars_subset
            symEnv e1 v1 hres1
          have hsub2 := Corellzk2smt.SymExec.Correctness.Lemmas.resolveSimpleExpr_vars_subset
            symEnv e2 v2 hres2
          have hmemF_eq : Var.ffv sconf.nextVarId ∈
              ffVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
                (FFTerm.ite
                  (FFFormula.or (FFFormula.eq (simpleSymValToTerm v1) (FFTerm.val 0))
                    (FFFormula.eq (simpleSymValToTerm v2) (FFTerm.val 0)))
                  (FFTerm.val 0) (FFTerm.val 1))) := by
            simp only [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_union_iff]
            exact Or.inl (Std.TreeSet.mem_insert_self ..)
          have hmemF : Var.ffv sconf.nextVarId ∈
              ffVarsOfFormula (FFFormula.and
                (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (FFTerm.ite
                    (FFFormula.or (FFFormula.eq (simpleSymValToTerm v1) (FFTerm.val 0))
                      (FFFormula.eq (simpleSymValToTerm v2) (FFTerm.val 0)))
                    (FFTerm.val 0) (FFTerm.val 1)))
                fbool) := by
            simp only [ffVarsOfFormula]
            exact Std.TreeSet.mem_union_of_left hmemF_eq
          refine ⟨Nat.le_succ _, ?_, ?_, ?_, varSetBelow_mono (Nat.le_succ _) hbelow,
            fun v' hv' => Or.inl hv', ValidBinRep_trivial gconf _ _, ?_, ?_⟩
          · intro v' hv'
            simp only [simpleValVars, simpleValOwnVars, Option.map_none, Option.getD_none,
              Std.TreeSet.mem_union_iff] at hv'
            rcases hv' with h | h
            · rcases Std.TreeSet.mem_insert.mp h with heq | hmem
              · rw [← Var_compare_eq_iff_eq.mp heq]
                exact Or.inr (Std.TreeSet.mem_union_of_left hmemF)
              · exact absurd hmem Std.TreeSet.not_mem_emptyc
            · exact absurd h Std.TreeSet.not_mem_emptyc
          · intro v' hv'
            simp only [exprSpecVars] at hv'
            rcases Std.TreeSet.mem_union_iff.mp hv' with hff_top | hb_top
            · simp only [ffVarsOfFormula] at hff_top
              rcases Std.TreeSet.mem_union_iff.mp hff_top with hff | hfbool
              · simp only [ffVarsOfFormula, ffVarsOfTerm, ffVarsOfTerm_simpleSymValToTerm,
                  Std.TreeSet.mem_union_iff] at hff
                rcases hff with h1 | ((((h2 | h3) | (h4 | h5)) | h6) | h7)
                · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
                  · rw [← Var_compare_eq_iff_eq.mp heq]
                    exact Or.inr (le_refl _)
                  · exact absurd hmem Std.TreeSet.not_mem_emptyc
                · exact Or.inl (hsub1 v' (simpleValOwnVars_subset_simpleValVars v1 v' h2))
                · exact absurd h3 Std.TreeSet.not_mem_emptyc
                · exact Or.inl (hsub2 v' (simpleValOwnVars_subset_simpleValVars v2 v' h4))
                · exact absurd h5 Std.TreeSet.not_mem_emptyc
                · exact absurd h6 Std.TreeSet.not_mem_emptyc
                · exact absurd h7 Std.TreeSet.not_mem_emptyc
              · rw [mem_ffVarsOfFormula_bool_ffterm_var gconf sconf sconf.nextVarId fbool
                  hbool] at hfbool
                rw [← hfbool]
                exact Or.inr (le_refl _)
            · simp only [bVarsOfFormula] at hb_top
              rcases Std.TreeSet.mem_union_iff.mp hb_top with hb | hbbool
              · simp only [bVarsOfFormula, bVarsOfTerm, bVarsOfTerm_simpleSymValToTerm,
                  Std.TreeSet.mem_union_iff] at hb
                rcases hb with h | ((((h | h) | (h | h)) | h) | h) <;>
                  exact absurd h Std.TreeSet.not_mem_emptyc
              · exact absurd hbbool
                  (not_mem_bVarsOfFormula_bool_ffterm_var gconf sconf sconf.nextVarId fbool hbool
                    v')
          · intro v' hv'
            simp only [exprSpecVars] at hv'
            rcases Std.TreeSet.mem_union_iff.mp hv' with hff_top | hb_top
            · simp only [ffVarsOfFormula] at hff_top
              rcases Std.TreeSet.mem_union_iff.mp hff_top with hff | hfbool
              · simp only [ffVarsOfFormula, ffVarsOfTerm, ffVarsOfTerm_simpleSymValToTerm,
                  Std.TreeSet.mem_union_iff] at hff
                rcases hff with h1 | ((((h2 | h3) | (h4 | h5)) | h6) | h7)
                · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
                  · rw [← Var_compare_eq_iff_eq.mp heq]
                    simp only [varIndex]
                    omega
                  · exact absurd hmem Std.TreeSet.not_mem_emptyc
                · exact lt_of_lt_of_le
                    (hbelow v' (hsub1 v' (simpleValOwnVars_subset_simpleValVars v1 v' h2)))
                    (Nat.le_succ _)
                · exact absurd h3 Std.TreeSet.not_mem_emptyc
                · exact lt_of_lt_of_le
                    (hbelow v' (hsub2 v' (simpleValOwnVars_subset_simpleValVars v2 v' h4)))
                    (Nat.le_succ _)
                · exact absurd h5 Std.TreeSet.not_mem_emptyc
                · exact absurd h6 Std.TreeSet.not_mem_emptyc
                · exact absurd h7 Std.TreeSet.not_mem_emptyc
              · rw [mem_ffVarsOfFormula_bool_ffterm_var gconf sconf sconf.nextVarId fbool
                  hbool] at hfbool
                rw [← hfbool]
                simp only [varIndex]
                omega
            · simp only [bVarsOfFormula] at hb_top
              rcases Std.TreeSet.mem_union_iff.mp hb_top with hb | hbbool
              · simp only [bVarsOfFormula, bVarsOfTerm, bVarsOfTerm_simpleSymValToTerm,
                  Std.TreeSet.mem_union_iff] at hb
                rcases hb with h | ((((h | h) | (h | h)) | h) | h) <;>
                  exact absurd h Std.TreeSet.not_mem_emptyc
              · exact absurd hbbool
                  (not_mem_bVarsOfFormula_bool_ffterm_var gconf sconf sconf.nextVarId fbool hbool
                    v')
          · intro env assignment hmatch val hval
            obtain ⟨val1', hval1', hm1⟩ :=
              resolveSimpleExpr_correct symEnv e1 env assignment v1 hmatch hres1
            obtain ⟨val2', hval2', hm2⟩ :=
              resolveSimpleExpr_correct symEnv e2 env assignment v2 hmatch hres2
            simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval1',
              hval2'] at hval
            injection hval with hval
            subst hval
            set assignment' : Assignment c :=
              { assignment with
                ff := fun n => if n = sconf.nextVarId then evalBand val1' val2'
                    else assignment.ff n }
              with hassignment'_def
            have hagreeff : agreesOnFF (symEnvVars symEnv) assignment assignment' := by
              intro n hn
              have hne : n ≠ sconf.nextVarId := Nat.ne_of_lt (hbelow (Var.ffv n) hn)
              simp only [hassignment'_def, if_neg hne]
            have hagreebool : agreesOnBool (symEnvVars symEnv) assignment assignment' :=
              fun n _ => rfl
            have hframeff : ∀ n, Var.ffv n ∉
                (ffVarsOfFormula (FFFormula.and
                  (FFFormula.eq (FFTerm.var sconf.nextVarId)
                    (FFTerm.ite
                      (FFFormula.or (FFFormula.eq (simpleSymValToTerm v1) (FFTerm.val 0))
                        (FFFormula.eq (simpleSymValToTerm v2) (FFTerm.val 0)))
                      (FFTerm.val 0) (FFTerm.val 1)))
                  fbool) ∪
                 bVarsOfFormula (FFFormula.and
                  (FFFormula.eq (FFTerm.var sconf.nextVarId)
                    (FFTerm.ite
                      (FFFormula.or (FFFormula.eq (simpleSymValToTerm v1) (FFTerm.val 0))
                        (FFFormula.eq (simpleSymValToTerm v2) (FFTerm.val 0)))
                      (FFTerm.val 0) (FFTerm.val 1)))
                  fbool)) →
                assignment'.ff n = assignment.ff n := by
              intro n hn
              have hne : n ≠ sconf.nextVarId := by
                intro heqn
                apply hn
                rw [heqn]
                exact Std.TreeSet.mem_union_of_left hmemF
              simp only [hassignment'_def, if_neg hne]
            have hframebool : ∀ n, Var.boolv n ∉
                (ffVarsOfFormula (FFFormula.and
                  (FFFormula.eq (FFTerm.var sconf.nextVarId)
                    (FFTerm.ite
                      (FFFormula.or (FFFormula.eq (simpleSymValToTerm v1) (FFTerm.val 0))
                        (FFFormula.eq (simpleSymValToTerm v2) (FFTerm.val 0)))
                      (FFTerm.val 0) (FFTerm.val 1)))
                  fbool) ∪
                 bVarsOfFormula (FFFormula.and
                  (FFFormula.eq (FFTerm.var sconf.nextVarId)
                    (FFTerm.ite
                      (FFFormula.or (FFFormula.eq (simpleSymValToTerm v1) (FFTerm.val 0))
                        (FFFormula.eq (simpleSymValToTerm v2) (FFTerm.val 0)))
                      (FFTerm.val 0) (FFTerm.val 1)))
                  fbool)) →
                assignment'.bool n = assignment.bool n := fun n _ => rfl
            have hsimpleMatch1' : simpleValMatches assignment' v1 val1' :=
              simpleValMatches_agreesOnFF_preserves assignment assignment' v1 val1'
                (symEnvVars symEnv) hsub1 hagreeff hm1
            have hsimpleMatch2' : simpleValMatches assignment' v2 val2' :=
              simpleValMatches_agreesOnFF_preserves assignment assignment' v2 val2'
                (symEnvVars symEnv) hsub2 hagreeff hm2
            have hevalTerm1' : evalTerm gconf assignment' (simpleSymValToTerm v1)
                (specs.map (·.f)) = Except.ok val1' :=
              evalTerm_simpleSymValToTerm gconf assignment' v1 val1' (specs.map (·.f))
                hsimpleMatch1'
            have hevalTerm2' : evalTerm gconf assignment' (simpleSymValToTerm v2)
                (specs.map (·.f)) = Except.ok val2' :=
              evalTerm_simpleSymValToTerm gconf assignment' v2 val2' (specs.map (·.f))
                hsimpleMatch2'
            have hffeval : assignment'.ff sconf.nextVarId = evalBand val1' val2' := by
              simp [hassignment'_def]
            have hiteEval : evalTerm gconf assignment'
                (FFTerm.ite
                  (FFFormula.or (FFFormula.eq (simpleSymValToTerm v1) (FFTerm.val 0))
                    (FFFormula.eq (simpleSymValToTerm v2) (FFTerm.val 0)))
                  (FFTerm.val 0) (FFTerm.val 1)) (specs.map (·.f))
                = Except.ok (evalBand val1' val2') := by
              simp only [evalBand]
              by_cases h1 : val1' = 0 <;> by_cases h2 : val2' = 0 <;>
                simp [evalTerm, evalFormula, hevalTerm1', hevalTerm2', h1, h2]
            have hf_eq_true : evalFormula gconf assignment'
                (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (FFTerm.ite
                    (FFFormula.or (FFFormula.eq (simpleSymValToTerm v1) (FFTerm.val 0))
                      (FFFormula.eq (simpleSymValToTerm v2) (FFTerm.val 0)))
                    (FFTerm.val 0) (FFTerm.val 1))) (specs.map (·.f)) = Except.ok true := by
              simp [evalFormula, evalTerm, hiteEval, hffeval]
            have hf_bool_true : evalFormula gconf assignment'
                fbool (specs.map (·.f))
                = Except.ok true := by
              rw [evalFormula_bool_ffterm_var_iff gconf sconf assignment' (specs.map (·.f))
                sconf.nextVarId fbool hbool, hffeval]
              simp only [evalBand]
              by_cases h1 : val1' = 0 <;> by_cases h2 : val2' = 0 <;> simp [h1, h2]
            refine ⟨assignment', hagreeff, hagreebool, hframeff, hframebool, ?_,
              EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagreeff hmatch,
              ?_⟩
            · exact evalFormula_and_intro gconf assignment'
                (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (FFTerm.ite
                    (FFFormula.or (FFFormula.eq (simpleSymValToTerm v1) (FFTerm.val 0))
                      (FFFormula.eq (simpleSymValToTerm v2) (FFTerm.val 0)))
                    (FFTerm.val 0) (FFTerm.val 1)))
                fbool (specs.map (·.f))
                hf_eq_true hf_bool_true
            · simp only [simpleValMatches, hffeval]
          · intro env assignment hmatch assignment' hagree heval_f
            have hmatch' : EnvMatches assignment' symEnv env :=
              EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagree hmatch
            obtain ⟨val1', hval1', hm1'⟩ :=
              resolveSimpleExpr_correct symEnv e1 env assignment' v1 hmatch' hres1
            obtain ⟨val2', hval2', hm2'⟩ :=
              resolveSimpleExpr_correct symEnv e2 env assignment' v2 hmatch' hres2
            have hevalTerm1' : evalTerm gconf assignment' (simpleSymValToTerm v1)
                (specs.map (·.f)) = Except.ok val1' :=
              evalTerm_simpleSymValToTerm gconf assignment' v1 val1' (specs.map (·.f)) hm1'
            have hevalTerm2' : evalTerm gconf assignment' (simpleSymValToTerm v2)
                (specs.map (·.f)) = Except.ok val2' :=
              evalTerm_simpleSymValToTerm gconf assignment' v2 val2' (specs.map (·.f)) hm2'
            have hiteEval : evalTerm gconf assignment'
                (FFTerm.ite
                  (FFFormula.or (FFFormula.eq (simpleSymValToTerm v1) (FFTerm.val 0))
                    (FFFormula.eq (simpleSymValToTerm v2) (FFTerm.val 0)))
                  (FFTerm.val 0) (FFTerm.val 1)) (specs.map (·.f))
                = Except.ok (evalBand val1' val2') := by
              simp only [evalBand]
              by_cases h1 : val1' = 0 <;> by_cases h2 : val2' = 0 <;>
                simp [evalTerm, evalFormula, hevalTerm1', hevalTerm2', h1, h2]
            obtain ⟨heval_feq, _heval_fbool⟩ :=
              evalFormula_and_elim gconf assignment'
                (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (FFTerm.ite
                    (FFFormula.or (FFFormula.eq (simpleSymValToTerm v1) (FFTerm.val 0))
                      (FFFormula.eq (simpleSymValToTerm v2) (FFTerm.val 0)))
                    (FFTerm.val 0) (FFTerm.val 1)))
                fbool (specs.map (·.f)) heval_f
            simp only [evalFormula, evalTerm, hiteEval, Except.ok.injEq] at heval_feq
            have hffeq : assignment'.ff sconf.nextVarId = evalBand val1' val2' :=
              (beq_iff_eq ..).mp heval_feq
            refine ⟨evalBand val1' val2', ?_, hmatch', ?_⟩
            · simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval1', hval2',
                evalBand]
            · simp only [simpleValMatches, hffeq]

/-- `seExprBNeg` mints one fresh var `outFFVar`, tied down by a single equation to a term-level
    `ite` on `vTerm = 0` -- `outFFVar = 1` when `vTerm = 0`, `0` otherwise -- lining up exactly
    with `evalBneg`'s own `if v = 0 then 1 else 0`, plus the same `bool_ffterm` boolean tag as
    `seExprEq`. -/
theorem seExprBNeg_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD) (e1 : SimpleExpr c) :
    TranslatesExprCorrectly gconf sconf specs ctx
      (fun env => Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env (Expr.uop UnOp.bneg e1))
      (fun symEnv => seExprBNeg md gconf sconf symEnv specs e1) := by
  intro symEnv hbelow _hvalid espec hspec_eq
  simp only [seExprBNeg] at hspec_eq
  cases hres : resolveSimpleExpr symEnv e1 with
  | error msg => rw [hres] at hspec_eq; simp at hspec_eq
  | ok v =>
      rw [hres] at hspec_eq
      cases hbool : bool_ffterm gconf sconf (FFTerm.var sconf.nextVarId) with
      | error msg => rw [hbool] at hspec_eq; simp at hspec_eq
      | ok fbool =>
      rw [hbool] at hspec_eq
      injection hspec_eq with hspec_eq
      subst hspec_eq
      have hsub := Corellzk2smt.SymExec.Correctness.Lemmas.resolveSimpleExpr_vars_subset
        symEnv e1 v hres
      have hmemF_eq : Var.ffv sconf.nextVarId ∈
          ffVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
            (FFTerm.ite (FFFormula.eq (simpleSymValToTerm v) (FFTerm.val 0))
              (FFTerm.val 1) (FFTerm.val 0))) := by
        simp only [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_union_iff]
        exact Or.inl (Std.TreeSet.mem_insert_self ..)
      have hmemF : Var.ffv sconf.nextVarId ∈
          ffVarsOfFormula (FFFormula.and
            (FFFormula.eq (FFTerm.var sconf.nextVarId)
              (FFTerm.ite (FFFormula.eq (simpleSymValToTerm v) (FFTerm.val 0))
                (FFTerm.val 1) (FFTerm.val 0)))
            fbool) := by
        simp only [ffVarsOfFormula]
        exact Std.TreeSet.mem_union_of_left hmemF_eq
      refine ⟨Nat.le_succ _, ?_, ?_, ?_, varSetBelow_mono (Nat.le_succ _) hbelow,
        fun v' hv' => Or.inl hv', ValidBinRep_trivial gconf _ _, ?_, ?_⟩
      · intro v' hv'
        simp only [simpleValVars, simpleValOwnVars, Option.map_none, Option.getD_none,
          Std.TreeSet.mem_union_iff] at hv'
        rcases hv' with h | h
        · rcases Std.TreeSet.mem_insert.mp h with heq | hmem
          · rw [← Var_compare_eq_iff_eq.mp heq]
            exact Or.inr (Std.TreeSet.mem_union_of_left hmemF)
          · exact absurd hmem Std.TreeSet.not_mem_emptyc
        · exact absurd h Std.TreeSet.not_mem_emptyc
      · intro v' hv'
        simp only [exprSpecVars] at hv'
        rcases Std.TreeSet.mem_union_iff.mp hv' with hff_top | hb_top
        · simp only [ffVarsOfFormula] at hff_top
          rcases Std.TreeSet.mem_union_iff.mp hff_top with hff | hfbool
          · simp only [ffVarsOfFormula, ffVarsOfTerm, ffVarsOfTerm_simpleSymValToTerm,
              Std.TreeSet.mem_union_iff] at hff
            rcases hff with h1 | (((h2 | h3) | h4) | h5)
            · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
              · rw [← Var_compare_eq_iff_eq.mp heq]
                exact Or.inr (le_refl _)
              · exact absurd hmem Std.TreeSet.not_mem_emptyc
            · exact Or.inl (hsub v' (simpleValOwnVars_subset_simpleValVars v v' h2))
            · exact absurd h3 Std.TreeSet.not_mem_emptyc
            · exact absurd h4 Std.TreeSet.not_mem_emptyc
            · exact absurd h5 Std.TreeSet.not_mem_emptyc
          · rw [mem_ffVarsOfFormula_bool_ffterm_var gconf sconf sconf.nextVarId fbool
              hbool] at hfbool
            rw [← hfbool]
            exact Or.inr (le_refl _)
        · simp only [bVarsOfFormula] at hb_top
          rcases Std.TreeSet.mem_union_iff.mp hb_top with hb | hbbool
          · simp only [bVarsOfFormula, bVarsOfTerm, bVarsOfTerm_simpleSymValToTerm,
              Std.TreeSet.mem_union_iff] at hb
            rcases hb with h | (((h | h) | h) | h) <;> exact absurd h Std.TreeSet.not_mem_emptyc
          · exact absurd hbbool
              (not_mem_bVarsOfFormula_bool_ffterm_var gconf sconf sconf.nextVarId fbool hbool v')
      · intro v' hv'
        simp only [exprSpecVars] at hv'
        rcases Std.TreeSet.mem_union_iff.mp hv' with hff_top | hb_top
        · simp only [ffVarsOfFormula] at hff_top
          rcases Std.TreeSet.mem_union_iff.mp hff_top with hff | hfbool
          · simp only [ffVarsOfFormula, ffVarsOfTerm, ffVarsOfTerm_simpleSymValToTerm,
              Std.TreeSet.mem_union_iff] at hff
            rcases hff with h1 | (((h2 | h3) | h4) | h5)
            · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
              · rw [← Var_compare_eq_iff_eq.mp heq]
                simp only [varIndex]
                omega
              · exact absurd hmem Std.TreeSet.not_mem_emptyc
            · exact lt_of_lt_of_le
                (hbelow v' (hsub v' (simpleValOwnVars_subset_simpleValVars v v' h2)))
                (Nat.le_succ _)
            · exact absurd h3 Std.TreeSet.not_mem_emptyc
            · exact absurd h4 Std.TreeSet.not_mem_emptyc
            · exact absurd h5 Std.TreeSet.not_mem_emptyc
          · rw [mem_ffVarsOfFormula_bool_ffterm_var gconf sconf sconf.nextVarId fbool
              hbool] at hfbool
            rw [← hfbool]
            simp only [varIndex]
            omega
        · simp only [bVarsOfFormula] at hb_top
          rcases Std.TreeSet.mem_union_iff.mp hb_top with hb | hbbool
          · simp only [bVarsOfFormula, bVarsOfTerm, bVarsOfTerm_simpleSymValToTerm,
              Std.TreeSet.mem_union_iff] at hb
            rcases hb with h | (((h | h) | h) | h) <;> exact absurd h Std.TreeSet.not_mem_emptyc
          · exact absurd hbbool
              (not_mem_bVarsOfFormula_bool_ffterm_var gconf sconf sconf.nextVarId fbool hbool v')
      · intro env assignment hmatch val hval
        obtain ⟨val', hval', hm⟩ :=
          resolveSimpleExpr_correct symEnv e1 env assignment v hmatch hres
        simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval'] at hval
        injection hval with hval
        subst hval
        set assignment' : Assignment c :=
          { assignment with
            ff := fun n => if n = sconf.nextVarId then evalBneg val' else assignment.ff n }
          with hassignment'_def
        have hagreeff : agreesOnFF (symEnvVars symEnv) assignment assignment' := by
          intro n hn
          have hne : n ≠ sconf.nextVarId := Nat.ne_of_lt (hbelow (Var.ffv n) hn)
          simp only [hassignment'_def, if_neg hne]
        have hagreebool : agreesOnBool (symEnvVars symEnv) assignment assignment' :=
          fun n _ => rfl
        have hframeff : ∀ n, Var.ffv n ∉
            (ffVarsOfFormula (FFFormula.and
              (FFFormula.eq (FFTerm.var sconf.nextVarId)
                (FFTerm.ite (FFFormula.eq (simpleSymValToTerm v) (FFTerm.val 0))
                  (FFTerm.val 1) (FFTerm.val 0)))
              fbool) ∪
             bVarsOfFormula (FFFormula.and
              (FFFormula.eq (FFTerm.var sconf.nextVarId)
                (FFTerm.ite (FFFormula.eq (simpleSymValToTerm v) (FFTerm.val 0))
                  (FFTerm.val 1) (FFTerm.val 0)))
              fbool)) →
            assignment'.ff n = assignment.ff n := by
          intro n hn
          have hne : n ≠ sconf.nextVarId := by
            intro heqn
            apply hn
            rw [heqn]
            exact Std.TreeSet.mem_union_of_left hmemF
          simp only [hassignment'_def, if_neg hne]
        have hframebool : ∀ n, Var.boolv n ∉
            (ffVarsOfFormula (FFFormula.and
              (FFFormula.eq (FFTerm.var sconf.nextVarId)
                (FFTerm.ite (FFFormula.eq (simpleSymValToTerm v) (FFTerm.val 0))
                  (FFTerm.val 1) (FFTerm.val 0)))
              fbool) ∪
             bVarsOfFormula (FFFormula.and
              (FFFormula.eq (FFTerm.var sconf.nextVarId)
                (FFTerm.ite (FFFormula.eq (simpleSymValToTerm v) (FFTerm.val 0))
                  (FFTerm.val 1) (FFTerm.val 0)))
              fbool)) →
            assignment'.bool n = assignment.bool n := fun n _ => rfl
        have hsimpleMatch' : simpleValMatches assignment' v val' :=
          simpleValMatches_agreesOnFF_preserves assignment assignment' v val'
            (symEnvVars symEnv) hsub hagreeff hm
        have hevalTerm' : evalTerm gconf assignment' (simpleSymValToTerm v)
            (specs.map (·.f)) = Except.ok val' :=
          evalTerm_simpleSymValToTerm gconf assignment' v val' (specs.map (·.f)) hsimpleMatch'
        have hffeval : assignment'.ff sconf.nextVarId = evalBneg val' := by
          simp [hassignment'_def]
        have hiteEval : evalTerm gconf assignment'
            (FFTerm.ite (FFFormula.eq (simpleSymValToTerm v) (FFTerm.val 0))
              (FFTerm.val 1) (FFTerm.val 0)) (specs.map (·.f))
            = Except.ok (evalBneg val') := by
          simp only [evalBneg]
          by_cases h : val' = 0 <;> simp [evalTerm, evalFormula, hevalTerm', h]
        have hf_eq_true : evalFormula gconf assignment'
            (FFFormula.eq (FFTerm.var sconf.nextVarId)
              (FFTerm.ite (FFFormula.eq (simpleSymValToTerm v) (FFTerm.val 0))
                (FFTerm.val 1) (FFTerm.val 0))) (specs.map (·.f)) = Except.ok true := by
          simp [evalFormula, evalTerm, hiteEval, hffeval]
        have hf_bool_true : evalFormula gconf assignment'
            fbool (specs.map (·.f))
            = Except.ok true := by
          rw [evalFormula_bool_ffterm_var_iff gconf sconf assignment' (specs.map (·.f))
            sconf.nextVarId fbool hbool, hffeval]
          simp only [evalBneg]
          by_cases h : val' = 0 <;> simp [h]
        refine ⟨assignment', hagreeff, hagreebool, hframeff, hframebool, ?_,
          EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagreeff hmatch,
          ?_⟩
        · exact evalFormula_and_intro gconf assignment'
            (FFFormula.eq (FFTerm.var sconf.nextVarId)
              (FFTerm.ite (FFFormula.eq (simpleSymValToTerm v) (FFTerm.val 0))
                (FFTerm.val 1) (FFTerm.val 0)))
            fbool (specs.map (·.f))
            hf_eq_true hf_bool_true
        · simp only [simpleValMatches, hffeval]
      · intro env assignment hmatch assignment' hagree heval_f
        have hmatch' : EnvMatches assignment' symEnv env :=
          EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagree hmatch
        obtain ⟨val', hval', hm'⟩ :=
          resolveSimpleExpr_correct symEnv e1 env assignment' v hmatch' hres
        have hevalTerm' : evalTerm gconf assignment' (simpleSymValToTerm v)
            (specs.map (·.f)) = Except.ok val' :=
          evalTerm_simpleSymValToTerm gconf assignment' v val' (specs.map (·.f)) hm'
        have hiteEval : evalTerm gconf assignment'
            (FFTerm.ite (FFFormula.eq (simpleSymValToTerm v) (FFTerm.val 0))
              (FFTerm.val 1) (FFTerm.val 0)) (specs.map (·.f))
            = Except.ok (evalBneg val') := by
          simp only [evalBneg]
          by_cases h : val' = 0 <;> simp [evalTerm, evalFormula, hevalTerm', h]
        obtain ⟨heval_feq, _heval_fbool⟩ :=
          evalFormula_and_elim gconf assignment'
            (FFFormula.eq (FFTerm.var sconf.nextVarId)
              (FFTerm.ite (FFFormula.eq (simpleSymValToTerm v) (FFTerm.val 0))
                (FFTerm.val 1) (FFTerm.val 0)))
            fbool (specs.map (·.f)) heval_f
        simp only [evalFormula, evalTerm, hiteEval, Except.ok.injEq] at heval_feq
        have hffeq : assignment'.ff sconf.nextVarId = evalBneg val' :=
          (beq_iff_eq ..).mp heval_feq
        refine ⟨evalBneg val', ?_, hmatch', ?_⟩
        · simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval', evalBneg]
        · simp only [simpleValMatches, hffeq]

/-- `seExprEq` mints one fresh var `outFFVar`, tied down by a single equation to a term-level
    `ite` on `v1Term = v2Term` -- structurally the same "mint one fresh var, tie it down" shape as
    `seExprAdd_correct`/`seExprSub_correct`/`seExprMul_correct`, just with the tie-down term one
    layer deeper (an `ite` over an `.eq` condition, instead of a bare arithmetic op). Both
    directions turn on the *same* case split: whether the two resolved values are equal, which
    picks which branch of the `ite` evaluates and lines up exactly with `evalEq`'s own `if v1 = v2
    then 1 else 0`. -/
theorem seExprEq_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD) (e1 e2 : SimpleExpr c) :
    TranslatesExprCorrectly gconf sconf specs ctx
      (fun env => Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env
        (Expr.bop BinOp.eq e1 e2))
      (fun symEnv => seExprEq md gconf sconf symEnv specs e1 e2) := by
  intro symEnv hbelow _hvalid espec hspec_eq
  simp only [seExprEq] at hspec_eq
  cases hres1 : resolveSimpleExpr symEnv e1 with
  | error msg => rw [hres1] at hspec_eq; simp at hspec_eq
  | ok v1 =>
      rw [hres1] at hspec_eq
      cases hres2 : resolveSimpleExpr symEnv e2 with
      | error msg => rw [hres2] at hspec_eq; simp at hspec_eq
      | ok v2 =>
          rw [hres2] at hspec_eq
          cases hbool : bool_ffterm gconf sconf (FFTerm.var sconf.nextVarId) with
          | error msg => rw [hbool] at hspec_eq; simp at hspec_eq
          | ok fbool =>
          rw [hbool] at hspec_eq
          injection hspec_eq with hspec_eq
          subst hspec_eq
          have hsub1 := Corellzk2smt.SymExec.Correctness.Lemmas.resolveSimpleExpr_vars_subset
            symEnv e1 v1 hres1
          have hsub2 := Corellzk2smt.SymExec.Correctness.Lemmas.resolveSimpleExpr_vars_subset
            symEnv e2 v2 hres2
          have hmemF_eq : Var.ffv sconf.nextVarId ∈
              ffVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
                (FFTerm.ite (FFFormula.eq (simpleSymValToTerm v1) (simpleSymValToTerm v2))
                  (FFTerm.val 1) (FFTerm.val 0))) := by
            simp only [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_union_iff]
            exact Or.inl (Std.TreeSet.mem_insert_self ..)
          have hmemF : Var.ffv sconf.nextVarId ∈
              ffVarsOfFormula (FFFormula.and
                (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (FFTerm.ite (FFFormula.eq (simpleSymValToTerm v1) (simpleSymValToTerm v2))
                    (FFTerm.val 1) (FFTerm.val 0)))
                fbool) := by
            simp only [ffVarsOfFormula]
            exact Std.TreeSet.mem_union_of_left hmemF_eq
          refine ⟨Nat.le_succ _, ?_, ?_, ?_, varSetBelow_mono (Nat.le_succ _) hbelow,
            fun v' hv' => Or.inl hv', ValidBinRep_trivial gconf _ _, ?_, ?_⟩
          · intro v' hv'
            simp only [simpleValVars, simpleValOwnVars, Option.map_none, Option.getD_none,
              Std.TreeSet.mem_union_iff] at hv'
            rcases hv' with h | h
            · rcases Std.TreeSet.mem_insert.mp h with heq | hmem
              · rw [← Var_compare_eq_iff_eq.mp heq]
                exact Or.inr (Std.TreeSet.mem_union_of_left hmemF)
              · exact absurd hmem Std.TreeSet.not_mem_emptyc
            · exact absurd h Std.TreeSet.not_mem_emptyc
          · intro v' hv'
            simp only [exprSpecVars] at hv'
            rcases Std.TreeSet.mem_union_iff.mp hv' with hff_top | hb_top
            · simp only [ffVarsOfFormula] at hff_top
              rcases Std.TreeSet.mem_union_iff.mp hff_top with hff | hfbool
              · simp only [ffVarsOfFormula, ffVarsOfTerm, ffVarsOfTerm_simpleSymValToTerm,
                  Std.TreeSet.mem_union_iff] at hff
                rcases hff with h1 | (((h2 | h3) | h4) | h5)
                · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
                  · rw [← Var_compare_eq_iff_eq.mp heq]
                    exact Or.inr (le_refl _)
                  · exact absurd hmem Std.TreeSet.not_mem_emptyc
                · exact Or.inl (hsub1 v' (simpleValOwnVars_subset_simpleValVars v1 v' h2))
                · exact Or.inl (hsub2 v' (simpleValOwnVars_subset_simpleValVars v2 v' h3))
                · exact absurd h4 Std.TreeSet.not_mem_emptyc
                · exact absurd h5 Std.TreeSet.not_mem_emptyc
              · rw [mem_ffVarsOfFormula_bool_ffterm_var gconf sconf sconf.nextVarId fbool
                  hbool] at hfbool
                rw [← hfbool]
                exact Or.inr (le_refl _)
            · simp only [bVarsOfFormula] at hb_top
              rcases Std.TreeSet.mem_union_iff.mp hb_top with hb | hbbool
              · simp only [bVarsOfFormula, bVarsOfTerm, bVarsOfTerm_simpleSymValToTerm,
                  Std.TreeSet.mem_union_iff] at hb
                rcases hb with h | (((h | h) | h) | h) <;> exact absurd h Std.TreeSet.not_mem_emptyc
              · exact absurd hbbool
                  (not_mem_bVarsOfFormula_bool_ffterm_var gconf sconf sconf.nextVarId fbool hbool v')
          · intro v' hv'
            simp only [exprSpecVars] at hv'
            rcases Std.TreeSet.mem_union_iff.mp hv' with hff_top | hb_top
            · simp only [ffVarsOfFormula] at hff_top
              rcases Std.TreeSet.mem_union_iff.mp hff_top with hff | hfbool
              · simp only [ffVarsOfFormula, ffVarsOfTerm, ffVarsOfTerm_simpleSymValToTerm,
                  Std.TreeSet.mem_union_iff] at hff
                rcases hff with h1 | (((h2 | h3) | h4) | h5)
                · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
                  · rw [← Var_compare_eq_iff_eq.mp heq]
                    simp only [varIndex]
                    omega
                  · exact absurd hmem Std.TreeSet.not_mem_emptyc
                · exact lt_of_lt_of_le
                    (hbelow v' (hsub1 v' (simpleValOwnVars_subset_simpleValVars v1 v' h2)))
                    (Nat.le_succ _)
                · exact lt_of_lt_of_le
                    (hbelow v' (hsub2 v' (simpleValOwnVars_subset_simpleValVars v2 v' h3)))
                    (Nat.le_succ _)
                · exact absurd h4 Std.TreeSet.not_mem_emptyc
                · exact absurd h5 Std.TreeSet.not_mem_emptyc
              · rw [mem_ffVarsOfFormula_bool_ffterm_var gconf sconf sconf.nextVarId fbool
                  hbool] at hfbool
                rw [← hfbool]
                simp only [varIndex]
                omega
            · simp only [bVarsOfFormula] at hb_top
              rcases Std.TreeSet.mem_union_iff.mp hb_top with hb | hbbool
              · simp only [bVarsOfFormula, bVarsOfTerm, bVarsOfTerm_simpleSymValToTerm,
                  Std.TreeSet.mem_union_iff] at hb
                rcases hb with h | (((h | h) | h) | h) <;> exact absurd h Std.TreeSet.not_mem_emptyc
              · exact absurd hbbool
                  (not_mem_bVarsOfFormula_bool_ffterm_var gconf sconf sconf.nextVarId fbool hbool v')
          · intro env assignment hmatch val hval
            obtain ⟨val1', hval1', hm1⟩ :=
              resolveSimpleExpr_correct symEnv e1 env assignment v1 hmatch hres1
            obtain ⟨val2', hval2', hm2⟩ :=
              resolveSimpleExpr_correct symEnv e2 env assignment v2 hmatch hres2
            simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval1', hval2',
              evalEq] at hval
            injection hval with hval
            subst hval
            set assignment' : Assignment c :=
              { assignment with
                ff := fun n => if n = sconf.nextVarId then
                    (if val1' = val2' then (1 : FF c) else 0) else assignment.ff n }
              with hassignment'_def
            have hagreeff : agreesOnFF (symEnvVars symEnv) assignment assignment' := by
              intro n hn
              have hne : n ≠ sconf.nextVarId := Nat.ne_of_lt (hbelow (Var.ffv n) hn)
              simp only [hassignment'_def, if_neg hne]
            have hagreebool : agreesOnBool (symEnvVars symEnv) assignment assignment' :=
              fun n _ => rfl
            have hframeff : ∀ n, Var.ffv n ∉
                (ffVarsOfFormula (FFFormula.and
                  (FFFormula.eq (FFTerm.var sconf.nextVarId)
                    (FFTerm.ite (FFFormula.eq (simpleSymValToTerm v1) (simpleSymValToTerm v2))
                      (FFTerm.val 1) (FFTerm.val 0)))
                  fbool) ∪
                 bVarsOfFormula (FFFormula.and
                  (FFFormula.eq (FFTerm.var sconf.nextVarId)
                    (FFTerm.ite (FFFormula.eq (simpleSymValToTerm v1) (simpleSymValToTerm v2))
                      (FFTerm.val 1) (FFTerm.val 0)))
                  fbool)) →
                assignment'.ff n = assignment.ff n := by
              intro n hn
              have hne : n ≠ sconf.nextVarId := by
                intro heqn
                apply hn
                rw [heqn]
                exact Std.TreeSet.mem_union_of_left hmemF
              simp only [hassignment'_def, if_neg hne]
            have hframebool : ∀ n, Var.boolv n ∉
                (ffVarsOfFormula (FFFormula.and
                  (FFFormula.eq (FFTerm.var sconf.nextVarId)
                    (FFTerm.ite (FFFormula.eq (simpleSymValToTerm v1) (simpleSymValToTerm v2))
                      (FFTerm.val 1) (FFTerm.val 0)))
                  fbool) ∪
                 bVarsOfFormula (FFFormula.and
                  (FFFormula.eq (FFTerm.var sconf.nextVarId)
                    (FFTerm.ite (FFFormula.eq (simpleSymValToTerm v1) (simpleSymValToTerm v2))
                      (FFTerm.val 1) (FFTerm.val 0)))
                  fbool)) →
                assignment'.bool n = assignment.bool n := fun n _ => rfl
            have hsimpleMatch1' : simpleValMatches assignment' v1 val1' :=
              simpleValMatches_agreesOnFF_preserves assignment assignment' v1 val1'
                (symEnvVars symEnv) hsub1 hagreeff hm1
            have hsimpleMatch2' : simpleValMatches assignment' v2 val2' :=
              simpleValMatches_agreesOnFF_preserves assignment assignment' v2 val2'
                (symEnvVars symEnv) hsub2 hagreeff hm2
            have hevalTerm1' : evalTerm gconf assignment' (simpleSymValToTerm v1)
                (specs.map (·.f)) = Except.ok val1' :=
              evalTerm_simpleSymValToTerm gconf assignment' v1 val1' (specs.map (·.f))
                hsimpleMatch1'
            have hevalTerm2' : evalTerm gconf assignment' (simpleSymValToTerm v2)
                (specs.map (·.f)) = Except.ok val2' :=
              evalTerm_simpleSymValToTerm gconf assignment' v2 val2' (specs.map (·.f))
                hsimpleMatch2'
            have hffeval : assignment'.ff sconf.nextVarId
                = (if val1' = val2' then (1 : FF c) else 0) := by
              simp [hassignment'_def]
            have hiteEval : evalTerm gconf assignment'
                (FFTerm.ite (FFFormula.eq (simpleSymValToTerm v1) (simpleSymValToTerm v2))
                  (FFTerm.val 1) (FFTerm.val 0)) (specs.map (·.f))
                = Except.ok (if val1' = val2' then (1 : FF c) else 0) := by
              by_cases heqv : val1' = val2' <;>
                simp [evalTerm, evalFormula, hevalTerm1', hevalTerm2', heqv]
            have hf_eq_true : evalFormula gconf assignment'
                (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (FFTerm.ite (FFFormula.eq (simpleSymValToTerm v1) (simpleSymValToTerm v2))
                    (FFTerm.val 1) (FFTerm.val 0))) (specs.map (·.f)) = Except.ok true := by
              simp [evalFormula, evalTerm, hiteEval, hffeval]
            have hf_bool_true : evalFormula gconf assignment'
                fbool (specs.map (·.f))
                = Except.ok true := by
              rw [evalFormula_bool_ffterm_var_iff gconf sconf assignment' (specs.map (·.f))
                sconf.nextVarId fbool hbool, hffeval]
              by_cases heqv : val1' = val2' <;> simp [heqv]
            refine ⟨assignment', hagreeff, hagreebool, hframeff, hframebool, ?_,
              EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagreeff hmatch,
              ?_⟩
            · exact evalFormula_and_intro gconf assignment'
                (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (FFTerm.ite (FFFormula.eq (simpleSymValToTerm v1) (simpleSymValToTerm v2))
                    (FFTerm.val 1) (FFTerm.val 0)))
                fbool (specs.map (·.f))
                hf_eq_true hf_bool_true
            · simp only [simpleValMatches, hffeval]
          · intro env assignment hmatch assignment' hagree heval_f
            have hmatch' : EnvMatches assignment' symEnv env :=
              EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagree hmatch
            obtain ⟨val1', hval1', hm1'⟩ :=
              resolveSimpleExpr_correct symEnv e1 env assignment' v1 hmatch' hres1
            obtain ⟨val2', hval2', hm2'⟩ :=
              resolveSimpleExpr_correct symEnv e2 env assignment' v2 hmatch' hres2
            have hevalTerm1' : evalTerm gconf assignment' (simpleSymValToTerm v1)
                (specs.map (·.f)) = Except.ok val1' :=
              evalTerm_simpleSymValToTerm gconf assignment' v1 val1' (specs.map (·.f)) hm1'
            have hevalTerm2' : evalTerm gconf assignment' (simpleSymValToTerm v2)
                (specs.map (·.f)) = Except.ok val2' :=
              evalTerm_simpleSymValToTerm gconf assignment' v2 val2' (specs.map (·.f)) hm2'
            have hiteEval : evalTerm gconf assignment'
                (FFTerm.ite (FFFormula.eq (simpleSymValToTerm v1) (simpleSymValToTerm v2))
                  (FFTerm.val 1) (FFTerm.val 0)) (specs.map (·.f))
                = Except.ok (if val1' = val2' then (1 : FF c) else 0) := by
              by_cases heqv : val1' = val2' <;>
                simp [evalTerm, evalFormula, hevalTerm1', hevalTerm2', heqv]
            obtain ⟨heval_feq, _heval_fbool⟩ :=
              evalFormula_and_elim gconf assignment'
                (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (FFTerm.ite (FFFormula.eq (simpleSymValToTerm v1) (simpleSymValToTerm v2))
                    (FFTerm.val 1) (FFTerm.val 0)))
                fbool (specs.map (·.f)) heval_f
            simp only [evalFormula, evalTerm, hiteEval, Except.ok.injEq] at heval_feq
            have hffeq : assignment'.ff sconf.nextVarId
                = (if val1' = val2' then (1 : FF c) else 0) := (beq_iff_eq ..).mp heval_feq
            refine ⟨if val1' = val2' then (1 : FF c) else 0, ?_, hmatch', ?_⟩
            · simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval1', hval2',
                evalEq]
            · simp only [simpleValMatches, hffeq]

/-- Mirror of `seExprEq_correct`, for `seExprNeq` -- same proof shape, `evalNeq` in place of
    `evalEq`, the two `ite` branches swapped (`0`/`1` instead of `1`/`0`), and the same
    `bool_ffterm` boolean-tag conjunct on the fresh var. -/
theorem seExprNeq_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD) (e1 e2 : SimpleExpr c) :
    TranslatesExprCorrectly gconf sconf specs ctx
      (fun env => Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env
        (Expr.bop BinOp.neq e1 e2))
      (fun symEnv => seExprNeq md gconf sconf symEnv specs e1 e2) := by
  intro symEnv hbelow _hvalid espec hspec_eq
  simp only [seExprNeq] at hspec_eq
  cases hres1 : resolveSimpleExpr symEnv e1 with
  | error msg => rw [hres1] at hspec_eq; simp at hspec_eq
  | ok v1 =>
      rw [hres1] at hspec_eq
      cases hres2 : resolveSimpleExpr symEnv e2 with
      | error msg => rw [hres2] at hspec_eq; simp at hspec_eq
      | ok v2 =>
          rw [hres2] at hspec_eq
          cases hbool : bool_ffterm gconf sconf (FFTerm.var sconf.nextVarId) with
          | error msg => rw [hbool] at hspec_eq; simp at hspec_eq
          | ok fbool =>
          rw [hbool] at hspec_eq
          injection hspec_eq with hspec_eq
          subst hspec_eq
          have hsub1 := Corellzk2smt.SymExec.Correctness.Lemmas.resolveSimpleExpr_vars_subset
            symEnv e1 v1 hres1
          have hsub2 := Corellzk2smt.SymExec.Correctness.Lemmas.resolveSimpleExpr_vars_subset
            symEnv e2 v2 hres2
          have hmemF_eq : Var.ffv sconf.nextVarId ∈
              ffVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
                (FFTerm.ite (FFFormula.eq (simpleSymValToTerm v1) (simpleSymValToTerm v2))
                  (FFTerm.val 0) (FFTerm.val 1))) := by
            simp only [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_union_iff]
            exact Or.inl (Std.TreeSet.mem_insert_self ..)
          have hmemF : Var.ffv sconf.nextVarId ∈
              ffVarsOfFormula (FFFormula.and
                (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (FFTerm.ite (FFFormula.eq (simpleSymValToTerm v1) (simpleSymValToTerm v2))
                    (FFTerm.val 0) (FFTerm.val 1)))
                fbool) := by
            simp only [ffVarsOfFormula]
            exact Std.TreeSet.mem_union_of_left hmemF_eq
          refine ⟨Nat.le_succ _, ?_, ?_, ?_, varSetBelow_mono (Nat.le_succ _) hbelow,
            fun v' hv' => Or.inl hv', ValidBinRep_trivial gconf _ _, ?_, ?_⟩
          · intro v' hv'
            simp only [simpleValVars, simpleValOwnVars, Option.map_none, Option.getD_none,
              Std.TreeSet.mem_union_iff] at hv'
            rcases hv' with h | h
            · rcases Std.TreeSet.mem_insert.mp h with heq | hmem
              · rw [← Var_compare_eq_iff_eq.mp heq]
                exact Or.inr (Std.TreeSet.mem_union_of_left hmemF)
              · exact absurd hmem Std.TreeSet.not_mem_emptyc
            · exact absurd h Std.TreeSet.not_mem_emptyc
          · intro v' hv'
            simp only [exprSpecVars] at hv'
            rcases Std.TreeSet.mem_union_iff.mp hv' with hff_top | hb_top
            · simp only [ffVarsOfFormula] at hff_top
              rcases Std.TreeSet.mem_union_iff.mp hff_top with hff | hfbool
              · simp only [ffVarsOfFormula, ffVarsOfTerm, ffVarsOfTerm_simpleSymValToTerm,
                  Std.TreeSet.mem_union_iff] at hff
                rcases hff with h1 | (((h2 | h3) | h4) | h5)
                · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
                  · rw [← Var_compare_eq_iff_eq.mp heq]
                    exact Or.inr (le_refl _)
                  · exact absurd hmem Std.TreeSet.not_mem_emptyc
                · exact Or.inl (hsub1 v' (simpleValOwnVars_subset_simpleValVars v1 v' h2))
                · exact Or.inl (hsub2 v' (simpleValOwnVars_subset_simpleValVars v2 v' h3))
                · exact absurd h4 Std.TreeSet.not_mem_emptyc
                · exact absurd h5 Std.TreeSet.not_mem_emptyc
              · rw [mem_ffVarsOfFormula_bool_ffterm_var gconf sconf sconf.nextVarId fbool
                  hbool] at hfbool
                rw [← hfbool]
                exact Or.inr (le_refl _)
            · simp only [bVarsOfFormula] at hb_top
              rcases Std.TreeSet.mem_union_iff.mp hb_top with hb | hbbool
              · simp only [bVarsOfFormula, bVarsOfTerm, bVarsOfTerm_simpleSymValToTerm,
                  Std.TreeSet.mem_union_iff] at hb
                rcases hb with h | (((h | h) | h) | h) <;> exact absurd h Std.TreeSet.not_mem_emptyc
              · exact absurd hbbool
                  (not_mem_bVarsOfFormula_bool_ffterm_var gconf sconf sconf.nextVarId fbool hbool
                    v')
          · intro v' hv'
            simp only [exprSpecVars] at hv'
            rcases Std.TreeSet.mem_union_iff.mp hv' with hff_top | hb_top
            · simp only [ffVarsOfFormula] at hff_top
              rcases Std.TreeSet.mem_union_iff.mp hff_top with hff | hfbool
              · simp only [ffVarsOfFormula, ffVarsOfTerm, ffVarsOfTerm_simpleSymValToTerm,
                  Std.TreeSet.mem_union_iff] at hff
                rcases hff with h1 | (((h2 | h3) | h4) | h5)
                · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
                  · rw [← Var_compare_eq_iff_eq.mp heq]
                    simp only [varIndex]
                    omega
                  · exact absurd hmem Std.TreeSet.not_mem_emptyc
                · exact lt_of_lt_of_le
                    (hbelow v' (hsub1 v' (simpleValOwnVars_subset_simpleValVars v1 v' h2)))
                    (Nat.le_succ _)
                · exact lt_of_lt_of_le
                    (hbelow v' (hsub2 v' (simpleValOwnVars_subset_simpleValVars v2 v' h3)))
                    (Nat.le_succ _)
                · exact absurd h4 Std.TreeSet.not_mem_emptyc
                · exact absurd h5 Std.TreeSet.not_mem_emptyc
              · rw [mem_ffVarsOfFormula_bool_ffterm_var gconf sconf sconf.nextVarId fbool
                  hbool] at hfbool
                rw [← hfbool]
                simp only [varIndex]
                omega
            · simp only [bVarsOfFormula] at hb_top
              rcases Std.TreeSet.mem_union_iff.mp hb_top with hb | hbbool
              · simp only [bVarsOfFormula, bVarsOfTerm, bVarsOfTerm_simpleSymValToTerm,
                  Std.TreeSet.mem_union_iff] at hb
                rcases hb with h | (((h | h) | h) | h) <;> exact absurd h Std.TreeSet.not_mem_emptyc
              · exact absurd hbbool
                  (not_mem_bVarsOfFormula_bool_ffterm_var gconf sconf sconf.nextVarId fbool hbool
                    v')
          · intro env assignment hmatch val hval
            obtain ⟨val1', hval1', hm1⟩ :=
              resolveSimpleExpr_correct symEnv e1 env assignment v1 hmatch hres1
            obtain ⟨val2', hval2', hm2⟩ :=
              resolveSimpleExpr_correct symEnv e2 env assignment v2 hmatch hres2
            simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval1', hval2',
              evalNeq] at hval
            injection hval with hval
            subst hval
            set assignment' : Assignment c :=
              { assignment with
                ff := fun n => if n = sconf.nextVarId then
                    (if val1' = val2' then (0 : FF c) else 1) else assignment.ff n }
              with hassignment'_def
            have hagreeff : agreesOnFF (symEnvVars symEnv) assignment assignment' := by
              intro n hn
              have hne : n ≠ sconf.nextVarId := Nat.ne_of_lt (hbelow (Var.ffv n) hn)
              simp only [hassignment'_def, if_neg hne]
            have hagreebool : agreesOnBool (symEnvVars symEnv) assignment assignment' :=
              fun n _ => rfl
            have hframeff : ∀ n, Var.ffv n ∉
                (ffVarsOfFormula (FFFormula.and
                  (FFFormula.eq (FFTerm.var sconf.nextVarId)
                    (FFTerm.ite (FFFormula.eq (simpleSymValToTerm v1) (simpleSymValToTerm v2))
                      (FFTerm.val 0) (FFTerm.val 1)))
                  fbool) ∪
                 bVarsOfFormula (FFFormula.and
                  (FFFormula.eq (FFTerm.var sconf.nextVarId)
                    (FFTerm.ite (FFFormula.eq (simpleSymValToTerm v1) (simpleSymValToTerm v2))
                      (FFTerm.val 0) (FFTerm.val 1)))
                  fbool)) →
                assignment'.ff n = assignment.ff n := by
              intro n hn
              have hne : n ≠ sconf.nextVarId := by
                intro heqn
                apply hn
                rw [heqn]
                exact Std.TreeSet.mem_union_of_left hmemF
              simp only [hassignment'_def, if_neg hne]
            have hframebool : ∀ n, Var.boolv n ∉
                (ffVarsOfFormula (FFFormula.and
                  (FFFormula.eq (FFTerm.var sconf.nextVarId)
                    (FFTerm.ite (FFFormula.eq (simpleSymValToTerm v1) (simpleSymValToTerm v2))
                      (FFTerm.val 0) (FFTerm.val 1)))
                  fbool) ∪
                 bVarsOfFormula (FFFormula.and
                  (FFFormula.eq (FFTerm.var sconf.nextVarId)
                    (FFTerm.ite (FFFormula.eq (simpleSymValToTerm v1) (simpleSymValToTerm v2))
                      (FFTerm.val 0) (FFTerm.val 1)))
                  fbool)) →
                assignment'.bool n = assignment.bool n := fun n _ => rfl
            have hsimpleMatch1' : simpleValMatches assignment' v1 val1' :=
              simpleValMatches_agreesOnFF_preserves assignment assignment' v1 val1'
                (symEnvVars symEnv) hsub1 hagreeff hm1
            have hsimpleMatch2' : simpleValMatches assignment' v2 val2' :=
              simpleValMatches_agreesOnFF_preserves assignment assignment' v2 val2'
                (symEnvVars symEnv) hsub2 hagreeff hm2
            have hevalTerm1' : evalTerm gconf assignment' (simpleSymValToTerm v1)
                (specs.map (·.f)) = Except.ok val1' :=
              evalTerm_simpleSymValToTerm gconf assignment' v1 val1' (specs.map (·.f))
                hsimpleMatch1'
            have hevalTerm2' : evalTerm gconf assignment' (simpleSymValToTerm v2)
                (specs.map (·.f)) = Except.ok val2' :=
              evalTerm_simpleSymValToTerm gconf assignment' v2 val2' (specs.map (·.f))
                hsimpleMatch2'
            have hffeval : assignment'.ff sconf.nextVarId
                = (if val1' = val2' then (0 : FF c) else 1) := by
              simp [hassignment'_def]
            have hiteEval : evalTerm gconf assignment'
                (FFTerm.ite (FFFormula.eq (simpleSymValToTerm v1) (simpleSymValToTerm v2))
                  (FFTerm.val 0) (FFTerm.val 1)) (specs.map (·.f))
                = Except.ok (if val1' = val2' then (0 : FF c) else 1) := by
              by_cases heqv : val1' = val2' <;>
                simp [evalTerm, evalFormula, hevalTerm1', hevalTerm2', heqv]
            have hf_eq_true : evalFormula gconf assignment'
                (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (FFTerm.ite (FFFormula.eq (simpleSymValToTerm v1) (simpleSymValToTerm v2))
                    (FFTerm.val 0) (FFTerm.val 1))) (specs.map (·.f)) = Except.ok true := by
              simp [evalFormula, evalTerm, hiteEval, hffeval]
            have hf_bool_true : evalFormula gconf assignment'
                fbool (specs.map (·.f))
                = Except.ok true := by
              rw [evalFormula_bool_ffterm_var_iff gconf sconf assignment' (specs.map (·.f))
                sconf.nextVarId fbool hbool, hffeval]
              by_cases heqv : val1' = val2' <;> simp [heqv]
            refine ⟨assignment', hagreeff, hagreebool, hframeff, hframebool, ?_,
              EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagreeff hmatch,
              ?_⟩
            · exact evalFormula_and_intro gconf assignment'
                (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (FFTerm.ite (FFFormula.eq (simpleSymValToTerm v1) (simpleSymValToTerm v2))
                    (FFTerm.val 0) (FFTerm.val 1)))
                fbool (specs.map (·.f))
                hf_eq_true hf_bool_true
            · simp only [simpleValMatches, hffeval]
              by_cases heqv : val1' = val2' <;> simp [heqv]
          · intro env assignment hmatch assignment' hagree heval_f
            have hmatch' : EnvMatches assignment' symEnv env :=
              EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagree hmatch
            obtain ⟨val1', hval1', hm1'⟩ :=
              resolveSimpleExpr_correct symEnv e1 env assignment' v1 hmatch' hres1
            obtain ⟨val2', hval2', hm2'⟩ :=
              resolveSimpleExpr_correct symEnv e2 env assignment' v2 hmatch' hres2
            have hevalTerm1' : evalTerm gconf assignment' (simpleSymValToTerm v1)
                (specs.map (·.f)) = Except.ok val1' :=
              evalTerm_simpleSymValToTerm gconf assignment' v1 val1' (specs.map (·.f)) hm1'
            have hevalTerm2' : evalTerm gconf assignment' (simpleSymValToTerm v2)
                (specs.map (·.f)) = Except.ok val2' :=
              evalTerm_simpleSymValToTerm gconf assignment' v2 val2' (specs.map (·.f)) hm2'
            have hiteEval : evalTerm gconf assignment'
                (FFTerm.ite (FFFormula.eq (simpleSymValToTerm v1) (simpleSymValToTerm v2))
                  (FFTerm.val 0) (FFTerm.val 1)) (specs.map (·.f))
                = Except.ok (if val1' = val2' then (0 : FF c) else 1) := by
              by_cases heqv : val1' = val2' <;>
                simp [evalTerm, evalFormula, hevalTerm1', hevalTerm2', heqv]
            obtain ⟨heval_feq, _heval_fbool⟩ :=
              evalFormula_and_elim gconf assignment'
                (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (FFTerm.ite (FFFormula.eq (simpleSymValToTerm v1) (simpleSymValToTerm v2))
                    (FFTerm.val 0) (FFTerm.val 1)))
                fbool (specs.map (·.f)) heval_f
            simp only [evalFormula, evalTerm, hiteEval, Except.ok.injEq] at heval_feq
            have hffeq : assignment'.ff sconf.nextVarId
                = (if val1' = val2' then (0 : FF c) else 1) := (beq_iff_eq ..).mp heval_feq
            refine ⟨if val1' = val2' then (0 : FF c) else 1, ?_, hmatch', ?_⟩
            · simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval1', hval2',
                evalNeq]
              by_cases heqv : val1' = val2' <;> simp [heqv]
            · simp only [simpleValMatches, hffeq]

theorem seExprLtSigned_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD) (e1 e2 : SimpleExpr c) :
    TranslatesExprCorrectly gconf sconf specs ctx
      (fun env => Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env
        (Expr.bop BinOp.lt e1 e2))
      (fun symEnv => seExprLtSigned md gconf sconf symEnv specs e1 e2) := by
  sorry

theorem seExprLeSigned_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD) (e1 e2 : SimpleExpr c) :
    TranslatesExprCorrectly gconf sconf specs ctx
      (fun env => Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env
        (Expr.bop BinOp.le e1 e2))
      (fun symEnv => seExprLeSigned md gconf sconf symEnv specs e1 e2) := by
  sorry

theorem seExprGtSigned_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD) (e1 e2 : SimpleExpr c) :
    TranslatesExprCorrectly gconf sconf specs ctx
      (fun env => Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env
        (Expr.bop BinOp.gt e1 e2))
      (fun symEnv => seExprGtSigned md gconf sconf symEnv specs e1 e2) := by
  sorry

theorem seExprGeSigned_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD) (e1 e2 : SimpleExpr c) :
    TranslatesExprCorrectly gconf sconf specs ctx
      (fun env => Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env
        (Expr.bop BinOp.ge e1 e2))
      (fun symEnv => seExprGeSigned md gconf sconf symEnv specs e1 e2) := by
  sorry

end Corellzk2smt.SymExec.Correctness.BoolExprCorrectness
