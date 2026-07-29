import Corellzk2smt.SymExec.Correctness.Lemmas
import Corellzk2smt.SymExec.Correctness.FuncCallCorrectness
import Corellzk2smt.SymExec.Correctness.BinaryExpansionCorrectness
import Corellzk2smt.SymExec.Correctness.ArithExprCorrectness
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
open Corellzk2smt.SymExec.Correctness.ArithExprCorrectness
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

/-- `s1 < s2` when `s2` constant-folds: ties `outFFVar` to `evalLt`'s own `if`-form by expressing
    "`lhs < rhs`" as a single-sided `FFFormula.range` bound (`c.midpoint` as a permanent lower-bound
    no-op, `rhs - 1` as the upper bound) -- except when `rhs` is itself the field's signed minimum,
    where the condition is directly `FFFormula.false` (nothing is less than the minimum). Plus the
    same `bool_ffterm` boolean-tag conjunct as `seExprEq`. -/
theorem seExprLtSignedConstantUpperBound_correct {c : ZKConfig} (gconf : GlobalConfig c)
    (specs : List (FuncSpec c)) (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD)
    (e1 e2 : SimpleExpr c) :
    TranslatesExprCorrectly gconf sconf specs ctx
      (fun env => Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env
        (Expr.bop BinOp.lt e1 e2))
      (fun symEnv => seExprLtSignedConstantUpperBound md gconf sconf symEnv specs e1 e2) := by
  intro symEnv hbelow _hvalid espec hspec_eq
  simp only [seExprLtSignedConstantUpperBound] at hspec_eq
  cases hres2 : tryEvalSimpleExprToFFValue symEnv e2 with
  | error msg => rw [hres2] at hspec_eq; simp at hspec_eq
  | ok rhs =>
      rw [hres2] at hspec_eq
      cases hres1 : resolveSimpleExpr symEnv e1 with
      | error msg => rw [hres1] at hspec_eq; simp at hspec_eq
      | ok lhs =>
          rw [hres1] at hspec_eq
          cases hbool : bool_ffterm gconf sconf (FFTerm.var sconf.nextVarId) with
          | error msg => rw [hbool] at hspec_eq; simp at hspec_eq
          | ok fbool =>
          rw [hbool] at hspec_eq
          injection hspec_eq with hspec_eq
          subst hspec_eq
          set lhsTerm := simpleSymValToTerm lhs with hlhsTerm_def
          set cond : FFFormula c :=
            if rhs = (c.midpoint : FF c) then FFFormula.false
            else FFFormula.range lhsTerm (c.midpoint : FF c) (rhs - 1) with hcond_def
          have hsub1 := Corellzk2smt.SymExec.Correctness.Lemmas.resolveSimpleExpr_vars_subset
            symEnv e1 lhs hres1
          have hcond_vars : ∀ v', v' ∈ ffVarsOfFormula cond → v' ∈ simpleValOwnVars lhs := by
            intro v' hv'
            by_cases hrhseq : rhs = (c.midpoint : FF c)
            · simp only [hcond_def, if_pos hrhseq, ffVarsOfFormula] at hv'
              exact absurd hv' Std.TreeSet.not_mem_emptyc
            · simp only [hcond_def, if_neg hrhseq, ffVarsOfFormula, hlhsTerm_def,
                ffVarsOfTerm_simpleSymValToTerm] at hv'
              exact hv'
          have hcond_bvars : ∀ v', v' ∉ bVarsOfFormula cond := by
            intro v' hv'
            by_cases hrhseq : rhs = (c.midpoint : FF c)
            · simp only [hcond_def, if_pos hrhseq, bVarsOfFormula] at hv'
              exact absurd hv' Std.TreeSet.not_mem_emptyc
            · simp only [hcond_def, if_neg hrhseq, bVarsOfFormula, hlhsTerm_def,
                bVarsOfTerm_simpleSymValToTerm] at hv'
              exact absurd hv' Std.TreeSet.not_mem_emptyc
          have hmemF_eq : Var.ffv sconf.nextVarId ∈
              ffVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
                (FFTerm.ite cond (FFTerm.val 1) (FFTerm.val 0))) := by
            simp only [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_union_iff]
            exact Or.inl (Std.TreeSet.mem_insert_self ..)
          have hmemF : Var.ffv sconf.nextVarId ∈
              ffVarsOfFormula (FFFormula.and
                (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (FFTerm.ite cond (FFTerm.val 1) (FFTerm.val 0)))
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
              · simp only [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_union_iff] at hff
                rcases hff with h1 | ((hcondv | h4) | h5)
                · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
                  · rw [← Var_compare_eq_iff_eq.mp heq]
                    exact Or.inr (le_refl _)
                  · exact absurd hmem Std.TreeSet.not_mem_emptyc
                · exact Or.inl (hsub1 v'
                    (simpleValOwnVars_subset_simpleValVars lhs v' (hcond_vars v' hcondv)))
                · exact absurd h4 Std.TreeSet.not_mem_emptyc
                · exact absurd h5 Std.TreeSet.not_mem_emptyc
              · rw [mem_ffVarsOfFormula_bool_ffterm_var gconf sconf sconf.nextVarId fbool
                  hbool] at hfbool
                rw [← hfbool]
                exact Or.inr (le_refl _)
            · simp only [bVarsOfFormula] at hb_top
              rcases Std.TreeSet.mem_union_iff.mp hb_top with hb | hbbool
              · simp only [bVarsOfFormula, bVarsOfTerm, Std.TreeSet.mem_union_iff] at hb
                rcases hb with h | ((hcondv | h) | h)
                · exact absurd h Std.TreeSet.not_mem_emptyc
                · exact absurd hcondv (hcond_bvars v')
                · exact absurd h Std.TreeSet.not_mem_emptyc
                · exact absurd h Std.TreeSet.not_mem_emptyc
              · exact absurd hbbool
                  (not_mem_bVarsOfFormula_bool_ffterm_var gconf sconf sconf.nextVarId fbool hbool
                    v')
          · intro v' hv'
            simp only [exprSpecVars] at hv'
            rcases Std.TreeSet.mem_union_iff.mp hv' with hff_top | hb_top
            · simp only [ffVarsOfFormula] at hff_top
              rcases Std.TreeSet.mem_union_iff.mp hff_top with hff | hfbool
              · simp only [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_union_iff] at hff
                rcases hff with h1 | ((hcondv | h4) | h5)
                · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
                  · rw [← Var_compare_eq_iff_eq.mp heq]
                    simp only [varIndex]
                    omega
                  · exact absurd hmem Std.TreeSet.not_mem_emptyc
                · exact lt_of_lt_of_le
                    (hbelow v' (hsub1 v'
                      (simpleValOwnVars_subset_simpleValVars lhs v' (hcond_vars v' hcondv))))
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
              · simp only [bVarsOfFormula, bVarsOfTerm, Std.TreeSet.mem_union_iff] at hb
                rcases hb with h | ((hcondv | h) | h)
                · exact absurd h Std.TreeSet.not_mem_emptyc
                · exact absurd hcondv (hcond_bvars v')
                · exact absurd h Std.TreeSet.not_mem_emptyc
                · exact absurd h Std.TreeSet.not_mem_emptyc
              · exact absurd hbbool
                  (not_mem_bVarsOfFormula_bool_ffterm_var gconf sconf sconf.nextVarId fbool hbool
                    v')
          · intro env assignment hmatch val hval
            obtain ⟨val1', hval1', hm1⟩ :=
              resolveSimpleExpr_correct symEnv e1 env assignment lhs hmatch hres1
            have hval2' := tryEvalSimpleExprToFFValue_correct symEnv e2 env assignment rhs hmatch
              hres2
            simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval1', hval2',
              evalLt] at hval
            injection hval with hval
            subst hval
            set assignment' : Assignment c :=
              { assignment with
                ff := fun n => if n = sconf.nextVarId then
                    (if toSigned val1' < toSigned rhs then (1 : FF c) else 0)
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
                    (FFTerm.ite cond (FFTerm.val 1) (FFTerm.val 0)))
                  fbool) ∪
                 bVarsOfFormula (FFFormula.and
                  (FFFormula.eq (FFTerm.var sconf.nextVarId)
                    (FFTerm.ite cond (FFTerm.val 1) (FFTerm.val 0)))
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
                    (FFTerm.ite cond (FFTerm.val 1) (FFTerm.val 0)))
                  fbool) ∪
                 bVarsOfFormula (FFFormula.and
                  (FFFormula.eq (FFTerm.var sconf.nextVarId)
                    (FFTerm.ite cond (FFTerm.val 1) (FFTerm.val 0)))
                  fbool)) →
                assignment'.bool n = assignment.bool n := fun n _ => rfl
            have hsimpleMatch1' : simpleValMatches assignment' lhs val1' :=
              simpleValMatches_agreesOnFF_preserves assignment assignment' lhs val1'
                (symEnvVars symEnv) hsub1 hagreeff hm1
            have hevalTerm1' : evalTerm gconf assignment' lhsTerm
                (specs.map (·.f)) = Except.ok val1' :=
              evalTerm_simpleSymValToTerm gconf assignment' lhs val1' (specs.map (·.f))
                hsimpleMatch1'
            have hffeval : assignment'.ff sconf.nextVarId
                = (if toSigned val1' < toSigned rhs then (1 : FF c) else 0) := by
              simp [hassignment'_def]
            have hiteEval : evalTerm gconf assignment'
                (FFTerm.ite cond (FFTerm.val 1) (FFTerm.val 0)) (specs.map (·.f))
                = Except.ok (if toSigned val1' < toSigned rhs then (1 : FF c) else 0) := by
              have hmin := toSigned_midpoint_le val1'
              by_cases hrhseq : rhs = (c.midpoint : FF c)
              · have hnotlt : ¬ toSigned val1' < toSigned rhs := by rw [hrhseq]; omega
                simp [evalTerm, hcond_def, if_pos hrhseq, evalFormula, hnotlt]
              · by_cases h1 : toSigned (c.midpoint : FF c) ≤ toSigned val1'
                · by_cases h2 : toSigned val1' ≤ toSigned (rhs - 1)
                  · have hlt : toSigned val1' < toSigned rhs := by
                      rw [toSigned_sub_one_of_ne_min rhs hrhseq] at h2; omega
                    simp [evalTerm, hcond_def, if_neg hrhseq, evalFormula,
                      Corellzk2smt.Language.Core.Semantics.Basic.evalLe, hevalTerm1', h1, h2, hlt]
                  · have hnotlt : ¬ toSigned val1' < toSigned rhs := by
                      rw [toSigned_sub_one_of_ne_min rhs hrhseq] at h2; omega
                    simp [evalTerm, hcond_def, if_neg hrhseq, evalFormula,
                      Corellzk2smt.Language.Core.Semantics.Basic.evalLe, hevalTerm1', h1, h2,
                      hnotlt]
                · exact absurd hmin h1
            have hf_eq_true : evalFormula gconf assignment'
                (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (FFTerm.ite cond (FFTerm.val 1) (FFTerm.val 0))) (specs.map (·.f))
                = Except.ok true := by
              simp [evalFormula, evalTerm, hiteEval, hffeval]
            have hf_bool_true : evalFormula gconf assignment'
                fbool (specs.map (·.f)) = Except.ok true := by
              rw [evalFormula_bool_ffterm_var_iff gconf sconf assignment' (specs.map (·.f))
                sconf.nextVarId fbool hbool, hffeval]
              by_cases hlt : toSigned val1' < toSigned rhs <;> simp [hlt]
            refine ⟨assignment', hagreeff, hagreebool, hframeff, hframebool, ?_,
              EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagreeff hmatch,
              ?_⟩
            · exact evalFormula_and_intro gconf assignment'
                (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (FFTerm.ite cond (FFTerm.val 1) (FFTerm.val 0)))
                fbool (specs.map (·.f)) hf_eq_true hf_bool_true
            · simp only [simpleValMatches, hffeval]
          · intro env assignment hmatch assignment' hagree heval_f
            have hmatch' : EnvMatches assignment' symEnv env :=
              EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagree hmatch
            obtain ⟨val1', hval1', hm1'⟩ :=
              resolveSimpleExpr_correct symEnv e1 env assignment' lhs hmatch' hres1
            have hval2' := tryEvalSimpleExprToFFValue_correct symEnv e2 env assignment' rhs hmatch'
              hres2
            have hevalTerm1' : evalTerm gconf assignment' lhsTerm
                (specs.map (·.f)) = Except.ok val1' :=
              evalTerm_simpleSymValToTerm gconf assignment' lhs val1' (specs.map (·.f)) hm1'
            have hiteEval : evalTerm gconf assignment'
                (FFTerm.ite cond (FFTerm.val 1) (FFTerm.val 0)) (specs.map (·.f))
                = Except.ok (if toSigned val1' < toSigned rhs then (1 : FF c) else 0) := by
              have hmin := toSigned_midpoint_le val1'
              by_cases hrhseq : rhs = (c.midpoint : FF c)
              · have hnotlt : ¬ toSigned val1' < toSigned rhs := by rw [hrhseq]; omega
                simp [evalTerm, hcond_def, if_pos hrhseq, evalFormula, hnotlt]
              · by_cases h1 : toSigned (c.midpoint : FF c) ≤ toSigned val1'
                · by_cases h2 : toSigned val1' ≤ toSigned (rhs - 1)
                  · have hlt : toSigned val1' < toSigned rhs := by
                      rw [toSigned_sub_one_of_ne_min rhs hrhseq] at h2; omega
                    simp [evalTerm, hcond_def, if_neg hrhseq, evalFormula,
                      Corellzk2smt.Language.Core.Semantics.Basic.evalLe, hevalTerm1', h1, h2, hlt]
                  · have hnotlt : ¬ toSigned val1' < toSigned rhs := by
                      rw [toSigned_sub_one_of_ne_min rhs hrhseq] at h2; omega
                    simp [evalTerm, hcond_def, if_neg hrhseq, evalFormula,
                      Corellzk2smt.Language.Core.Semantics.Basic.evalLe, hevalTerm1', h1, h2,
                      hnotlt]
                · exact absurd hmin h1
            obtain ⟨heval_feq, _heval_fbool⟩ :=
              evalFormula_and_elim gconf assignment'
                (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (FFTerm.ite cond (FFTerm.val 1) (FFTerm.val 0)))
                fbool (specs.map (·.f)) heval_f
            simp only [evalFormula, evalTerm, hiteEval, Except.ok.injEq] at heval_feq
            have hffeq : assignment'.ff sconf.nextVarId
                = (if toSigned val1' < toSigned rhs then (1 : FF c) else 0) :=
              (beq_iff_eq ..).mp heval_feq
            refine ⟨if toSigned val1' < toSigned rhs then (1 : FF c) else 0, ?_, hmatch', ?_⟩
            · simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval1', hval2',
                evalLt]
            · simp only [simpleValMatches, hffeq]

/-- Mirror of `seExprLtSignedConstantUpperBound_correct`, for `s1 < s2` when `s1` constant-folds:
    ties `outFFVar` to `evalLt`'s own `if`-form by expressing "`lhs < rhs`" as a single-sided
    `FFFormula.range` bound (`lhs + 1` as the lower bound, `c.midpoint - 1` as a permanent
    upper-bound no-op) -- except when `lhs` is itself the field's signed maximum, where the
    condition is directly `FFFormula.false` (nothing exceeds the maximum). -/
theorem seExprLtSignedConstantLowerBound_correct {c : ZKConfig} (gconf : GlobalConfig c)
    (specs : List (FuncSpec c)) (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD)
    (e1 e2 : SimpleExpr c) :
    TranslatesExprCorrectly gconf sconf specs ctx
      (fun env => Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env
        (Expr.bop BinOp.lt e1 e2))
      (fun symEnv => seExprLtSignedConstantLowerBound md gconf sconf symEnv specs e1 e2) := by
  intro symEnv hbelow _hvalid espec hspec_eq
  simp only [seExprLtSignedConstantLowerBound] at hspec_eq
  cases hres1 : tryEvalSimpleExprToFFValue symEnv e1 with
  | error msg => rw [hres1] at hspec_eq; simp at hspec_eq
  | ok lhs =>
      rw [hres1] at hspec_eq
      cases hres2 : resolveSimpleExpr symEnv e2 with
      | error msg => rw [hres2] at hspec_eq; simp at hspec_eq
      | ok rhs =>
          rw [hres2] at hspec_eq
          cases hbool : bool_ffterm gconf sconf (FFTerm.var sconf.nextVarId) with
          | error msg => rw [hbool] at hspec_eq; simp at hspec_eq
          | ok fbool =>
          rw [hbool] at hspec_eq
          injection hspec_eq with hspec_eq
          subst hspec_eq
          set rhsTerm := simpleSymValToTerm rhs with hrhsTerm_def
          set cond : FFFormula c :=
            if lhs = (c.midpoint - 1 : FF c) then FFFormula.false
            else FFFormula.range rhsTerm (lhs + 1) (c.midpoint - 1 : FF c) with hcond_def
          have hsub2 := Corellzk2smt.SymExec.Correctness.Lemmas.resolveSimpleExpr_vars_subset
            symEnv e2 rhs hres2
          have hcond_vars : ∀ v', v' ∈ ffVarsOfFormula cond → v' ∈ simpleValOwnVars rhs := by
            intro v' hv'
            by_cases hlhseq : lhs = (c.midpoint - 1 : FF c)
            · simp only [hcond_def, if_pos hlhseq, ffVarsOfFormula] at hv'
              exact absurd hv' Std.TreeSet.not_mem_emptyc
            · simp only [hcond_def, if_neg hlhseq, ffVarsOfFormula, hrhsTerm_def,
                ffVarsOfTerm_simpleSymValToTerm] at hv'
              exact hv'
          have hcond_bvars : ∀ v', v' ∉ bVarsOfFormula cond := by
            intro v' hv'
            by_cases hlhseq : lhs = (c.midpoint - 1 : FF c)
            · simp only [hcond_def, if_pos hlhseq, bVarsOfFormula] at hv'
              exact absurd hv' Std.TreeSet.not_mem_emptyc
            · simp only [hcond_def, if_neg hlhseq, bVarsOfFormula, hrhsTerm_def,
                bVarsOfTerm_simpleSymValToTerm] at hv'
              exact absurd hv' Std.TreeSet.not_mem_emptyc
          have hmemF_eq : Var.ffv sconf.nextVarId ∈
              ffVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
                (FFTerm.ite cond (FFTerm.val 1) (FFTerm.val 0))) := by
            simp only [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_union_iff]
            exact Or.inl (Std.TreeSet.mem_insert_self ..)
          have hmemF : Var.ffv sconf.nextVarId ∈
              ffVarsOfFormula (FFFormula.and
                (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (FFTerm.ite cond (FFTerm.val 1) (FFTerm.val 0)))
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
              · simp only [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_union_iff] at hff
                rcases hff with h1 | ((hcondv | h4) | h5)
                · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
                  · rw [← Var_compare_eq_iff_eq.mp heq]
                    exact Or.inr (le_refl _)
                  · exact absurd hmem Std.TreeSet.not_mem_emptyc
                · exact Or.inl (hsub2 v'
                    (simpleValOwnVars_subset_simpleValVars rhs v' (hcond_vars v' hcondv)))
                · exact absurd h4 Std.TreeSet.not_mem_emptyc
                · exact absurd h5 Std.TreeSet.not_mem_emptyc
              · rw [mem_ffVarsOfFormula_bool_ffterm_var gconf sconf sconf.nextVarId fbool
                  hbool] at hfbool
                rw [← hfbool]
                exact Or.inr (le_refl _)
            · simp only [bVarsOfFormula] at hb_top
              rcases Std.TreeSet.mem_union_iff.mp hb_top with hb | hbbool
              · simp only [bVarsOfFormula, bVarsOfTerm, Std.TreeSet.mem_union_iff] at hb
                rcases hb with h | ((hcondv | h) | h)
                · exact absurd h Std.TreeSet.not_mem_emptyc
                · exact absurd hcondv (hcond_bvars v')
                · exact absurd h Std.TreeSet.not_mem_emptyc
                · exact absurd h Std.TreeSet.not_mem_emptyc
              · exact absurd hbbool
                  (not_mem_bVarsOfFormula_bool_ffterm_var gconf sconf sconf.nextVarId fbool hbool
                    v')
          · intro v' hv'
            simp only [exprSpecVars] at hv'
            rcases Std.TreeSet.mem_union_iff.mp hv' with hff_top | hb_top
            · simp only [ffVarsOfFormula] at hff_top
              rcases Std.TreeSet.mem_union_iff.mp hff_top with hff | hfbool
              · simp only [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_union_iff] at hff
                rcases hff with h1 | ((hcondv | h4) | h5)
                · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
                  · rw [← Var_compare_eq_iff_eq.mp heq]
                    simp only [varIndex]
                    omega
                  · exact absurd hmem Std.TreeSet.not_mem_emptyc
                · exact lt_of_lt_of_le
                    (hbelow v' (hsub2 v'
                      (simpleValOwnVars_subset_simpleValVars rhs v' (hcond_vars v' hcondv))))
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
              · simp only [bVarsOfFormula, bVarsOfTerm, Std.TreeSet.mem_union_iff] at hb
                rcases hb with h | ((hcondv | h) | h)
                · exact absurd h Std.TreeSet.not_mem_emptyc
                · exact absurd hcondv (hcond_bvars v')
                · exact absurd h Std.TreeSet.not_mem_emptyc
                · exact absurd h Std.TreeSet.not_mem_emptyc
              · exact absurd hbbool
                  (not_mem_bVarsOfFormula_bool_ffterm_var gconf sconf sconf.nextVarId fbool hbool
                    v')
          · intro env assignment hmatch val hval
            have hval1' := tryEvalSimpleExprToFFValue_correct symEnv e1 env assignment lhs hmatch
              hres1
            obtain ⟨val2', hval2', hm2⟩ :=
              resolveSimpleExpr_correct symEnv e2 env assignment rhs hmatch hres2
            simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval1', hval2',
              evalLt] at hval
            injection hval with hval
            subst hval
            set assignment' : Assignment c :=
              { assignment with
                ff := fun n => if n = sconf.nextVarId then
                    (if toSigned lhs < toSigned val2' then (1 : FF c) else 0)
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
                    (FFTerm.ite cond (FFTerm.val 1) (FFTerm.val 0)))
                  fbool) ∪
                 bVarsOfFormula (FFFormula.and
                  (FFFormula.eq (FFTerm.var sconf.nextVarId)
                    (FFTerm.ite cond (FFTerm.val 1) (FFTerm.val 0)))
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
                    (FFTerm.ite cond (FFTerm.val 1) (FFTerm.val 0)))
                  fbool) ∪
                 bVarsOfFormula (FFFormula.and
                  (FFFormula.eq (FFTerm.var sconf.nextVarId)
                    (FFTerm.ite cond (FFTerm.val 1) (FFTerm.val 0)))
                  fbool)) →
                assignment'.bool n = assignment.bool n := fun n _ => rfl
            have hsimpleMatch2' : simpleValMatches assignment' rhs val2' :=
              simpleValMatches_agreesOnFF_preserves assignment assignment' rhs val2'
                (symEnvVars symEnv) hsub2 hagreeff hm2
            have hevalTerm2' : evalTerm gconf assignment' rhsTerm
                (specs.map (·.f)) = Except.ok val2' :=
              evalTerm_simpleSymValToTerm gconf assignment' rhs val2' (specs.map (·.f))
                hsimpleMatch2'
            have hffeval : assignment'.ff sconf.nextVarId
                = (if toSigned lhs < toSigned val2' then (1 : FF c) else 0) := by
              simp [hassignment'_def]
            have hiteEval : evalTerm gconf assignment'
                (FFTerm.ite cond (FFTerm.val 1) (FFTerm.val 0)) (specs.map (·.f))
                = Except.ok (if toSigned lhs < toSigned val2' then (1 : FF c) else 0) := by
              have hmax := toSigned_le_midpoint_sub_one val2'
              by_cases hlhseq : lhs = (c.midpoint - 1 : FF c)
              · have hnotlt : ¬ toSigned lhs < toSigned val2' := by rw [hlhseq]; omega
                simp [evalTerm, hcond_def, if_pos hlhseq, evalFormula, hnotlt]
              · by_cases h1 : toSigned (lhs + 1) ≤ toSigned val2'
                · by_cases h2 : toSigned val2' ≤ toSigned (c.midpoint - 1 : FF c)
                  · have hlt : toSigned lhs < toSigned val2' := by
                      rw [toSigned_add_one_of_ne_max lhs hlhseq] at h1; omega
                    simp [evalTerm, hcond_def, if_neg hlhseq, evalFormula,
                      Corellzk2smt.Language.Core.Semantics.Basic.evalLe, hevalTerm2', h1, h2, hlt]
                  · exact absurd hmax h2
                · have hnotlt : ¬ toSigned lhs < toSigned val2' := by
                    rw [toSigned_add_one_of_ne_max lhs hlhseq] at h1; omega
                  simp [evalTerm, hcond_def, if_neg hlhseq, evalFormula,
                    Corellzk2smt.Language.Core.Semantics.Basic.evalLe, hevalTerm2', h1, hnotlt]
            have hf_eq_true : evalFormula gconf assignment'
                (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (FFTerm.ite cond (FFTerm.val 1) (FFTerm.val 0))) (specs.map (·.f))
                = Except.ok true := by
              simp [evalFormula, evalTerm, hiteEval, hffeval]
            have hf_bool_true : evalFormula gconf assignment'
                fbool (specs.map (·.f)) = Except.ok true := by
              rw [evalFormula_bool_ffterm_var_iff gconf sconf assignment' (specs.map (·.f))
                sconf.nextVarId fbool hbool, hffeval]
              by_cases hlt : toSigned lhs < toSigned val2' <;> simp [hlt]
            refine ⟨assignment', hagreeff, hagreebool, hframeff, hframebool, ?_,
              EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagreeff hmatch,
              ?_⟩
            · exact evalFormula_and_intro gconf assignment'
                (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (FFTerm.ite cond (FFTerm.val 1) (FFTerm.val 0)))
                fbool (specs.map (·.f)) hf_eq_true hf_bool_true
            · simp only [simpleValMatches, hffeval]
          · intro env assignment hmatch assignment' hagree heval_f
            have hmatch' : EnvMatches assignment' symEnv env :=
              EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagree hmatch
            have hval1' := tryEvalSimpleExprToFFValue_correct symEnv e1 env assignment' lhs
              hmatch' hres1
            obtain ⟨val2', hval2', hm2'⟩ :=
              resolveSimpleExpr_correct symEnv e2 env assignment' rhs hmatch' hres2
            have hevalTerm2' : evalTerm gconf assignment' rhsTerm
                (specs.map (·.f)) = Except.ok val2' :=
              evalTerm_simpleSymValToTerm gconf assignment' rhs val2' (specs.map (·.f)) hm2'
            have hiteEval : evalTerm gconf assignment'
                (FFTerm.ite cond (FFTerm.val 1) (FFTerm.val 0)) (specs.map (·.f))
                = Except.ok (if toSigned lhs < toSigned val2' then (1 : FF c) else 0) := by
              have hmax := toSigned_le_midpoint_sub_one val2'
              by_cases hlhseq : lhs = (c.midpoint - 1 : FF c)
              · have hnotlt : ¬ toSigned lhs < toSigned val2' := by rw [hlhseq]; omega
                simp [evalTerm, hcond_def, if_pos hlhseq, evalFormula, hnotlt]
              · by_cases h1 : toSigned (lhs + 1) ≤ toSigned val2'
                · by_cases h2 : toSigned val2' ≤ toSigned (c.midpoint - 1 : FF c)
                  · have hlt : toSigned lhs < toSigned val2' := by
                      rw [toSigned_add_one_of_ne_max lhs hlhseq] at h1; omega
                    simp [evalTerm, hcond_def, if_neg hlhseq, evalFormula,
                      Corellzk2smt.Language.Core.Semantics.Basic.evalLe, hevalTerm2', h1, h2, hlt]
                  · exact absurd hmax h2
                · have hnotlt : ¬ toSigned lhs < toSigned val2' := by
                    rw [toSigned_add_one_of_ne_max lhs hlhseq] at h1; omega
                  simp [evalTerm, hcond_def, if_neg hlhseq, evalFormula,
                    Corellzk2smt.Language.Core.Semantics.Basic.evalLe, hevalTerm2', h1, hnotlt]
            obtain ⟨heval_feq, _heval_fbool⟩ :=
              evalFormula_and_elim gconf assignment'
                (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (FFTerm.ite cond (FFTerm.val 1) (FFTerm.val 0)))
                fbool (specs.map (·.f)) heval_f
            simp only [evalFormula, evalTerm, hiteEval, Except.ok.injEq] at heval_feq
            have hffeq : assignment'.ff sconf.nextVarId
                = (if toSigned lhs < toSigned val2' then (1 : FF c) else 0) :=
              (beq_iff_eq ..).mp heval_feq
            refine ⟨if toSigned lhs < toSigned val2' then (1 : FF c) else 0, ?_, hmatch', ?_⟩
            · simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval1', hval2',
                evalLt]
            · simp only [simpleValMatches, hffeq]

/-- The general (neither operand constant) case: `s1 < s2` when neither side folds. `s1`/`s2`'s
    sign is tested via `FFFormula.range` (reusing the "no-op other bound" trick from the constant
    cases); when the signs differ the answer is immediate (negative `<` non-negative always,
    non-negative `<` negative never), and when they agree the difference `s1 - s2` never
    over/underflows the representable signed range (`toSigned_sub_of_both_nonneg`/
    `toSigned_sub_of_both_neg`), so its own sign decides the comparison. Plus the same
    `bool_ffterm` boolean-tag conjunct as `seExprEq`. -/
theorem seExprLtSignedNonConstant_correct {c : ZKConfig} (gconf : GlobalConfig c)
    (specs : List (FuncSpec c)) (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD)
    (e1 e2 : SimpleExpr c) :
    TranslatesExprCorrectly gconf sconf specs ctx
      (fun env => Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env
        (Expr.bop BinOp.lt e1 e2))
      (fun symEnv => seExprLtSignedNonConstant md gconf sconf symEnv specs e1 e2) := by
  intro symEnv hbelow _hvalid espec hspec_eq
  simp only [seExprLtSignedNonConstant] at hspec_eq
  cases hres1 : resolveSimpleExpr symEnv e1 with
  | error msg => rw [hres1] at hspec_eq; simp at hspec_eq
  | ok lhs =>
      rw [hres1] at hspec_eq
      cases hres2 : resolveSimpleExpr symEnv e2 with
      | error msg => rw [hres2] at hspec_eq; simp at hspec_eq
      | ok rhs =>
          rw [hres2] at hspec_eq
          cases hbool : bool_ffterm gconf sconf (FFTerm.var sconf.nextVarId) with
          | error msg => rw [hbool] at hspec_eq; simp at hspec_eq
          | ok fbool =>
          rw [hbool] at hspec_eq
          injection hspec_eq with hspec_eq
          subst hspec_eq
          set lhsTerm := simpleSymValToTerm lhs with hlhsTerm_def
          set rhsTerm := simpleSymValToTerm rhs with hrhsTerm_def
          set diffTerm : FFTerm c := FFTerm.sub lhsTerm rhsTerm with hdiffTerm_def
          set iteTerm : FFTerm c :=
            FFTerm.ite
              (FFFormula.and (FFFormula.range lhsTerm (c.midpoint : FF c) (c.p - 1 : FF c))
                (FFFormula.range rhsTerm 0 (c.midpoint - 1 : FF c)))
              (FFTerm.val 1)
              (FFTerm.ite
                (FFFormula.and (FFFormula.range lhsTerm 0 (c.midpoint - 1 : FF c))
                  (FFFormula.range rhsTerm (c.midpoint : FF c) (c.p - 1 : FF c)))
                (FFTerm.val 0)
                (FFTerm.ite (FFFormula.range diffTerm (c.midpoint : FF c) (c.p - 1 : FF c))
                  (FFTerm.val 1) (FFTerm.val 0)))
            with hiteTerm_def
          have hsub1 := Corellzk2smt.SymExec.Correctness.Lemmas.resolveSimpleExpr_vars_subset
            symEnv e1 lhs hres1
          have hsub2 := Corellzk2smt.SymExec.Correctness.Lemmas.resolveSimpleExpr_vars_subset
            symEnv e2 rhs hres2
          have hite_vars : ∀ v', v' ∈ ffVarsOfTerm iteTerm →
              v' ∈ simpleValOwnVars lhs ∨ v' ∈ simpleValOwnVars rhs := by
            intro v' hv'
            simp only [hiteTerm_def, hdiffTerm_def, hlhsTerm_def, hrhsTerm_def, ffVarsOfFormula,
              ffVarsOfTerm, ffVarsOfTerm_simpleSymValToTerm, Std.TreeSet.mem_union_iff] at hv'
            tauto
          have hite_bvars : ∀ v', v' ∉ bVarsOfTerm iteTerm := by
            intro v' hv'
            simp only [hiteTerm_def, hdiffTerm_def, hlhsTerm_def, hrhsTerm_def, bVarsOfFormula,
              bVarsOfTerm, bVarsOfTerm_simpleSymValToTerm, Std.TreeSet.mem_union_iff] at hv'
            tauto
          have hmemF_eq : Var.ffv sconf.nextVarId ∈
              ffVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId) iteTerm) := by
            simp only [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_union_iff]
            exact Or.inl (Std.TreeSet.mem_insert_self ..)
          have hmemF : Var.ffv sconf.nextVarId ∈
              ffVarsOfFormula (FFFormula.and
                (FFFormula.eq (FFTerm.var sconf.nextVarId) iteTerm) fbool) := by
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
              · simp only [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_union_iff] at hff
                rcases hff with h1 | hite
                · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
                  · rw [← Var_compare_eq_iff_eq.mp heq]
                    exact Or.inr (le_refl _)
                  · exact absurd hmem Std.TreeSet.not_mem_emptyc
                · rcases hite_vars v' hite with hlv | hrv
                  · exact Or.inl (hsub1 v' (simpleValOwnVars_subset_simpleValVars lhs v' hlv))
                  · exact Or.inl (hsub2 v' (simpleValOwnVars_subset_simpleValVars rhs v' hrv))
              · rw [mem_ffVarsOfFormula_bool_ffterm_var gconf sconf sconf.nextVarId fbool
                  hbool] at hfbool
                rw [← hfbool]
                exact Or.inr (le_refl _)
            · simp only [bVarsOfFormula] at hb_top
              rcases Std.TreeSet.mem_union_iff.mp hb_top with hb | hbbool
              · simp only [bVarsOfFormula, bVarsOfTerm, Std.TreeSet.mem_union_iff] at hb
                rcases hb with h | hite
                · exact absurd h Std.TreeSet.not_mem_emptyc
                · exact absurd hite (hite_bvars v')
              · exact absurd hbbool
                  (not_mem_bVarsOfFormula_bool_ffterm_var gconf sconf sconf.nextVarId fbool hbool
                    v')
          · intro v' hv'
            simp only [exprSpecVars] at hv'
            rcases Std.TreeSet.mem_union_iff.mp hv' with hff_top | hb_top
            · simp only [ffVarsOfFormula] at hff_top
              rcases Std.TreeSet.mem_union_iff.mp hff_top with hff | hfbool
              · simp only [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_union_iff] at hff
                rcases hff with h1 | hite
                · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
                  · rw [← Var_compare_eq_iff_eq.mp heq]
                    simp only [varIndex]
                    omega
                  · exact absurd hmem Std.TreeSet.not_mem_emptyc
                · rcases hite_vars v' hite with hlv | hrv
                  · exact lt_of_lt_of_le
                      (hbelow v' (hsub1 v' (simpleValOwnVars_subset_simpleValVars lhs v' hlv)))
                      (Nat.le_succ _)
                  · exact lt_of_lt_of_le
                      (hbelow v' (hsub2 v' (simpleValOwnVars_subset_simpleValVars rhs v' hrv)))
                      (Nat.le_succ _)
              · rw [mem_ffVarsOfFormula_bool_ffterm_var gconf sconf sconf.nextVarId fbool
                  hbool] at hfbool
                rw [← hfbool]
                simp only [varIndex]
                omega
            · simp only [bVarsOfFormula] at hb_top
              rcases Std.TreeSet.mem_union_iff.mp hb_top with hb | hbbool
              · simp only [bVarsOfFormula, bVarsOfTerm, Std.TreeSet.mem_union_iff] at hb
                rcases hb with h | hite
                · exact absurd h Std.TreeSet.not_mem_emptyc
                · exact absurd hite (hite_bvars v')
              · exact absurd hbbool
                  (not_mem_bVarsOfFormula_bool_ffterm_var gconf sconf sconf.nextVarId fbool hbool
                    v')
          · intro env assignment hmatch val hval
            obtain ⟨val1', hval1', hm1⟩ :=
              resolveSimpleExpr_correct symEnv e1 env assignment lhs hmatch hres1
            obtain ⟨val2', hval2', hm2⟩ :=
              resolveSimpleExpr_correct symEnv e2 env assignment rhs hmatch hres2
            simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval1', hval2',
              evalLt] at hval
            injection hval with hval
            subst hval
            set assignment' : Assignment c :=
              { assignment with
                ff := fun n => if n = sconf.nextVarId then
                    (if toSigned val1' < toSigned val2' then (1 : FF c) else 0)
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
                  (FFFormula.eq (FFTerm.var sconf.nextVarId) iteTerm) fbool) ∪
                 bVarsOfFormula (FFFormula.and
                  (FFFormula.eq (FFTerm.var sconf.nextVarId) iteTerm) fbool)) →
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
                  (FFFormula.eq (FFTerm.var sconf.nextVarId) iteTerm) fbool) ∪
                 bVarsOfFormula (FFFormula.and
                  (FFFormula.eq (FFTerm.var sconf.nextVarId) iteTerm) fbool)) →
                assignment'.bool n = assignment.bool n := fun n _ => rfl
            have hsimpleMatch1' : simpleValMatches assignment' lhs val1' :=
              simpleValMatches_agreesOnFF_preserves assignment assignment' lhs val1'
                (symEnvVars symEnv) hsub1 hagreeff hm1
            have hsimpleMatch2' : simpleValMatches assignment' rhs val2' :=
              simpleValMatches_agreesOnFF_preserves assignment assignment' rhs val2'
                (symEnvVars symEnv) hsub2 hagreeff hm2
            have hevalTerm1' : evalTerm gconf assignment' lhsTerm
                (specs.map (·.f)) = Except.ok val1' :=
              evalTerm_simpleSymValToTerm gconf assignment' lhs val1' (specs.map (·.f))
                hsimpleMatch1'
            have hevalTerm2' : evalTerm gconf assignment' rhsTerm
                (specs.map (·.f)) = Except.ok val2' :=
              evalTerm_simpleSymValToTerm gconf assignment' rhs val2' (specs.map (·.f))
                hsimpleMatch2'
            have hffeval : assignment'.ff sconf.nextVarId
                = (if toSigned val1' < toSigned val2' then (1 : FF c) else 0) := by
              simp [hassignment'_def]
            have hiteEval : evalTerm gconf assignment' iteTerm (specs.map (·.f))
                = Except.ok (if toSigned val1' < toSigned val2' then (1 : FF c) else 0) := by
              have hs1pos_eq := evalFormula_isPositive_eq gconf assignment' (specs.map (·.f))
                lhsTerm val1' hevalTerm1'
              have hs1neg_eq := evalFormula_isNegative_eq gconf assignment' (specs.map (·.f))
                lhsTerm val1' hevalTerm1'
              have hs2pos_eq := evalFormula_isPositive_eq gconf assignment' (specs.map (·.f))
                rhsTerm val2' hevalTerm2'
              have hs2neg_eq := evalFormula_isNegative_eq gconf assignment' (specs.map (·.f))
                rhsTerm val2' hevalTerm2'
              have hdiffTerm_eval : evalTerm gconf assignment' diffTerm (specs.map (·.f))
                  = Except.ok (val1' - val2') := by
                simp only [hdiffTerm_def, evalTerm, hevalTerm1', hevalTerm2']
              have hdiffneg_eq := evalFormula_isNegative_eq gconf assignment' (specs.map (·.f))
                diffTerm (val1' - val2') hdiffTerm_eval
              rw [cast_p_sub_one_field_eq_neg_one] at hs1neg_eq hs2neg_eq hdiffneg_eq
              simp only [hiteTerm_def]
              by_cases h1neg : toSigned val1' < 0
              · have hs1neg_true : evalFormula gconf assignment'
                    (FFFormula.range lhsTerm (c.midpoint : FF c) (-1 : FF c))
                    (specs.map (·.f)) = Except.ok true := by
                  rw [hs1neg_eq]; congr 1; exact decide_eq_true_iff.mpr h1neg
                have hs1pos_false : evalFormula gconf assignment'
                    (FFFormula.range lhsTerm 0 (c.midpoint - 1 : FF c)) (specs.map (·.f))
                    = Except.ok false := by
                  rw [hs1pos_eq]; congr 1
                  exact decide_eq_false_iff_not.mpr (by omega)
                by_cases h2pos : 0 ≤ toSigned val2'
                · have hs2pos_true : evalFormula gconf assignment'
                      (FFFormula.range rhsTerm 0 (c.midpoint - 1 : FF c)) (specs.map (·.f))
                      = Except.ok true := by
                    rw [hs2pos_eq]; congr 1; exact decide_eq_true_iff.mpr h2pos
                  have hc1_true : evalFormula gconf assignment'
                      (FFFormula.and (FFFormula.range lhsTerm (c.midpoint : FF c)
                        (-1 : FF c)) (FFFormula.range rhsTerm 0 (c.midpoint - 1 : FF c)))
                      (specs.map (·.f)) = Except.ok true :=
                    evalFormula_and_intro gconf assignment' _ _ (specs.map (·.f)) hs1neg_true
                      hs2pos_true
                  have hlt : toSigned val1' < toSigned val2' := by omega
                  simp [evalTerm, hc1_true, hlt]
                · have h2neg : toSigned val2' < 0 := by omega
                  have hs2pos_false : evalFormula gconf assignment'
                      (FFFormula.range rhsTerm 0 (c.midpoint - 1 : FF c)) (specs.map (·.f))
                      = Except.ok false := by
                    rw [hs2pos_eq]; congr 1; exact decide_eq_false_iff_not.mpr h2pos
                  have hs2neg_true : evalFormula gconf assignment'
                      (FFFormula.range rhsTerm (c.midpoint : FF c) (-1 : FF c))
                      (specs.map (·.f)) = Except.ok true := by
                    rw [hs2neg_eq]; congr 1; exact decide_eq_true_iff.mpr h2neg
                  have hc1_false : evalFormula gconf assignment'
                      (FFFormula.and (FFFormula.range lhsTerm (c.midpoint : FF c)
                        (-1 : FF c)) (FFFormula.range rhsTerm 0 (c.midpoint - 1 : FF c)))
                      (specs.map (·.f)) = Except.ok false := by
                    simp [evalFormula, hs1neg_true, hs2pos_false]
                  have hc2_false : evalFormula gconf assignment'
                      (FFFormula.and (FFFormula.range lhsTerm 0 (c.midpoint - 1 : FF c))
                        (FFFormula.range rhsTerm (c.midpoint : FF c) (-1 : FF c)))
                      (specs.map (·.f)) = Except.ok false := by
                    simp [evalFormula, hs1pos_false, hs2neg_true]
                  have hval1neg : c.midpoint ≤ val1'.val := (toSigned_lt_zero_iff val1').mp h1neg
                  have hval2neg : c.midpoint ≤ val2'.val := (toSigned_lt_zero_iff val2').mp h2neg
                  have hdiffsigned := toSigned_sub_of_both_neg val1' val2' hval1neg hval2neg
                  by_cases hlt : toSigned val1' < toSigned val2'
                  · have hdiffneg_true : evalFormula gconf assignment'
                        (FFFormula.range diffTerm (c.midpoint : FF c) (-1 : FF c))
                        (specs.map (·.f)) = Except.ok true := by
                      rw [hdiffneg_eq]; congr 1; exact decide_eq_true_iff.mpr (by omega)
                    simp [evalTerm, hc1_false, hc2_false, hdiffneg_true, hlt]
                  · have hdiffneg_false : evalFormula gconf assignment'
                        (FFFormula.range diffTerm (c.midpoint : FF c) (-1 : FF c))
                        (specs.map (·.f)) = Except.ok false := by
                      rw [hdiffneg_eq]; congr 1; exact decide_eq_false_iff_not.mpr (by omega)
                    simp [evalTerm, hc1_false, hc2_false, hdiffneg_false, hlt]
              · have h1pos : 0 ≤ toSigned val1' := by omega
                have hs1neg_false : evalFormula gconf assignment'
                    (FFFormula.range lhsTerm (c.midpoint : FF c) (-1 : FF c))
                    (specs.map (·.f)) = Except.ok false := by
                  rw [hs1neg_eq]; congr 1; exact decide_eq_false_iff_not.mpr h1neg
                have hs1pos_true : evalFormula gconf assignment'
                    (FFFormula.range lhsTerm 0 (c.midpoint - 1 : FF c)) (specs.map (·.f))
                    = Except.ok true := by
                  rw [hs1pos_eq]; congr 1; exact decide_eq_true_iff.mpr h1pos
                by_cases h2neg : toSigned val2' < 0
                · have hs2neg_true : evalFormula gconf assignment'
                      (FFFormula.range rhsTerm (c.midpoint : FF c) (-1 : FF c))
                      (specs.map (·.f)) = Except.ok true := by
                    rw [hs2neg_eq]; congr 1; exact decide_eq_true_iff.mpr h2neg
                  have hc1_false : evalFormula gconf assignment'
                      (FFFormula.and (FFFormula.range lhsTerm (c.midpoint : FF c)
                        (-1 : FF c)) (FFFormula.range rhsTerm 0 (c.midpoint - 1 : FF c)))
                      (specs.map (·.f)) = Except.ok false := by
                    simp [evalFormula, hs1neg_false, hevalTerm2']
                  have hc2_true : evalFormula gconf assignment'
                      (FFFormula.and (FFFormula.range lhsTerm 0 (c.midpoint - 1 : FF c))
                        (FFFormula.range rhsTerm (c.midpoint : FF c) (-1 : FF c)))
                      (specs.map (·.f)) = Except.ok true :=
                    evalFormula_and_intro gconf assignment' _ _ (specs.map (·.f)) hs1pos_true
                      hs2neg_true
                  have hnotlt : ¬ toSigned val1' < toSigned val2' := by omega
                  simp [evalTerm, hc1_false, hc2_true, hnotlt]
                · have h2pos : 0 ≤ toSigned val2' := by omega
                  have hs2neg_false : evalFormula gconf assignment'
                      (FFFormula.range rhsTerm (c.midpoint : FF c) (-1 : FF c))
                      (specs.map (·.f)) = Except.ok false := by
                    rw [hs2neg_eq]; congr 1; exact decide_eq_false_iff_not.mpr h2neg
                  have hc1_false : evalFormula gconf assignment'
                      (FFFormula.and (FFFormula.range lhsTerm (c.midpoint : FF c)
                        (-1 : FF c)) (FFFormula.range rhsTerm 0 (c.midpoint - 1 : FF c)))
                      (specs.map (·.f)) = Except.ok false := by
                    simp [evalFormula, hs1neg_false, hevalTerm2']
                  have hc2_false : evalFormula gconf assignment'
                      (FFFormula.and (FFFormula.range lhsTerm 0 (c.midpoint - 1 : FF c))
                        (FFFormula.range rhsTerm (c.midpoint : FF c) (-1 : FF c)))
                      (specs.map (·.f)) = Except.ok false := by
                    simp [evalFormula, hs1pos_true, hs2neg_false]
                  have hval1pos : val1'.val < c.midpoint := by
                    by_contra hc; exact h1neg ((toSigned_lt_zero_iff val1').mpr (by omega))
                  have hval2pos : val2'.val < c.midpoint := by
                    by_contra hc; exact h2neg ((toSigned_lt_zero_iff val2').mpr (by omega))
                  have hdiffsigned := toSigned_sub_of_both_nonneg val1' val2' hval1pos hval2pos
                  by_cases hlt : toSigned val1' < toSigned val2'
                  · have hdiffneg_true : evalFormula gconf assignment'
                        (FFFormula.range diffTerm (c.midpoint : FF c) (-1 : FF c))
                        (specs.map (·.f)) = Except.ok true := by
                      rw [hdiffneg_eq]; congr 1; exact decide_eq_true_iff.mpr (by omega)
                    simp [evalTerm, hc1_false, hc2_false, hdiffneg_true, hlt]
                  · have hdiffneg_false : evalFormula gconf assignment'
                        (FFFormula.range diffTerm (c.midpoint : FF c) (-1 : FF c))
                        (specs.map (·.f)) = Except.ok false := by
                      rw [hdiffneg_eq]; congr 1; exact decide_eq_false_iff_not.mpr (by omega)
                    simp [evalTerm, hc1_false, hc2_false, hdiffneg_false, hlt]
            have hf_eq_true : evalFormula gconf assignment'
                (FFFormula.eq (FFTerm.var sconf.nextVarId) iteTerm) (specs.map (·.f))
                = Except.ok true := by
              simp [evalFormula, evalTerm, hiteEval, hffeval]
            have hf_bool_true : evalFormula gconf assignment'
                fbool (specs.map (·.f)) = Except.ok true := by
              rw [evalFormula_bool_ffterm_var_iff gconf sconf assignment' (specs.map (·.f))
                sconf.nextVarId fbool hbool, hffeval]
              by_cases hlt : toSigned val1' < toSigned val2' <;> simp [hlt]
            refine ⟨assignment', hagreeff, hagreebool, hframeff, hframebool, ?_,
              EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagreeff hmatch,
              ?_⟩
            · exact evalFormula_and_intro gconf assignment'
                (FFFormula.eq (FFTerm.var sconf.nextVarId) iteTerm) fbool (specs.map (·.f))
                hf_eq_true hf_bool_true
            · simp only [simpleValMatches, hffeval]
          · intro env assignment hmatch assignment' hagree heval_f
            have hmatch' : EnvMatches assignment' symEnv env :=
              EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagree hmatch
            obtain ⟨val1', hval1', hm1'⟩ :=
              resolveSimpleExpr_correct symEnv e1 env assignment' lhs hmatch' hres1
            obtain ⟨val2', hval2', hm2'⟩ :=
              resolveSimpleExpr_correct symEnv e2 env assignment' rhs hmatch' hres2
            have hevalTerm1' : evalTerm gconf assignment' lhsTerm
                (specs.map (·.f)) = Except.ok val1' :=
              evalTerm_simpleSymValToTerm gconf assignment' lhs val1' (specs.map (·.f)) hm1'
            have hevalTerm2' : evalTerm gconf assignment' rhsTerm
                (specs.map (·.f)) = Except.ok val2' :=
              evalTerm_simpleSymValToTerm gconf assignment' rhs val2' (specs.map (·.f)) hm2'
            have hiteEval : evalTerm gconf assignment' iteTerm (specs.map (·.f))
                = Except.ok (if toSigned val1' < toSigned val2' then (1 : FF c) else 0) := by
              have hs1pos_eq := evalFormula_isPositive_eq gconf assignment' (specs.map (·.f))
                lhsTerm val1' hevalTerm1'
              have hs1neg_eq := evalFormula_isNegative_eq gconf assignment' (specs.map (·.f))
                lhsTerm val1' hevalTerm1'
              have hs2pos_eq := evalFormula_isPositive_eq gconf assignment' (specs.map (·.f))
                rhsTerm val2' hevalTerm2'
              have hs2neg_eq := evalFormula_isNegative_eq gconf assignment' (specs.map (·.f))
                rhsTerm val2' hevalTerm2'
              have hdiffTerm_eval : evalTerm gconf assignment' diffTerm (specs.map (·.f))
                  = Except.ok (val1' - val2') := by
                simp only [hdiffTerm_def, evalTerm, hevalTerm1', hevalTerm2']
              have hdiffneg_eq := evalFormula_isNegative_eq gconf assignment' (specs.map (·.f))
                diffTerm (val1' - val2') hdiffTerm_eval
              rw [cast_p_sub_one_field_eq_neg_one] at hs1neg_eq hs2neg_eq hdiffneg_eq
              simp only [hiteTerm_def]
              by_cases h1neg : toSigned val1' < 0
              · have hs1neg_true : evalFormula gconf assignment'
                    (FFFormula.range lhsTerm (c.midpoint : FF c) (-1 : FF c))
                    (specs.map (·.f)) = Except.ok true := by
                  rw [hs1neg_eq]; congr 1; exact decide_eq_true_iff.mpr h1neg
                have hs1pos_false : evalFormula gconf assignment'
                    (FFFormula.range lhsTerm 0 (c.midpoint - 1 : FF c)) (specs.map (·.f))
                    = Except.ok false := by
                  rw [hs1pos_eq]; congr 1
                  exact decide_eq_false_iff_not.mpr (by omega)
                by_cases h2pos : 0 ≤ toSigned val2'
                · have hs2pos_true : evalFormula gconf assignment'
                      (FFFormula.range rhsTerm 0 (c.midpoint - 1 : FF c)) (specs.map (·.f))
                      = Except.ok true := by
                    rw [hs2pos_eq]; congr 1; exact decide_eq_true_iff.mpr h2pos
                  have hc1_true : evalFormula gconf assignment'
                      (FFFormula.and (FFFormula.range lhsTerm (c.midpoint : FF c)
                        (-1 : FF c)) (FFFormula.range rhsTerm 0 (c.midpoint - 1 : FF c)))
                      (specs.map (·.f)) = Except.ok true :=
                    evalFormula_and_intro gconf assignment' _ _ (specs.map (·.f)) hs1neg_true
                      hs2pos_true
                  have hlt : toSigned val1' < toSigned val2' := by omega
                  simp [evalTerm, hc1_true, hlt]
                · have h2neg : toSigned val2' < 0 := by omega
                  have hs2pos_false : evalFormula gconf assignment'
                      (FFFormula.range rhsTerm 0 (c.midpoint - 1 : FF c)) (specs.map (·.f))
                      = Except.ok false := by
                    rw [hs2pos_eq]; congr 1; exact decide_eq_false_iff_not.mpr h2pos
                  have hs2neg_true : evalFormula gconf assignment'
                      (FFFormula.range rhsTerm (c.midpoint : FF c) (-1 : FF c))
                      (specs.map (·.f)) = Except.ok true := by
                    rw [hs2neg_eq]; congr 1; exact decide_eq_true_iff.mpr h2neg
                  have hc1_false : evalFormula gconf assignment'
                      (FFFormula.and (FFFormula.range lhsTerm (c.midpoint : FF c)
                        (-1 : FF c)) (FFFormula.range rhsTerm 0 (c.midpoint - 1 : FF c)))
                      (specs.map (·.f)) = Except.ok false := by
                    simp [evalFormula, hs1neg_true, hs2pos_false]
                  have hc2_false : evalFormula gconf assignment'
                      (FFFormula.and (FFFormula.range lhsTerm 0 (c.midpoint - 1 : FF c))
                        (FFFormula.range rhsTerm (c.midpoint : FF c) (-1 : FF c)))
                      (specs.map (·.f)) = Except.ok false := by
                    simp [evalFormula, hs1pos_false, hs2neg_true]
                  have hval1neg : c.midpoint ≤ val1'.val := (toSigned_lt_zero_iff val1').mp h1neg
                  have hval2neg : c.midpoint ≤ val2'.val := (toSigned_lt_zero_iff val2').mp h2neg
                  have hdiffsigned := toSigned_sub_of_both_neg val1' val2' hval1neg hval2neg
                  by_cases hlt : toSigned val1' < toSigned val2'
                  · have hdiffneg_true : evalFormula gconf assignment'
                        (FFFormula.range diffTerm (c.midpoint : FF c) (-1 : FF c))
                        (specs.map (·.f)) = Except.ok true := by
                      rw [hdiffneg_eq]; congr 1; exact decide_eq_true_iff.mpr (by omega)
                    simp [evalTerm, hc1_false, hc2_false, hdiffneg_true, hlt]
                  · have hdiffneg_false : evalFormula gconf assignment'
                        (FFFormula.range diffTerm (c.midpoint : FF c) (-1 : FF c))
                        (specs.map (·.f)) = Except.ok false := by
                      rw [hdiffneg_eq]; congr 1; exact decide_eq_false_iff_not.mpr (by omega)
                    simp [evalTerm, hc1_false, hc2_false, hdiffneg_false, hlt]
              · have h1pos : 0 ≤ toSigned val1' := by omega
                have hs1neg_false : evalFormula gconf assignment'
                    (FFFormula.range lhsTerm (c.midpoint : FF c) (-1 : FF c))
                    (specs.map (·.f)) = Except.ok false := by
                  rw [hs1neg_eq]; congr 1; exact decide_eq_false_iff_not.mpr h1neg
                have hs1pos_true : evalFormula gconf assignment'
                    (FFFormula.range lhsTerm 0 (c.midpoint - 1 : FF c)) (specs.map (·.f))
                    = Except.ok true := by
                  rw [hs1pos_eq]; congr 1; exact decide_eq_true_iff.mpr h1pos
                by_cases h2neg : toSigned val2' < 0
                · have hs2neg_true : evalFormula gconf assignment'
                      (FFFormula.range rhsTerm (c.midpoint : FF c) (-1 : FF c))
                      (specs.map (·.f)) = Except.ok true := by
                    rw [hs2neg_eq]; congr 1; exact decide_eq_true_iff.mpr h2neg
                  have hc1_false : evalFormula gconf assignment'
                      (FFFormula.and (FFFormula.range lhsTerm (c.midpoint : FF c)
                        (-1 : FF c)) (FFFormula.range rhsTerm 0 (c.midpoint - 1 : FF c)))
                      (specs.map (·.f)) = Except.ok false := by
                    simp [evalFormula, hs1neg_false, hevalTerm2']
                  have hc2_true : evalFormula gconf assignment'
                      (FFFormula.and (FFFormula.range lhsTerm 0 (c.midpoint - 1 : FF c))
                        (FFFormula.range rhsTerm (c.midpoint : FF c) (-1 : FF c)))
                      (specs.map (·.f)) = Except.ok true :=
                    evalFormula_and_intro gconf assignment' _ _ (specs.map (·.f)) hs1pos_true
                      hs2neg_true
                  have hnotlt : ¬ toSigned val1' < toSigned val2' := by omega
                  simp [evalTerm, hc1_false, hc2_true, hnotlt]
                · have h2pos : 0 ≤ toSigned val2' := by omega
                  have hs2neg_false : evalFormula gconf assignment'
                      (FFFormula.range rhsTerm (c.midpoint : FF c) (-1 : FF c))
                      (specs.map (·.f)) = Except.ok false := by
                    rw [hs2neg_eq]; congr 1; exact decide_eq_false_iff_not.mpr h2neg
                  have hc1_false : evalFormula gconf assignment'
                      (FFFormula.and (FFFormula.range lhsTerm (c.midpoint : FF c)
                        (-1 : FF c)) (FFFormula.range rhsTerm 0 (c.midpoint - 1 : FF c)))
                      (specs.map (·.f)) = Except.ok false := by
                    simp [evalFormula, hs1neg_false, hevalTerm2']
                  have hc2_false : evalFormula gconf assignment'
                      (FFFormula.and (FFFormula.range lhsTerm 0 (c.midpoint - 1 : FF c))
                        (FFFormula.range rhsTerm (c.midpoint : FF c) (-1 : FF c)))
                      (specs.map (·.f)) = Except.ok false := by
                    simp [evalFormula, hs1pos_true, hs2neg_false]
                  have hval1pos : val1'.val < c.midpoint := by
                    by_contra hc; exact h1neg ((toSigned_lt_zero_iff val1').mpr (by omega))
                  have hval2pos : val2'.val < c.midpoint := by
                    by_contra hc; exact h2neg ((toSigned_lt_zero_iff val2').mpr (by omega))
                  have hdiffsigned := toSigned_sub_of_both_nonneg val1' val2' hval1pos hval2pos
                  by_cases hlt : toSigned val1' < toSigned val2'
                  · have hdiffneg_true : evalFormula gconf assignment'
                        (FFFormula.range diffTerm (c.midpoint : FF c) (-1 : FF c))
                        (specs.map (·.f)) = Except.ok true := by
                      rw [hdiffneg_eq]; congr 1; exact decide_eq_true_iff.mpr (by omega)
                    simp [evalTerm, hc1_false, hc2_false, hdiffneg_true, hlt]
                  · have hdiffneg_false : evalFormula gconf assignment'
                        (FFFormula.range diffTerm (c.midpoint : FF c) (-1 : FF c))
                        (specs.map (·.f)) = Except.ok false := by
                      rw [hdiffneg_eq]; congr 1; exact decide_eq_false_iff_not.mpr (by omega)
                    simp [evalTerm, hc1_false, hc2_false, hdiffneg_false, hlt]
            obtain ⟨heval_feq, _heval_fbool⟩ :=
              evalFormula_and_elim gconf assignment'
                (FFFormula.eq (FFTerm.var sconf.nextVarId) iteTerm) fbool (specs.map (·.f))
                heval_f
            simp only [evalFormula, evalTerm, hiteEval, Except.ok.injEq] at heval_feq
            have hffeq : assignment'.ff sconf.nextVarId
                = (if toSigned val1' < toSigned val2' then (1 : FF c) else 0) :=
              (beq_iff_eq ..).mp heval_feq
            refine ⟨if toSigned val1' < toSigned val2' then (1 : FF c) else 0, ?_, hmatch', ?_⟩
            · simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval1', hval2',
                evalLt]
            · simp only [simpleValMatches, hffeq]

/-- Combines the three `seExprLtSigned*` cases in dispatch order (constant-RHS, then
    constant-LHS, then neither) -- same "try X, else Y" pattern as `seExprPow_correct`, one level
    deeper. -/
theorem seExprLtSigned_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD) (e1 e2 : SimpleExpr c) :
    TranslatesExprCorrectly gconf sconf specs ctx
      (fun env => Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env
        (Expr.bop BinOp.lt e1 e2))
      (fun symEnv => seExprLtSigned md gconf sconf symEnv specs e1 e2) := by
  intro symEnv hbelow hvalid espec hspec_eq
  simp only [seExprLtSigned] at hspec_eq
  cases hconst1 : seExprLtSignedConstantUpperBound md gconf sconf symEnv specs e1 e2 with
  | ok result =>
      rw [hconst1] at hspec_eq
      injection hspec_eq with hspec_eq
      subst hspec_eq
      exact seExprLtSignedConstantUpperBound_correct gconf specs sconf ctx md e1 e2 symEnv hbelow
        hvalid result hconst1
  | error msg =>
      rw [hconst1] at hspec_eq
      cases hconst2 : seExprLtSignedConstantLowerBound md gconf sconf symEnv specs e1 e2 with
      | ok result =>
          rw [hconst2] at hspec_eq
          injection hspec_eq with hspec_eq
          subst hspec_eq
          exact seExprLtSignedConstantLowerBound_correct gconf specs sconf ctx md e1 e2 symEnv
            hbelow hvalid result hconst2
      | error msg =>
          rw [hconst2] at hspec_eq
          exact seExprLtSignedNonConstant_correct gconf specs sconf ctx md e1 e2 symEnv hbelow
            hvalid espec hspec_eq

/-- `s1 > s2` and `s2 < s1` agree on every successful evaluation: both evaluate `e1`/`e2` against
    the same (pure, order-independent) `env`, and `evalGt v1 v2 = evalLt v2 v1` by definition of
    `toSigned`-comparison. They may disagree on the exact error message when both operands are
    individually ill-defined (whichever is evaluated first wins), which is why this is only an
    `iff` on the `Except.ok` case, not full function equality -- exactly what
    `TranslatesExprCorrectly_of_concrete_iff` needs. -/
theorem evalExpr_gt_ok_iff_lt_swap_ok {c : ZKConfig} (env : Env c) (e1 e2 : SimpleExpr c)
    (val : FF c) :
    Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env (Expr.bop BinOp.gt e1 e2)
      = Except.ok val ↔
    Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env (Expr.bop BinOp.lt e2 e1)
      = Except.ok val := by
  simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr]
  cases h1 : evalSimpleExprToFFValue env e1 <;> cases h2 : evalSimpleExprToFFValue env e2 <;>
    simp [h1, h2, evalGt, evalLt, gt_iff_lt]

/-- Derived directly from `seExprLtSigned_correct` (with the two operands swapped) via
    `TranslatesExprCorrectly_of_concrete_iff` -- `seExprGtSigned` is definitionally
    `seExprLtSigned` with `e1`/`e2` swapped, and `s1 > s2` is semantically `s2 < s1`, so there is
    no need to re-run the `seExprLtSigned_correct` proof. -/
theorem seExprGtSigned_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD) (e1 e2 : SimpleExpr c) :
    TranslatesExprCorrectly gconf sconf specs ctx
      (fun env => Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env
        (Expr.bop BinOp.gt e1 e2))
      (fun symEnv => seExprGtSigned md gconf sconf symEnv specs e1 e2) := by
  have h := seExprLtSigned_correct gconf specs sconf ctx md e2 e1
  exact Corellzk2smt.SymExec.Correctness.Lemmas.TranslatesExprCorrectly_of_concrete_iff
    gconf sconf specs ctx _ _ _ (fun env val => evalExpr_gt_ok_iff_lt_swap_ok env e1 e2 val) h

/-- `≤` and `>` are complementary under `toSigned`'s linear order (`Int`), regardless of argument
    order -- unlike the `Gt`/`Lt` relationship, no swap is involved here. This is the identity that
    makes `seExprLeSigned`'s "one minus `Gt`, same argument order" encoding correct; the *original*
    version of that encoding swapped the arguments (`seExprGtSigned ... s2 s1`), which instead
    computes `Ge`, not `Le` -- confirmed by a concrete counterexample (F5, `s1=1`, `s2=4`) before
    the fix. -/
theorem evalLe_eq_one_sub_evalGt {c : ZKConfig} (v1 v2 : FF c) :
    evalLe v1 v2 = 1 - evalGt v1 v2 := by
  simp only [evalLe, evalGt]
  split_ifs with h1 h2
  · exfalso; omega
  · ring
  · ring
  · exfalso; omega

/-- `evalGt`'s result is always `0` or `1` -- immediate from its `if _ then 1 else 0` shape,
    needed to re-derive `seExprLeSigned`'s `bool_ffterm` tag on the fresh var in the soundness
    direction. -/
theorem evalGt_eq_zero_or_one {c : ZKConfig} (v1 v2 : FF c) :
    evalGt v1 v2 = 0 ∨ evalGt v1 v2 = 1 := by
  simp only [evalGt]; split_ifs <;> simp

/-- Soundness-direction bridge from `.le` to `.gt`: a `.le` success at `val` comes from some `.gt`
    success at `gtVal` (same operands, same evaluation order -- no swap), with `val = 1 - gtVal`
    and `gtVal ∈ {0, 1}`. -/
theorem evalExpr_le_soundness_bridge {c : ZKConfig} (env : Env c) (e1 e2 : SimpleExpr c)
    (val : FF c)
    (h : Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env (Expr.bop BinOp.le e1 e2)
      = Except.ok val) :
    ∃ gtVal, Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env (Expr.bop BinOp.gt e1 e2)
        = Except.ok gtVal ∧
      val = 1 - gtVal ∧ (gtVal = 0 ∨ gtVal = 1) := by
  cases hv1 : evalSimpleExprToFFValue env e1 with
  | error msg =>
      simp [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hv1] at h
  | ok v1 =>
      cases hv2 : evalSimpleExprToFFValue env e2 with
      | error msg =>
          simp [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hv1, hv2] at h
      | ok v2 =>
          simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hv1, hv2] at h
          injection h with h
          refine ⟨evalGt v1 v2, ?_, by rw [← h, evalLe_eq_one_sub_evalGt],
            evalGt_eq_zero_or_one v1 v2⟩
          simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hv1, hv2]

/-- Completeness-direction bridge, the reverse of `evalExpr_le_soundness_bridge`: a `.gt` success
    at `gtVal` gives a `.le` success at `1 - gtVal` (same operands, same evaluation order). -/
theorem evalExpr_gt_to_le {c : ZKConfig} (env : Env c) (e1 e2 : SimpleExpr c) (gtVal : FF c)
    (h : Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env (Expr.bop BinOp.gt e1 e2)
      = Except.ok gtVal) :
    Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env (Expr.bop BinOp.le e1 e2)
      = Except.ok (1 - gtVal) := by
  cases hv1 : evalSimpleExprToFFValue env e1 with
  | error msg =>
      simp [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hv1] at h
  | ok v1 =>
      cases hv2 : evalSimpleExprToFFValue env e2 with
      | error msg =>
          simp [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hv1, hv2] at h
      | ok v2 =>
          simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hv1, hv2] at h
          injection h with h
          subst h
          simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hv1, hv2,
            evalLe_eq_one_sub_evalGt]

/-- `seExprLeSigned` mints one fresh var on top of `seExprGtSigned`'s own spec (`gtSpec`): tied
    down by `outVar = 1 - gtSpec.result`, plus the usual `bool_ffterm` tag. Proved directly against
    `seExprGtSigned_correct` (treating `gtSpec.f`/`gtSpec`'s own vars opaquely, via its own 9-part
    contract) rather than re-deriving anything about `Gt`'s internals -- the first `seExprXXX_correct`
    proof in this file that wraps another already-proved `ExprSpec`, instead of directly resolving
    `SimpleExpr` operands or dispatching to a sibling. -/
theorem seExprLeSigned_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD) (e1 e2 : SimpleExpr c) :
    TranslatesExprCorrectly gconf sconf specs ctx
      (fun env => Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env
        (Expr.bop BinOp.le e1 e2))
      (fun symEnv => seExprLeSigned md gconf sconf symEnv specs e1 e2) := by
  intro symEnv hbelow hvalid espec hspec_eq
  cases hgtSpec : seExprGtSigned md gconf sconf symEnv specs e1 e2 with
  | error msg => simp [seExprLeSigned, hgtSpec] at hspec_eq
  | ok gtSpec =>
      cases hbool : bool_ffterm gconf sconf (FFTerm.var gtSpec.nextVarId) with
      | error msg => simp [seExprLeSigned, hgtSpec, hbool] at hspec_eq
      | ok fbool =>
      simp only [seExprLeSigned, hgtSpec, hbool] at hspec_eq
      injection hspec_eq with hspec_eq
      subst hspec_eq
      obtain ⟨hgt1, hgt2, hgt3, hgt4, hgt5, hgt6, hgt7, hgtsound, hgtcomplete⟩ :=
        seExprGtSigned_correct gconf specs sconf ctx md e1 e2 symEnv hbelow hvalid gtSpec hgtSpec
      have hmemF_eq : Var.ffv gtSpec.nextVarId ∈
          ffVarsOfFormula (FFFormula.eq (FFTerm.var gtSpec.nextVarId)
            (FFTerm.sub (FFTerm.val 1) (simpleSymValToTerm gtSpec.result))) := by
        simp only [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_union_iff]
        exact Or.inl (Std.TreeSet.mem_insert_self ..)
      have hmemF_espec : Var.ffv gtSpec.nextVarId ∈ exprSpecVars
          (ExprSpec.mk gtSpec.outSymEnv
            (FFFormula.and gtSpec.f
              (FFFormula.and
                (FFFormula.eq (FFTerm.var gtSpec.nextVarId)
                  (FFTerm.sub (FFTerm.val 1) (simpleSymValToTerm gtSpec.result)))
                fbool))
            (gtSpec.nextVarId + 1) (SimpleSymVal.ffvar ⟨gtSpec.nextVarId, none⟩)) := by
        simp only [exprSpecVars, ffVarsOfFormula]
        exact Std.TreeSet.mem_union_of_left
          (Std.TreeSet.mem_union_of_right (Std.TreeSet.mem_union_of_left hmemF_eq))
      have hgtF_sub : ∀ v, v ∈ exprSpecVars gtSpec → v ∈ exprSpecVars
          (ExprSpec.mk gtSpec.outSymEnv
            (FFFormula.and gtSpec.f
              (FFFormula.and
                (FFFormula.eq (FFTerm.var gtSpec.nextVarId)
                  (FFTerm.sub (FFTerm.val 1) (simpleSymValToTerm gtSpec.result)))
                fbool))
            (gtSpec.nextVarId + 1) (SimpleSymVal.ffvar ⟨gtSpec.nextVarId, none⟩)) := by
        intro v hv
        simp only [exprSpecVars] at hv
        rcases Std.TreeSet.mem_union_iff.mp hv with hff | hb
        · simp only [exprSpecVars, ffVarsOfFormula]
          exact Std.TreeSet.mem_union_of_left (Std.TreeSet.mem_union_of_left hff)
        · simp only [exprSpecVars, bVarsOfFormula]
          exact Std.TreeSet.mem_union_of_right (Std.TreeSet.mem_union_of_left hb)
      refine ⟨le_trans hgt1 (Nat.le_succ _), ?_, ?_, ?_, varSetBelow_mono (Nat.le_succ _) hgt5,
        hgt6, ValidBinRep_trivial gconf _ _, ?_, ?_⟩
      · intro v' hv'
        simp only [simpleValVars, simpleValOwnVars, Option.map_none, Option.getD_none,
          Std.TreeSet.mem_union_iff] at hv'
        rcases hv' with h | h
        · rcases Std.TreeSet.mem_insert.mp h with heq | hmem
          · rw [← Var_compare_eq_iff_eq.mp heq]
            exact Or.inr hmemF_espec
          · exact absurd hmem Std.TreeSet.not_mem_emptyc
        · exact absurd h Std.TreeSet.not_mem_emptyc
      · intro v' hv'
        simp only [exprSpecVars, ffVarsOfFormula, bVarsOfFormula,
          Std.TreeSet.mem_union_iff] at hv'
        rcases hv' with ((hff_gt | (hff_eq | hff_fbool)) | (hb_gt | (hb_eq | hb_fbool)))
        · exact hgt3 v' (by simp only [exprSpecVars]; exact Std.TreeSet.mem_union_of_left hff_gt)
        · simp only [ffVarsOfFormula, ffVarsOfTerm, ffVarsOfTerm_simpleSymValToTerm,
            Std.TreeSet.mem_union_iff] at hff_eq
          rcases hff_eq with h1 | (h2 | h3)
          · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
            · rw [← Var_compare_eq_iff_eq.mp heq]
              exact Or.inr hgt1
            · exact absurd hmem Std.TreeSet.not_mem_emptyc
          · exact absurd h2 Std.TreeSet.not_mem_emptyc
          · rcases hgt2 v' (simpleValOwnVars_subset_simpleValVars gtSpec.result v' h3)
              with hin | hin
            · exact Or.inl hin
            · exact hgt3 v' hin
        · rw [mem_ffVarsOfFormula_bool_ffterm_var gconf sconf gtSpec.nextVarId fbool
            hbool] at hff_fbool
          rw [← hff_fbool]
          exact Or.inr hgt1
        · exact hgt3 v' (by simp only [exprSpecVars]; exact Std.TreeSet.mem_union_of_right hb_gt)
        · simp only [bVarsOfFormula, bVarsOfTerm, bVarsOfTerm_simpleSymValToTerm,
            Std.TreeSet.mem_union_iff] at hb_eq
          rcases hb_eq with h | h | h <;> exact absurd h Std.TreeSet.not_mem_emptyc
        · exact absurd hb_fbool
            (not_mem_bVarsOfFormula_bool_ffterm_var gconf sconf gtSpec.nextVarId fbool hbool v')
      · intro v' hv'
        simp only [exprSpecVars, ffVarsOfFormula, bVarsOfFormula,
          Std.TreeSet.mem_union_iff] at hv'
        rcases hv' with ((hff_gt | (hff_eq | hff_fbool)) | (hb_gt | (hb_eq | hb_fbool)))
        · exact lt_of_lt_of_le
            (hgt4 v' (by simp only [exprSpecVars]; exact Std.TreeSet.mem_union_of_left hff_gt))
            (Nat.le_succ _)
        · simp only [ffVarsOfFormula, ffVarsOfTerm, ffVarsOfTerm_simpleSymValToTerm,
            Std.TreeSet.mem_union_iff] at hff_eq
          rcases hff_eq with h1 | (h2 | h3)
          · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
            · rw [← Var_compare_eq_iff_eq.mp heq]
              simp only [varIndex]
              omega
            · exact absurd hmem Std.TreeSet.not_mem_emptyc
          · exact absurd h2 Std.TreeSet.not_mem_emptyc
          · rcases hgt2 v' (simpleValOwnVars_subset_simpleValVars gtSpec.result v' h3)
              with hin | hin
            · have hup : varIndex v' < sconf.nextVarId := hbelow v' hin
              show varIndex v' < gtSpec.nextVarId + 1
              omega
            · exact lt_of_lt_of_le (hgt4 v' hin) (Nat.le_succ _)
        · rw [mem_ffVarsOfFormula_bool_ffterm_var gconf sconf gtSpec.nextVarId fbool
            hbool] at hff_fbool
          rw [← hff_fbool]
          simp only [varIndex]
          omega
        · exact lt_of_lt_of_le
            (hgt4 v' (by simp only [exprSpecVars]; exact Std.TreeSet.mem_union_of_right hb_gt))
            (Nat.le_succ _)
        · simp only [bVarsOfFormula, bVarsOfTerm, bVarsOfTerm_simpleSymValToTerm,
            Std.TreeSet.mem_union_iff] at hb_eq
          rcases hb_eq with h | h | h <;> exact absurd h Std.TreeSet.not_mem_emptyc
        · exact absurd hb_fbool
            (not_mem_bVarsOfFormula_bool_ffterm_var gconf sconf gtSpec.nextVarId fbool hbool v')
      · intro env assignment hmatch val hval
        obtain ⟨gtVal, hgtval, hval_eq, hgtVal01⟩ :=
          evalExpr_le_soundness_bridge env e1 e2 val hval
        obtain ⟨assignment', hagreeff, hagreebool, hframeff, hframebool, hf_true, hmatch_out,
            hresmatch⟩ := hgtsound env assignment hmatch gtVal hgtval
        set assignment'' : Assignment c :=
          { assignment' with
            ff := fun n => if n = gtSpec.nextVarId then 1 - gtVal else assignment'.ff n }
          with hassignment''_def
        have hagreeff'' : agreesOnFF (symEnvVars symEnv) assignment assignment'' := by
          intro n hn
          have hlt : n < sconf.nextVarId := hbelow (Var.ffv n) hn
          have hup : sconf.nextVarId ≤ gtSpec.nextVarId := hgt1
          have hne : n ≠ gtSpec.nextVarId := Nat.ne_of_lt (lt_of_lt_of_le hlt hup)
          rw [hagreeff n hn]
          simp only [hassignment''_def, if_neg hne]
        have hagreebool'' : agreesOnBool (symEnvVars symEnv) assignment assignment'' := hagreebool
        have hgtF_agreeFF : agreesOnFF (ffVarsOfFormula gtSpec.f) assignment' assignment'' := by
          intro n hn
          have hlt : n < gtSpec.nextVarId :=
            hgt4 (Var.ffv n) (by simp only [exprSpecVars]; exact Std.TreeSet.mem_union_of_left hn)
          have hne : n ≠ gtSpec.nextVarId := Nat.ne_of_lt hlt
          simp only [hassignment''_def, if_neg hne]
        have hgtF_agreeBool : agreesOnBool (bVarsOfFormula gtSpec.f) assignment' assignment'' :=
          fun n _ => rfl
        have hgtF_true'' :
            evalFormula gconf assignment'' gtSpec.f (specs.map (·.f)) = Except.ok true := by
          rw [← evalFormula_congr gconf (specs.map (·.f)) gtSpec.f assignment' assignment''
            hgtF_agreeFF hgtF_agreeBool]
          exact hf_true
        have hresultAgree : agreesOnFF (simpleValVars gtSpec.result) assignment' assignment'' := by
          intro n hn
          have hn' := hgt2 (Var.ffv n) hn
          have hlt : n < gtSpec.nextVarId := by
            rcases hn' with h | h
            · have hup : n < sconf.nextVarId := hbelow (Var.ffv n) h
              have hup2 : sconf.nextVarId ≤ gtSpec.nextVarId := hgt1
              exact lt_of_lt_of_le hup hup2
            · exact hgt4 (Var.ffv n) h
          have hne : n ≠ gtSpec.nextVarId := Nat.ne_of_lt hlt
          simp only [hassignment''_def, if_neg hne]
        have hresmatch'' : simpleValMatches assignment'' gtSpec.result gtVal :=
          simpleValMatches_agreesOnFF_preserves assignment' assignment'' gtSpec.result gtVal
            (simpleValVars gtSpec.result) (fun v hv => hv) hresultAgree hresmatch
        have hevalTermResult'' : evalTerm gconf assignment'' (simpleSymValToTerm gtSpec.result)
            (specs.map (·.f)) = Except.ok gtVal :=
          evalTerm_simpleSymValToTerm gconf assignment'' gtSpec.result gtVal (specs.map (·.f))
            hresmatch''
        have hffeval'' : assignment''.ff gtSpec.nextVarId = 1 - gtVal := by
          simp [hassignment''_def]
        have heqTrue : evalFormula gconf assignment''
            (FFFormula.eq (FFTerm.var gtSpec.nextVarId)
              (FFTerm.sub (FFTerm.val 1) (simpleSymValToTerm gtSpec.result)))
            (specs.map (·.f)) = Except.ok true := by
          simp [evalFormula, evalTerm, hevalTermResult'', hffeval'']
        have hfboolTrue : evalFormula gconf assignment'' fbool (specs.map (·.f))
            = Except.ok true := by
          rw [evalFormula_bool_ffterm_var_iff gconf sconf assignment'' (specs.map (·.f))
            gtSpec.nextVarId fbool hbool, hffeval'']
          rcases hgtVal01 with h | h <;> simp [h]
        have houtAgree : agreesOnFF (symEnvVars gtSpec.outSymEnv) assignment' assignment'' := by
          intro n hn
          have hlt : n < gtSpec.nextVarId := hgt5 (Var.ffv n) hn
          have hne : n ≠ gtSpec.nextVarId := Nat.ne_of_lt hlt
          simp only [hassignment''_def, if_neg hne]
        have hframeff'' : ∀ n, Var.ffv n ∉ exprSpecVars
              (ExprSpec.mk gtSpec.outSymEnv
                (FFFormula.and gtSpec.f
                  (FFFormula.and
                    (FFFormula.eq (FFTerm.var gtSpec.nextVarId)
                      (FFTerm.sub (FFTerm.val 1) (simpleSymValToTerm gtSpec.result)))
                    fbool))
                (gtSpec.nextVarId + 1) (SimpleSymVal.ffvar ⟨gtSpec.nextVarId, none⟩)) →
            assignment''.ff n = assignment.ff n := by
          intro n hn
          have hne : n ≠ gtSpec.nextVarId := by
            intro heqn
            apply hn
            rw [heqn]
            exact hmemF_espec
          have hnotgt : Var.ffv n ∉ exprSpecVars gtSpec := fun hcontra => hn (hgtF_sub _ hcontra)
          rw [show assignment''.ff n = assignment'.ff n from by
            simp only [hassignment''_def, if_neg hne]]
          exact hframeff n hnotgt
        have hframebool'' : ∀ n, Var.boolv n ∉ exprSpecVars
              (ExprSpec.mk gtSpec.outSymEnv
                (FFFormula.and gtSpec.f
                  (FFFormula.and
                    (FFFormula.eq (FFTerm.var gtSpec.nextVarId)
                      (FFTerm.sub (FFTerm.val 1) (simpleSymValToTerm gtSpec.result)))
                    fbool))
                (gtSpec.nextVarId + 1) (SimpleSymVal.ffvar ⟨gtSpec.nextVarId, none⟩)) →
            assignment''.bool n = assignment.bool n := by
          intro n hn
          have hnotgt : Var.boolv n ∉ exprSpecVars gtSpec := fun hcontra => hn (hgtF_sub _ hcontra)
          exact hframebool n hnotgt
        refine ⟨assignment'', hagreeff'', hagreebool'', hframeff'', hframebool'', ?_,
          EnvMatches_agreesOnFF_preserves assignment' assignment'' gtSpec.outSymEnv env houtAgree
            hmatch_out, ?_⟩
        · exact evalFormula_and_intro gconf assignment'' gtSpec.f
            (FFFormula.and
              (FFFormula.eq (FFTerm.var gtSpec.nextVarId)
                (FFTerm.sub (FFTerm.val 1) (simpleSymValToTerm gtSpec.result)))
              fbool)
            (specs.map (·.f)) hgtF_true''
            (evalFormula_and_intro gconf assignment''
              (FFFormula.eq (FFTerm.var gtSpec.nextVarId)
                (FFTerm.sub (FFTerm.val 1) (simpleSymValToTerm gtSpec.result)))
              fbool (specs.map (·.f)) heqTrue hfboolTrue)
        · simp only [simpleValMatches]
          rw [hval_eq]
          exact hffeval''
      · intro env assignment hmatch assignment' hagree hform
        obtain ⟨hgtF_true, hrest_true⟩ :=
          evalFormula_and_elim gconf assignment' gtSpec.f
            (FFFormula.and
              (FFFormula.eq (FFTerm.var gtSpec.nextVarId)
                (FFTerm.sub (FFTerm.val 1) (simpleSymValToTerm gtSpec.result)))
              fbool)
            (specs.map (·.f)) hform
        obtain ⟨heq_true, _hfbool_true⟩ :=
          evalFormula_and_elim gconf assignment'
            (FFFormula.eq (FFTerm.var gtSpec.nextVarId)
              (FFTerm.sub (FFTerm.val 1) (simpleSymValToTerm gtSpec.result)))
            fbool (specs.map (·.f)) hrest_true
        obtain ⟨gtVal, hgtval_eq, hmatch_out, hresmatch⟩ :=
          hgtcomplete env assignment hmatch assignment' hagree hgtF_true
        have hevalTermResult : evalTerm gconf assignment' (simpleSymValToTerm gtSpec.result)
            (specs.map (·.f)) = Except.ok gtVal :=
          evalTerm_simpleSymValToTerm gconf assignment' gtSpec.result gtVal (specs.map (·.f))
            hresmatch
        have hffeq : assignment'.ff gtSpec.nextVarId = 1 - gtVal := by
          simp [evalFormula, evalTerm, hevalTermResult] at heq_true
          exact heq_true
        refine ⟨1 - gtVal, evalExpr_gt_to_le env e1 e2 gtVal hgtval_eq, hmatch_out, ?_⟩
        simp only [simpleValMatches]
        exact hffeq

/-- `≥` and `≤` are complementary the same way `>`/`<` are, with the arguments swapped -- mirrors
    `evalExpr_gt_ok_iff_lt_swap_ok` exactly. -/
theorem evalExpr_ge_ok_iff_le_swap_ok {c : ZKConfig} (env : Env c) (e1 e2 : SimpleExpr c)
    (val : FF c) :
    Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env (Expr.bop BinOp.ge e1 e2)
      = Except.ok val ↔
    Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env (Expr.bop BinOp.le e2 e1)
      = Except.ok val := by
  simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr]
  cases h1 : evalSimpleExprToFFValue env e1 <;> cases h2 : evalSimpleExprToFFValue env e2 <;>
    simp [h1, h2, evalGe, evalLe, ge_iff_le]

/-- Derived directly from `seExprLeSigned_correct` (with the two operands swapped) via
    `TranslatesExprCorrectly_of_concrete_iff` -- mirrors `seExprGtSigned_correct` exactly, one
    level up (`Ge` from `Le`, instead of `Gt` from `Lt`). -/
theorem seExprGeSigned_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD) (e1 e2 : SimpleExpr c) :
    TranslatesExprCorrectly gconf sconf specs ctx
      (fun env => Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env
        (Expr.bop BinOp.ge e1 e2))
      (fun symEnv => seExprGeSigned md gconf sconf symEnv specs e1 e2) := by
  have h := seExprLeSigned_correct gconf specs sconf ctx md e2 e1
  exact Corellzk2smt.SymExec.Correctness.Lemmas.TranslatesExprCorrectly_of_concrete_iff
    gconf sconf specs ctx _ _ _ (fun env val => evalExpr_ge_ok_iff_le_swap_ok env e1 e2 val) h

end Corellzk2smt.SymExec.Correctness.BoolExprCorrectness
