import Corellzk2smt.SymExec.Correctness.Lemmas
import Corellzk2smt.SymExec.Correctness.FuncCallCorrectness
import Corellzk2smt.SymExec.ArithExpr

/-!
Correctness statements for the arithmetic `seExprXXX` operations (`SymExec/ArithExpr.lean`)
against their concrete `Expr`-level counterparts. Every one of these is currently an honest
`sorry` -- each `seExprXXX` is a permanent `"Not implemented yet"` stub (`Except.error`), so its
`TranslatesExprCorrectly` obligation would be vacuously provable that way, but that proves the
wrong thing (see `AssignmentCorrectness.lean`'s `seEvalExpr_correct` docstring for the same
reasoning). Left open until each operator is actually implemented -- `seEvalExpr_correct`
dispatches to these by name, so discharging one of these `sorry`s is exactly what's needed to make
that operator's case of `seEvalExpr_correct` (and hence `seEvalAssignmentNonConst_correct`) real.
-/

namespace Corellzk2smt.SymExec.Correctness.ArithExprCorrectness

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

/-- `seExprAdd` resolves both operands' symbolic values `v1`/`v2`, mints one fresh var tied to
    them via `outVar = v1 + v2`, and reports that fresh var as the result -- the two-operand
    analogue of `seExprNeg_correct`'s "mint one fresh var, tie it down with an `.eq` formula"
    pattern. Soundness/completeness proceed identically, just discharging both operands' resolve
    facts instead of one. -/
theorem seExprAdd_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD) (e1 e2 : SimpleExpr c) :
    TranslatesExprCorrectly gconf sconf specs ctx
      (fun env => Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env
        (Expr.bop BinOp.add e1 e2))
      (fun symEnv => seExprAdd md gconf sconf symEnv specs e1 e2) := by
  intro symEnv hbelow _hvalid espec hspec_eq
  simp only [seExprAdd] at hspec_eq
  cases hres1 : resolveSimpleExpr symEnv e1 with
  | error msg => rw [hres1] at hspec_eq; simp at hspec_eq
  | ok v1 =>
      rw [hres1] at hspec_eq
      cases hres2 : resolveSimpleExpr symEnv e2 with
      | error msg => rw [hres2] at hspec_eq; simp at hspec_eq
      | ok v2 =>
          rw [hres2] at hspec_eq
          injection hspec_eq with hspec_eq
          subst hspec_eq
          have hsub1 := Corellzk2smt.SymExec.Correctness.Lemmas.resolveSimpleExpr_vars_subset
            symEnv e1 v1 hres1
          have hsub2 := Corellzk2smt.SymExec.Correctness.Lemmas.resolveSimpleExpr_vars_subset
            symEnv e2 v2 hres2
          have hmemF : Var.ffv sconf.nextVarId ∈
              ffVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
                (FFTerm.add (simpleSymValToTerm v1) (simpleSymValToTerm v2))) := by
            simp only [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_union_iff]
            exact Or.inl (Std.TreeSet.mem_insert_self ..)
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
            rcases Std.TreeSet.mem_union_iff.mp hv' with hff | hb
            · simp only [ffVarsOfFormula, ffVarsOfTerm, ffVarsOfTerm_simpleSymValToTerm,
                Std.TreeSet.mem_union_iff] at hff
              rcases hff with h1 | h2 | h3
              · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
                · rw [← Var_compare_eq_iff_eq.mp heq]
                  exact Or.inr (le_refl _)
                · exact absurd hmem Std.TreeSet.not_mem_emptyc
              · exact Or.inl (hsub1 v' (simpleValOwnVars_subset_simpleValVars v1 v' h2))
              · exact Or.inl (hsub2 v' (simpleValOwnVars_subset_simpleValVars v2 v' h3))
            · simp only [bVarsOfFormula, bVarsOfTerm, bVarsOfTerm_simpleSymValToTerm,
                Std.TreeSet.mem_union_iff] at hb
              rcases hb with h | h | h <;> exact absurd h Std.TreeSet.not_mem_emptyc
          · intro v' hv'
            simp only [exprSpecVars] at hv'
            rcases Std.TreeSet.mem_union_iff.mp hv' with hff | hb
            · simp only [ffVarsOfFormula, ffVarsOfTerm, ffVarsOfTerm_simpleSymValToTerm,
                Std.TreeSet.mem_union_iff] at hff
              rcases hff with h1 | h2 | h3
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
            · simp only [bVarsOfFormula, bVarsOfTerm, bVarsOfTerm_simpleSymValToTerm,
                Std.TreeSet.mem_union_iff] at hb
              rcases hb with h | h | h <;> exact absurd h Std.TreeSet.not_mem_emptyc
          · intro env assignment hmatch val hval
            obtain ⟨val1', hval1', hm1⟩ :=
              resolveSimpleExpr_correct symEnv e1 env assignment v1 hmatch hres1
            obtain ⟨val2', hval2', hm2⟩ :=
              resolveSimpleExpr_correct symEnv e2 env assignment v2 hmatch hres2
            simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval1', hval2',
              evalAdd] at hval
            injection hval with hval
            subst hval
            set assignment' : Assignment c :=
              { assignment with
                ff := fun n => if n = sconf.nextVarId then val1' + val2' else assignment.ff n }
              with hassignment'_def
            have hagreeff : agreesOnFF (symEnvVars symEnv) assignment assignment' := by
              intro n hn
              have hne : n ≠ sconf.nextVarId := Nat.ne_of_lt (hbelow (Var.ffv n) hn)
              simp only [hassignment'_def, if_neg hne]
            have hagreebool : agreesOnBool (symEnvVars symEnv) assignment assignment' :=
              fun n _ => rfl
            have hframeff : ∀ n, Var.ffv n ∉
                (ffVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (FFTerm.add (simpleSymValToTerm v1) (simpleSymValToTerm v2))) ∪
                 bVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (FFTerm.add (simpleSymValToTerm v1) (simpleSymValToTerm v2)))) →
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
                  (FFTerm.add (simpleSymValToTerm v1) (simpleSymValToTerm v2))) ∪
                 bVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (FFTerm.add (simpleSymValToTerm v1) (simpleSymValToTerm v2)))) →
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
            have hffeval : assignment'.ff sconf.nextVarId = val1' + val2' := by
              simp [hassignment'_def]
            refine ⟨assignment', hagreeff, hagreebool, hframeff, hframebool, ?_,
              EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagreeff hmatch,
              ?_⟩
            · simp [evalFormula, evalTerm, hevalTerm1', hevalTerm2', hffeval]
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
            simp only [evalFormula, evalTerm, hevalTerm1', hevalTerm2', Except.ok.injEq] at heval_f
            have hffeq : assignment'.ff sconf.nextVarId = val1' + val2' :=
              (beq_iff_eq ..).mp heval_f
            refine ⟨val1' + val2', ?_, hmatch', ?_⟩
            · simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval1', hval2',
                evalAdd]
            · simp only [simpleValMatches, hffeq]

/-- Mirror of `seExprAdd_correct`, for `seExprSub` (`outVar = v1 - v2`). -/
theorem seExprSub_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD) (e1 e2 : SimpleExpr c) :
    TranslatesExprCorrectly gconf sconf specs ctx
      (fun env => Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env
        (Expr.bop BinOp.sub e1 e2))
      (fun symEnv => seExprSub md gconf sconf symEnv specs e1 e2) := by
  intro symEnv hbelow _hvalid espec hspec_eq
  simp only [seExprSub] at hspec_eq
  cases hres1 : resolveSimpleExpr symEnv e1 with
  | error msg => rw [hres1] at hspec_eq; simp at hspec_eq
  | ok v1 =>
      rw [hres1] at hspec_eq
      cases hres2 : resolveSimpleExpr symEnv e2 with
      | error msg => rw [hres2] at hspec_eq; simp at hspec_eq
      | ok v2 =>
          rw [hres2] at hspec_eq
          injection hspec_eq with hspec_eq
          subst hspec_eq
          have hsub1 := Corellzk2smt.SymExec.Correctness.Lemmas.resolveSimpleExpr_vars_subset
            symEnv e1 v1 hres1
          have hsub2 := Corellzk2smt.SymExec.Correctness.Lemmas.resolveSimpleExpr_vars_subset
            symEnv e2 v2 hres2
          have hmemF : Var.ffv sconf.nextVarId ∈
              ffVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
                (FFTerm.sub (simpleSymValToTerm v1) (simpleSymValToTerm v2))) := by
            simp only [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_union_iff]
            exact Or.inl (Std.TreeSet.mem_insert_self ..)
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
            rcases Std.TreeSet.mem_union_iff.mp hv' with hff | hb
            · simp only [ffVarsOfFormula, ffVarsOfTerm, ffVarsOfTerm_simpleSymValToTerm,
                Std.TreeSet.mem_union_iff] at hff
              rcases hff with h1 | h2 | h3
              · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
                · rw [← Var_compare_eq_iff_eq.mp heq]
                  exact Or.inr (le_refl _)
                · exact absurd hmem Std.TreeSet.not_mem_emptyc
              · exact Or.inl (hsub1 v' (simpleValOwnVars_subset_simpleValVars v1 v' h2))
              · exact Or.inl (hsub2 v' (simpleValOwnVars_subset_simpleValVars v2 v' h3))
            · simp only [bVarsOfFormula, bVarsOfTerm, bVarsOfTerm_simpleSymValToTerm,
                Std.TreeSet.mem_union_iff] at hb
              rcases hb with h | h | h <;> exact absurd h Std.TreeSet.not_mem_emptyc
          · intro v' hv'
            simp only [exprSpecVars] at hv'
            rcases Std.TreeSet.mem_union_iff.mp hv' with hff | hb
            · simp only [ffVarsOfFormula, ffVarsOfTerm, ffVarsOfTerm_simpleSymValToTerm,
                Std.TreeSet.mem_union_iff] at hff
              rcases hff with h1 | h2 | h3
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
            · simp only [bVarsOfFormula, bVarsOfTerm, bVarsOfTerm_simpleSymValToTerm,
                Std.TreeSet.mem_union_iff] at hb
              rcases hb with h | h | h <;> exact absurd h Std.TreeSet.not_mem_emptyc
          · intro env assignment hmatch val hval
            obtain ⟨val1', hval1', hm1⟩ :=
              resolveSimpleExpr_correct symEnv e1 env assignment v1 hmatch hres1
            obtain ⟨val2', hval2', hm2⟩ :=
              resolveSimpleExpr_correct symEnv e2 env assignment v2 hmatch hres2
            simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval1', hval2',
              evalSub] at hval
            injection hval with hval
            subst hval
            set assignment' : Assignment c :=
              { assignment with
                ff := fun n => if n = sconf.nextVarId then val1' - val2' else assignment.ff n }
              with hassignment'_def
            have hagreeff : agreesOnFF (symEnvVars symEnv) assignment assignment' := by
              intro n hn
              have hne : n ≠ sconf.nextVarId := Nat.ne_of_lt (hbelow (Var.ffv n) hn)
              simp only [hassignment'_def, if_neg hne]
            have hagreebool : agreesOnBool (symEnvVars symEnv) assignment assignment' :=
              fun n _ => rfl
            have hframeff : ∀ n, Var.ffv n ∉
                (ffVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (FFTerm.sub (simpleSymValToTerm v1) (simpleSymValToTerm v2))) ∪
                 bVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (FFTerm.sub (simpleSymValToTerm v1) (simpleSymValToTerm v2)))) →
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
                  (FFTerm.sub (simpleSymValToTerm v1) (simpleSymValToTerm v2))) ∪
                 bVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (FFTerm.sub (simpleSymValToTerm v1) (simpleSymValToTerm v2)))) →
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
            have hffeval : assignment'.ff sconf.nextVarId = val1' - val2' := by
              simp [hassignment'_def]
            refine ⟨assignment', hagreeff, hagreebool, hframeff, hframebool, ?_,
              EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagreeff hmatch,
              ?_⟩
            · simp [evalFormula, evalTerm, hevalTerm1', hevalTerm2', hffeval]
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
            simp only [evalFormula, evalTerm, hevalTerm1', hevalTerm2', Except.ok.injEq] at heval_f
            have hffeq : assignment'.ff sconf.nextVarId = val1' - val2' :=
              (beq_iff_eq ..).mp heval_f
            refine ⟨val1' - val2', ?_, hmatch', ?_⟩
            · simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval1', hval2',
                evalSub]
            · simp only [simpleValMatches, hffeq]

/-- Mirror of `seExprAdd_correct`, for `seExprMul` (`outVar = v1 * v2`). -/
theorem seExprMul_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD) (e1 e2 : SimpleExpr c) :
    TranslatesExprCorrectly gconf sconf specs ctx
      (fun env => Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env
        (Expr.bop BinOp.mul e1 e2))
      (fun symEnv => seExprMul md gconf sconf symEnv specs e1 e2) := by
  intro symEnv hbelow _hvalid espec hspec_eq
  simp only [seExprMul] at hspec_eq
  cases hres1 : resolveSimpleExpr symEnv e1 with
  | error msg => rw [hres1] at hspec_eq; simp at hspec_eq
  | ok v1 =>
      rw [hres1] at hspec_eq
      cases hres2 : resolveSimpleExpr symEnv e2 with
      | error msg => rw [hres2] at hspec_eq; simp at hspec_eq
      | ok v2 =>
          rw [hres2] at hspec_eq
          injection hspec_eq with hspec_eq
          subst hspec_eq
          have hsub1 := Corellzk2smt.SymExec.Correctness.Lemmas.resolveSimpleExpr_vars_subset
            symEnv e1 v1 hres1
          have hsub2 := Corellzk2smt.SymExec.Correctness.Lemmas.resolveSimpleExpr_vars_subset
            symEnv e2 v2 hres2
          have hmemF : Var.ffv sconf.nextVarId ∈
              ffVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
                (FFTerm.mul (simpleSymValToTerm v1) (simpleSymValToTerm v2))) := by
            simp only [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_union_iff]
            exact Or.inl (Std.TreeSet.mem_insert_self ..)
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
            rcases Std.TreeSet.mem_union_iff.mp hv' with hff | hb
            · simp only [ffVarsOfFormula, ffVarsOfTerm, ffVarsOfTerm_simpleSymValToTerm,
                Std.TreeSet.mem_union_iff] at hff
              rcases hff with h1 | h2 | h3
              · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
                · rw [← Var_compare_eq_iff_eq.mp heq]
                  exact Or.inr (le_refl _)
                · exact absurd hmem Std.TreeSet.not_mem_emptyc
              · exact Or.inl (hsub1 v' (simpleValOwnVars_subset_simpleValVars v1 v' h2))
              · exact Or.inl (hsub2 v' (simpleValOwnVars_subset_simpleValVars v2 v' h3))
            · simp only [bVarsOfFormula, bVarsOfTerm, bVarsOfTerm_simpleSymValToTerm,
                Std.TreeSet.mem_union_iff] at hb
              rcases hb with h | h | h <;> exact absurd h Std.TreeSet.not_mem_emptyc
          · intro v' hv'
            simp only [exprSpecVars] at hv'
            rcases Std.TreeSet.mem_union_iff.mp hv' with hff | hb
            · simp only [ffVarsOfFormula, ffVarsOfTerm, ffVarsOfTerm_simpleSymValToTerm,
                Std.TreeSet.mem_union_iff] at hff
              rcases hff with h1 | h2 | h3
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
            · simp only [bVarsOfFormula, bVarsOfTerm, bVarsOfTerm_simpleSymValToTerm,
                Std.TreeSet.mem_union_iff] at hb
              rcases hb with h | h | h <;> exact absurd h Std.TreeSet.not_mem_emptyc
          · intro env assignment hmatch val hval
            obtain ⟨val1', hval1', hm1⟩ :=
              resolveSimpleExpr_correct symEnv e1 env assignment v1 hmatch hres1
            obtain ⟨val2', hval2', hm2⟩ :=
              resolveSimpleExpr_correct symEnv e2 env assignment v2 hmatch hres2
            simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval1', hval2',
              evalMul] at hval
            injection hval with hval
            subst hval
            set assignment' : Assignment c :=
              { assignment with
                ff := fun n => if n = sconf.nextVarId then val1' * val2' else assignment.ff n }
              with hassignment'_def
            have hagreeff : agreesOnFF (symEnvVars symEnv) assignment assignment' := by
              intro n hn
              have hne : n ≠ sconf.nextVarId := Nat.ne_of_lt (hbelow (Var.ffv n) hn)
              simp only [hassignment'_def, if_neg hne]
            have hagreebool : agreesOnBool (symEnvVars symEnv) assignment assignment' :=
              fun n _ => rfl
            have hframeff : ∀ n, Var.ffv n ∉
                (ffVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (FFTerm.mul (simpleSymValToTerm v1) (simpleSymValToTerm v2))) ∪
                 bVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (FFTerm.mul (simpleSymValToTerm v1) (simpleSymValToTerm v2)))) →
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
                  (FFTerm.mul (simpleSymValToTerm v1) (simpleSymValToTerm v2))) ∪
                 bVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (FFTerm.mul (simpleSymValToTerm v1) (simpleSymValToTerm v2)))) →
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
            have hffeval : assignment'.ff sconf.nextVarId = val1' * val2' := by
              simp [hassignment'_def]
            refine ⟨assignment', hagreeff, hagreebool, hframeff, hframebool, ?_,
              EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagreeff hmatch,
              ?_⟩
            · simp [evalFormula, evalTerm, hevalTerm1', hevalTerm2', hffeval]
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
            simp only [evalFormula, evalTerm, hevalTerm1', hevalTerm2', Except.ok.injEq] at heval_f
            have hffeq : assignment'.ff sconf.nextVarId = val1' * val2' :=
              (beq_iff_eq ..).mp heval_f
            refine ⟨val1' * val2', ?_, hmatch', ?_⟩
            · simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval1', hval2',
                evalMul]
            · simp only [simpleValMatches, hffeq]

/-- `seExprDiv` resolves both operands' symbolic values `v1`/`v2`, then mints one fresh var tied
    to them via the "safe division" formula `if v2 = 0 then false else outVar * v2 = v1` --
    unlike `seExprAdd_correct`/etc, the tie-back formula isn't a plain `.eq`, it branches on
    whether `v2` is zero, exactly mirroring `evalDiv`'s own `if v2 = 0 then error else ok (v1/v2)`
    behavior (see `Language/Core/Semantics/Basic.lean`). Soundness/completeness both case on
    `v2 = 0`: when it holds, the formula is `FFFormula.false` (never satisfiable, matching
    `evalDiv`'s error, so soundness's premise -- a concrete success -- never arises, and
    completeness's premise -- a satisfying assignment -- never arises either); when it doesn't,
    the formula is the same `outVar * v2 = v1` tie-back as `seExprMul_correct`'s shape, discharged
    via the field facts `div_mul_cancel₀`/`eq_div_iff` (available since `ZMod c.p` is a `Field`,
    `c.p` being prime). -/
theorem seExprDiv_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD) (e1 e2 : SimpleExpr c) :
    TranslatesExprCorrectly gconf sconf specs ctx
      (fun env => Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env
        (Expr.bop BinOp.div e1 e2))
      (fun symEnv => seExprDiv md gconf sconf symEnv specs e1 e2) := by
  intro symEnv hbelow _hvalid espec hspec_eq
  simp only [seExprDiv] at hspec_eq
  cases hres1 : resolveSimpleExpr symEnv e1 with
  | error msg => rw [hres1] at hspec_eq; simp at hspec_eq
  | ok v1 =>
      rw [hres1] at hspec_eq
      cases hres2 : resolveSimpleExpr symEnv e2 with
      | error msg => rw [hres2] at hspec_eq; simp at hspec_eq
      | ok v2 =>
          rw [hres2] at hspec_eq
          injection hspec_eq with hspec_eq
          subst hspec_eq
          have hsub1 := Corellzk2smt.SymExec.Correctness.Lemmas.resolveSimpleExpr_vars_subset
            symEnv e1 v1 hres1
          have hsub2 := Corellzk2smt.SymExec.Correctness.Lemmas.resolveSimpleExpr_vars_subset
            symEnv e2 v2 hres2
          have hmemF : Var.ffv sconf.nextVarId ∈
              ffVarsOfFormula (FFFormula.ite
                (FFFormula.eq (simpleSymValToTerm v2) (FFTerm.val 0)) FFFormula.false
                (FFFormula.eq (FFTerm.mul (FFTerm.var sconf.nextVarId) (simpleSymValToTerm v2))
                  (simpleSymValToTerm v1))) := by
            simp only [ffVarsOfFormula, ffVarsOfTerm, ffVarsOfTerm_simpleSymValToTerm,
              Std.TreeSet.mem_union_iff]
            exact Or.inr (Or.inl (Or.inl (Std.TreeSet.mem_insert_self ..)))
          have hffdisj : ∀ v', v' ∈
              ffVarsOfFormula (FFFormula.ite
                (FFFormula.eq (simpleSymValToTerm v2) (FFTerm.val 0)) FFFormula.false
                (FFFormula.eq (FFTerm.mul (FFTerm.var sconf.nextVarId) (simpleSymValToTerm v2))
                  (simpleSymValToTerm v1))) →
              v' = Var.ffv sconf.nextVarId ∨ v' ∈ simpleValOwnVars v1 ∨
                v' ∈ simpleValOwnVars v2 := by
            intro v' hv'
            simp only [ffVarsOfFormula, ffVarsOfTerm, ffVarsOfTerm_simpleSymValToTerm,
              Std.TreeSet.mem_union_iff] at hv'
            rcases hv' with (((h | h) | h) | ((h | h) | h))
            · exact Or.inr (Or.inr h)
            · exact absurd h Std.TreeSet.not_mem_emptyc
            · exact absurd h Std.TreeSet.not_mem_emptyc
            · rcases Std.TreeSet.mem_insert.mp h with heq | hmem
              · exact Or.inl (Var_compare_eq_iff_eq.mp heq).symm
              · exact absurd hmem Std.TreeSet.not_mem_emptyc
            · exact Or.inr (Or.inr h)
            · exact Or.inr (Or.inl h)
          have hbdisj : ∀ v', v' ∈
              bVarsOfFormula (FFFormula.ite
                (FFFormula.eq (simpleSymValToTerm v2) (FFTerm.val 0)) FFFormula.false
                (FFFormula.eq (FFTerm.mul (FFTerm.var sconf.nextVarId) (simpleSymValToTerm v2))
                  (simpleSymValToTerm v1))) → False := by
            intro v' hv'
            simp only [bVarsOfFormula, bVarsOfTerm, bVarsOfTerm_simpleSymValToTerm,
              Std.TreeSet.mem_union_iff] at hv'
            rcases hv' with (((h | h) | h) | ((h | h) | h)) <;>
              exact absurd h Std.TreeSet.not_mem_emptyc
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
            rcases Std.TreeSet.mem_union_iff.mp hv' with hff | hb
            · rcases hffdisj v' hff with heq | h | h
              · rw [heq]; exact Or.inr (le_refl _)
              · exact Or.inl (hsub1 v' (simpleValOwnVars_subset_simpleValVars v1 v' h))
              · exact Or.inl (hsub2 v' (simpleValOwnVars_subset_simpleValVars v2 v' h))
            · exact absurd (hbdisj v' hb) (fun h => h)
          · intro v' hv'
            simp only [exprSpecVars] at hv'
            rcases Std.TreeSet.mem_union_iff.mp hv' with hff | hb
            · rcases hffdisj v' hff with heq | h | h
              · rw [heq]; simp only [varIndex]; omega
              · exact lt_of_lt_of_le
                  (hbelow v' (hsub1 v' (simpleValOwnVars_subset_simpleValVars v1 v' h)))
                  (Nat.le_succ _)
              · exact lt_of_lt_of_le
                  (hbelow v' (hsub2 v' (simpleValOwnVars_subset_simpleValVars v2 v' h)))
                  (Nat.le_succ _)
            · exact absurd (hbdisj v' hb) (fun h => h)
          · intro env assignment hmatch val hval
            obtain ⟨val1', hval1', hm1⟩ :=
              resolveSimpleExpr_correct symEnv e1 env assignment v1 hmatch hres1
            obtain ⟨val2', hval2', hm2⟩ :=
              resolveSimpleExpr_correct symEnv e2 env assignment v2 hmatch hres2
            simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval1', hval2',
              evalDiv] at hval
            by_cases hz : val2' = 0
            · simp [hz] at hval
            · simp only [hz, if_false] at hval
              injection hval with hval
              set assignment' : Assignment c :=
                { assignment with
                  ff := fun n => if n = sconf.nextVarId then val1' / val2' else assignment.ff n }
                with hassignment'_def
              have hagreeff : agreesOnFF (symEnvVars symEnv) assignment assignment' := by
                intro n hn
                have hne : n ≠ sconf.nextVarId := Nat.ne_of_lt (hbelow (Var.ffv n) hn)
                simp only [hassignment'_def, if_neg hne]
              have hagreebool : agreesOnBool (symEnvVars symEnv) assignment assignment' :=
                fun n _ => rfl
              have hframeff : ∀ n, Var.ffv n ∉
                  (ffVarsOfFormula (FFFormula.ite
                      (FFFormula.eq (simpleSymValToTerm v2) (FFTerm.val 0)) FFFormula.false
                      (FFFormula.eq (FFTerm.mul (FFTerm.var sconf.nextVarId)
                        (simpleSymValToTerm v2)) (simpleSymValToTerm v1))) ∪
                   bVarsOfFormula (FFFormula.ite
                      (FFFormula.eq (simpleSymValToTerm v2) (FFTerm.val 0)) FFFormula.false
                      (FFFormula.eq (FFTerm.mul (FFTerm.var sconf.nextVarId)
                        (simpleSymValToTerm v2)) (simpleSymValToTerm v1)))) →
                  assignment'.ff n = assignment.ff n := by
                intro n hn
                have hne : n ≠ sconf.nextVarId := by
                  intro heqn
                  apply hn
                  rw [heqn]
                  exact Std.TreeSet.mem_union_of_left hmemF
                simp only [hassignment'_def, if_neg hne]
              have hframebool : ∀ n, Var.boolv n ∉
                  (ffVarsOfFormula (FFFormula.ite
                      (FFFormula.eq (simpleSymValToTerm v2) (FFTerm.val 0)) FFFormula.false
                      (FFFormula.eq (FFTerm.mul (FFTerm.var sconf.nextVarId)
                        (simpleSymValToTerm v2)) (simpleSymValToTerm v1))) ∪
                   bVarsOfFormula (FFFormula.ite
                      (FFFormula.eq (simpleSymValToTerm v2) (FFTerm.val 0)) FFFormula.false
                      (FFFormula.eq (FFTerm.mul (FFTerm.var sconf.nextVarId)
                        (simpleSymValToTerm v2)) (simpleSymValToTerm v1)))) →
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
              have hffeval : assignment'.ff sconf.nextVarId = val1' / val2' := by
                simp [hassignment'_def]
              refine ⟨assignment', hagreeff, hagreebool, hframeff, hframebool, ?_,
                EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagreeff hmatch,
                ?_⟩
              · simp only [evalFormula, evalTerm, hevalTerm2', hz, if_false, beq_iff_eq,
                  hevalTerm1', hffeval, Except.ok.injEq]
                exact div_mul_cancel₀ val1' hz
              · simp only [simpleValMatches, hffeval]
                exact hval
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
            by_cases hz : val2' = 0
            · exfalso
              simp [evalFormula, evalTerm, hevalTerm2', hz] at heval_f
            · simp only [evalFormula, evalTerm, hevalTerm2', hz, if_false, beq_iff_eq,
                hevalTerm1', Except.ok.injEq] at heval_f
              have hffeq : assignment'.ff sconf.nextVarId = val1' / val2' :=
                (eq_div_iff hz).mpr heval_f
              refine ⟨val1' / val2', ?_, hmatch', ?_⟩
              · simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval1', hval2',
                  evalDiv, hz, if_false]
              · simp only [simpleValMatches, hffeq]

/-- `evalTerm` distributes over `ffTermPow`: evaluating `t`'s `n`-fold term-level product gives
    the field power of whatever `t` itself evaluates to. Proved by plain induction on `n`,
    matching `ffTermPow`'s own recursion exactly. -/
theorem ffTermPow_correct {c : ZKConfig} (gconf : GlobalConfig c) (assignment : Assignment c)
    (ms : List (FFMacro c)) (t : FFTerm c) (v : FF c)
    (ht : evalTerm gconf assignment t ms = Except.ok v) (n : Nat) :
    evalTerm gconf assignment (ffTermPow t n) ms = Except.ok (v ^ n) := by
  induction n with
  | zero => simp [ffTermPow, evalTerm]
  | succ n ih => simp [ffTermPow, evalTerm, ht, ih, pow_succ']

/-- `ffTermPow t n` only ever mentions vars that `t` itself does -- it's built purely out of `n`
    copies of `t` chained by `.mul`, never anything else. -/
theorem ffVarsOfTerm_ffTermPow_subset {c : ZKConfig} (t : FFTerm c) (n : Nat) :
    ffVarsOfTerm (ffTermPow t n) ⊆ ffVarsOfTerm t := by
  induction n with
  | zero =>
      intro v hv
      simp only [ffTermPow, ffVarsOfTerm] at hv
      exact absurd hv Std.TreeSet.not_mem_emptyc
  | succ n ih =>
      intro v hv
      simp only [ffTermPow, ffVarsOfTerm, Std.TreeSet.mem_union_iff] at hv
      rcases hv with h | h
      · exact h
      · exact ih v h

/-- Mirror of `ffVarsOfTerm_ffTermPow_subset`, for `bVarsOfTerm`. -/
theorem bVarsOfTerm_ffTermPow_subset {c : ZKConfig} (t : FFTerm c) (n : Nat) :
    bVarsOfTerm (ffTermPow t n) ⊆ bVarsOfTerm t := by
  induction n with
  | zero =>
      intro v hv
      simp only [ffTermPow, bVarsOfTerm] at hv
      exact absurd hv Std.TreeSet.not_mem_emptyc
  | succ n ih =>
      intro v hv
      simp only [ffTermPow, bVarsOfTerm, Std.TreeSet.mem_union_iff] at hv
      rcases hv with h | h
      · exact h
      · exact ih v h

/-- `seExprPowWithConstantExponent` resolves the base's symbolic value `base` and fully
    constant-folds the exponent to `power` (via `tryEvalSimpleExprToFFValue`, never touching a
    live variable), then mints one fresh var tied to `base`'s `power.val`-fold term product via
    `ffTermPow`. Since `power` is fully determined by `symEnv` alone, it evaluates to the exact
    same concrete value under *every* env/assignment matching `symEnv`
    (`tryEvalSimpleExprToFFValue_correct`) -- so unlike `seExprDiv_correct`, there's no case split
    here, just `ffTermPow_correct` bridging the term-level product to the field power `evalPow`
    itself computes. -/
theorem seExprPowWithConstantExponent_correct {c : ZKConfig} (gconf : GlobalConfig c)
    (specs : List (FuncSpec c)) (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD)
    (e1 e2 : SimpleExpr c) :
    TranslatesExprCorrectly gconf sconf specs ctx
      (fun env => Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env
        (Expr.bop BinOp.pow e1 e2))
      (fun symEnv => seExprPowWithConstantExponent md gconf sconf symEnv specs e1 e2) := by
  intro symEnv hbelow _hvalid espec hspec_eq
  simp only [seExprPowWithConstantExponent] at hspec_eq
  cases hpow : tryEvalSimpleExprToFFValue symEnv e2 with
  | error msg => rw [hpow] at hspec_eq; simp at hspec_eq
  | ok power =>
      rw [hpow] at hspec_eq
      cases hres1 : resolveSimpleExpr symEnv e1 with
      | error msg => rw [hres1] at hspec_eq; simp at hspec_eq
      | ok base =>
          rw [hres1] at hspec_eq
          injection hspec_eq with hspec_eq
          subst hspec_eq
          have hsub1 := Corellzk2smt.SymExec.Correctness.Lemmas.resolveSimpleExpr_vars_subset
            symEnv e1 base hres1
          have hpowsub : ffVarsOfTerm (ffTermPow (simpleSymValToTerm base) power.val) ⊆
              simpleValOwnVars base := by
            rw [← ffVarsOfTerm_simpleSymValToTerm base]
            exact ffVarsOfTerm_ffTermPow_subset (simpleSymValToTerm base) power.val
          have hpowsubB : bVarsOfTerm (ffTermPow (simpleSymValToTerm base) power.val) ⊆
              (emptyVarSet : VarSet) := by
            rw [← bVarsOfTerm_simpleSymValToTerm base]
            exact bVarsOfTerm_ffTermPow_subset (simpleSymValToTerm base) power.val
          have hmemF : Var.ffv sconf.nextVarId ∈
              ffVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
                (ffTermPow (simpleSymValToTerm base) power.val)) := by
            simp only [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_union_iff]
            exact Or.inl (Std.TreeSet.mem_insert_self ..)
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
            rcases Std.TreeSet.mem_union_iff.mp hv' with hff | hb
            · simp only [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_union_iff] at hff
              rcases hff with h1 | h2
              · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
                · rw [← Var_compare_eq_iff_eq.mp heq]
                  exact Or.inr (le_refl _)
                · exact absurd hmem Std.TreeSet.not_mem_emptyc
              · exact Or.inl (hsub1 v' (simpleValOwnVars_subset_simpleValVars base v'
                  (hpowsub v' h2)))
            · simp only [bVarsOfFormula, bVarsOfTerm, Std.TreeSet.mem_union_iff] at hb
              rcases hb with h1 | h2
              · exact absurd h1 Std.TreeSet.not_mem_emptyc
              · exact absurd (hpowsubB v' h2) Std.TreeSet.not_mem_emptyc
          · intro v' hv'
            simp only [exprSpecVars] at hv'
            rcases Std.TreeSet.mem_union_iff.mp hv' with hff | hb
            · simp only [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_union_iff] at hff
              rcases hff with h1 | h2
              · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
                · rw [← Var_compare_eq_iff_eq.mp heq]
                  simp only [varIndex]
                  omega
                · exact absurd hmem Std.TreeSet.not_mem_emptyc
              · exact lt_of_lt_of_le
                  (hbelow v' (hsub1 v' (simpleValOwnVars_subset_simpleValVars base v'
                    (hpowsub v' h2))))
                  (Nat.le_succ _)
            · simp only [bVarsOfFormula, bVarsOfTerm, Std.TreeSet.mem_union_iff] at hb
              rcases hb with h1 | h2
              · exact absurd h1 Std.TreeSet.not_mem_emptyc
              · exact absurd (hpowsubB v' h2) Std.TreeSet.not_mem_emptyc
          · intro env assignment hmatch val hval
            have hval2 := tryEvalSimpleExprToFFValue_correct symEnv e2 env assignment power
              hmatch hpow
            obtain ⟨val1, hval1, hm1⟩ :=
              resolveSimpleExpr_correct symEnv e1 env assignment base hmatch hres1
            simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval1, hval2,
              evalPow] at hval
            injection hval with hval
            subst hval
            set assignment' : Assignment c :=
              { assignment with
                ff := fun n => if n = sconf.nextVarId then val1 ^ power.val else assignment.ff n }
              with hassignment'_def
            have hagreeff : agreesOnFF (symEnvVars symEnv) assignment assignment' := by
              intro n hn
              have hne : n ≠ sconf.nextVarId := Nat.ne_of_lt (hbelow (Var.ffv n) hn)
              simp only [hassignment'_def, if_neg hne]
            have hagreebool : agreesOnBool (symEnvVars symEnv) assignment assignment' :=
              fun n _ => rfl
            have hframeff : ∀ n, Var.ffv n ∉
                (ffVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (ffTermPow (simpleSymValToTerm base) power.val)) ∪
                 bVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (ffTermPow (simpleSymValToTerm base) power.val))) →
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
                  (ffTermPow (simpleSymValToTerm base) power.val)) ∪
                 bVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
                  (ffTermPow (simpleSymValToTerm base) power.val))) →
                assignment'.bool n = assignment.bool n := fun n _ => rfl
            have hsimpleMatch1' : simpleValMatches assignment' base val1 :=
              simpleValMatches_agreesOnFF_preserves assignment assignment' base val1
                (symEnvVars symEnv) hsub1 hagreeff hm1
            have hevalTerm1' : evalTerm gconf assignment' (simpleSymValToTerm base)
                (specs.map (·.f)) = Except.ok val1 :=
              evalTerm_simpleSymValToTerm gconf assignment' base val1 (specs.map (·.f))
                hsimpleMatch1'
            have hevalPow' : evalTerm gconf assignment'
                (ffTermPow (simpleSymValToTerm base) power.val) (specs.map (·.f))
                = Except.ok (val1 ^ power.val) :=
              ffTermPow_correct gconf assignment' (specs.map (·.f)) (simpleSymValToTerm base)
                val1 hevalTerm1' power.val
            have hffeval : assignment'.ff sconf.nextVarId = val1 ^ power.val := by
              simp [hassignment'_def]
            refine ⟨assignment', hagreeff, hagreebool, hframeff, hframebool, ?_,
              EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagreeff hmatch,
              ?_⟩
            · simp [evalFormula, evalTerm, hevalPow', hffeval]
            · simp only [simpleValMatches, hffeval]
          · intro env assignment hmatch assignment' hagree heval_f
            have hmatch' : EnvMatches assignment' symEnv env :=
              EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagree hmatch
            have hval2 := tryEvalSimpleExprToFFValue_correct symEnv e2 env assignment' power
              hmatch' hpow
            obtain ⟨val1, hval1, hm1'⟩ :=
              resolveSimpleExpr_correct symEnv e1 env assignment' base hmatch' hres1
            have hevalTerm1' : evalTerm gconf assignment' (simpleSymValToTerm base)
                (specs.map (·.f)) = Except.ok val1 :=
              evalTerm_simpleSymValToTerm gconf assignment' base val1 (specs.map (·.f)) hm1'
            have hevalPow' : evalTerm gconf assignment'
                (ffTermPow (simpleSymValToTerm base) power.val) (specs.map (·.f))
                = Except.ok (val1 ^ power.val) :=
              ffTermPow_correct gconf assignment' (specs.map (·.f)) (simpleSymValToTerm base)
                val1 hevalTerm1' power.val
            simp only [evalFormula, evalTerm, hevalPow', Except.ok.injEq, beq_iff_eq] at heval_f
            refine ⟨val1 ^ power.val, ?_, hmatch', ?_⟩
            · simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval1, hval2,
                evalPow]
            · simp only [simpleValMatches]
              exact heval_f

/-- `seExprPow` dispatch: it tries `seExprPowWithConstantExponent` first and only falls back to
    `seExprPowWithNonConstantExponent` (a permanent stub) on error, so its success cases coincide
    exactly with the constant-exponent path's own. -/
theorem seExprPow_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD) (e1 e2 : SimpleExpr c) :
    TranslatesExprCorrectly gconf sconf specs ctx
      (fun env => Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env
        (Expr.bop BinOp.pow e1 e2))
      (fun symEnv => seExprPow md gconf sconf symEnv specs e1 e2) := by
  intro symEnv hbelow hvalid espec hspec_eq
  simp only [seExprPow] at hspec_eq
  cases hconst : seExprPowWithConstantExponent md gconf sconf symEnv specs e1 e2 with
  | ok result =>
      rw [hconst] at hspec_eq
      injection hspec_eq with hspec_eq
      subst hspec_eq
      exact seExprPowWithConstantExponent_correct gconf specs sconf ctx md e1 e2 symEnv hbelow
        hvalid result hconst
  | error msg =>
      rw [hconst] at hspec_eq
      simp [seExprPowWithNonConstantExponent] at hspec_eq

-- ---------------------------------------------------------------------------
-- `.uidiv`'s constant-divisor gadget: the plain-Nat arithmetic behind it
-- ---------------------------------------------------------------------------
--
-- `uiDivModGadget` splits the dividend `A` into two halves at `midpoint` and uses a differently
-- sized `Q`-range per half (`[0, (midpoint-1)/B]` low, `[midpoint/B, (p-1)/B]` high). A single
-- bound covering the *whole* field can't be both sound (every real quotient must fit) and
-- complete (no other `(Q,R)` may also satisfy the equation, i.e. no wraparound mod `p`) --
-- splitting at `midpoint` is what makes each half individually small enough relative to `p` to
-- get both. The two lemmas below are the crux of that argument, in plain `Nat` terms, before any
-- field/`FFFormula` machinery gets involved.

/-- Under the divisor bounds `.uidiv`'s gadget requires (`2 ≤ B < midpoint`), `p` is forced odd,
    giving the exact relationship between `p` and its own signed/positive split point that both
    bounds below rely on. (`p = 2` would force `midpoint = 2`, contradicting `2 ≤ B < midpoint`.) -/
theorem two_mul_midpoint_eq {c : ZKConfig} (B : Nat) (hB2 : 2 ≤ B) (hBmid : B < c.midpoint) :
    2 * c.midpoint = c.p + 1 := by
  have hmid := c.midpoint_ok
  rcases c.p_prime.eq_two_or_odd with h2 | hodd
  · omega
  · omega

/-- The low half never wraps: the largest possible `Q·B+R` (at `Q`'s own bound) stays strictly
    below `p`, so the tie-back equation can never be satisfied by anything other than the true
    quotient/remainder of a dividend in the low half. -/
theorem uidiv_low_no_wrap {c : ZKConfig} (B : Nat) (hB2 : 2 ≤ B) (hBmid : B < c.midpoint) :
    (c.midpoint - 1) / B * B + (B - 1) < c.p := by
  have h2mid := two_mul_midpoint_eq B hB2 hBmid
  have hle := Nat.div_mul_le_self (c.midpoint - 1) B
  omega

/-- The high half never wraps *relative to any dividend `A` in that half* (`A ≥ midpoint`): the
    largest possible `Q·B+R` stays strictly below `A + p`, so the tie-back equation can never be
    satisfied by the "wrapped" value `A + p` -- only `A` itself. -/
theorem uidiv_high_no_wrap {c : ZKConfig} (B : Nat) (hB2 : 2 ≤ B) (hBmid : B < c.midpoint) :
    (c.p - 1) / B * B + (B - 1) < c.midpoint + c.p := by
  have hle := Nat.div_mul_le_self (c.p - 1) B
  omega

/-- The low branch's own `Q`-bound (`uLo = (midpoint-1)/B`) is itself below `midpoint` -- needed so
    `toSigned` can read it back as a plain `Nat.cast` (via `toSigned_natCast_of_lt`). Proved via
    `Nat.div_le_self` rather than `omega` alone: `omega` tends to choke once several unrelated
    `_/B*B`-shaped opaque products (from `uidiv_low_no_wrap`/`uidiv_high_no_wrap`) are in context
    alongside a *fresh* division atom it has no direct linear handle on. -/
theorem uidiv_qLow_bound {c : ZKConfig} (B : Nat) (hB2 : 2 ≤ B) (hBmid : B < c.midpoint) :
    (c.midpoint - 1) / B < c.midpoint := by
  have h := Nat.div_le_self (c.midpoint - 1) B
  omega

/-- The high branch's own `Q`-lower-bound (`lo = midpoint/B`) is itself below `midpoint` -- same
    role as `uidiv_qLow_bound`, for the other endpoint. -/
theorem uidiv_qHighLo_bound {c : ZKConfig} (B : Nat) (hB2 : 2 ≤ B) (hBmid : B < c.midpoint) :
    c.midpoint / B < c.midpoint := by
  exact Nat.div_lt_self (by omega) (by omega)

/-- The high branch's own `Q`-upper-bound (`hi = (p-1)/B`) is itself below `midpoint` -- the key
    fact making the two-branch split sound (see the module-level discussion of why `B < midpoint`
    is exactly the slack needed). Proved by first halving: since `B ≥ 2`, `(p-1)/B ≤ (p-1)/2`,
    and `(p-1)/2` is *exactly* `midpoint - 1` (from `two_mul_midpoint_eq`, no remainder). -/
theorem uidiv_qHighHi_bound {c : ZKConfig} (B : Nat) (hB2 : 2 ≤ B) (hBmid : B < c.midpoint) :
    (c.p - 1) / B < c.midpoint := by
  have h2mid := two_mul_midpoint_eq B hB2 hBmid
  have hle : (c.p - 1) / B ≤ (c.p - 1) / 2 := Nat.div_le_div_left hB2 (by norm_num)
  omega

/-- Given `Q·B+R = A` (a genuine, non-wrapped Nat equation) and `R < B`, `Q`/`R` are forced to be
    the real quotient/remainder of `A` by `B` -- restates `Nat.div_mod_unique` with the operand
    order `uiDivModGadget`'s own equation uses. -/
theorem nat_eq_div_mod_of_eq {A B Q R : Nat} (hB : 0 < B) (heq : Q * B + R = A) (hR : R < B) :
    A / B = Q ∧ A % B = R := by
  rw [Nat.div_mod_unique hB]
  refine ⟨?_, hR⟩
  rw [Nat.mul_comm B Q]
  omega

-- ---------------------------------------------------------------------------
-- `.uidiv`'s constant-divisor gadget: bridging the `Nat` facts above to `FFFormula`/`toSigned`
-- ---------------------------------------------------------------------------

/-- `(n : FF c) - 1`, for `n ≥ 1`, is the same value as casting the `Nat` subtraction `n - 1`
    directly -- lets the `toSigned`/`.val` reasoning below work uniformly on plain `Nat.cast`s,
    regardless of whether the source literal was written as a field subtraction (as `rRange`'s and
    `isLow`'s own upper bounds are, since they're spelled `(_ - 1 : FF c)` inline) or a Nat one
    computed ahead of time (as `uLo`/`lo`/`hi` are). -/
theorem cast_sub_one_eq {c : ZKConfig} (n : Nat) (h : 1 ≤ n) :
    ((n : FF c) - 1) = ((n - 1 : Nat) : FF c) := by
  have heq : (n - 1 : Nat) + 1 = n := Nat.sub_add_cancel h
  have hcast : ((n - 1 : Nat) : FF c) + 1 = (n : FF c) := by
    conv_rhs => rw [← heq]
    push_cast
    ring
  exact (eq_sub_of_add_eq hcast).symm

/-- The `.val` of a literal Nat cast into the field is just that Nat, reduced mod `p` -- restates
    `ZMod.val_natCast`. -/
theorem val_natCast_eq {c : ZKConfig} (n : Nat) : ((n : Nat) : FF c).val = n % c.p :=
  ZMod.val_natCast (n := c.p) n

/-- `toSigned` is the identity (as an integer) on any FF value already known to be "positive"
    (below `midpoint`) -- the signed/unsigned split only matters once `.val` reaches the upper
    half. -/
theorem toSigned_of_val_lt_midpoint {c : ZKConfig} (x : FF c) (h : x.val < c.midpoint) :
    toSigned x = (x.val : Int) := by
  simp only [Corellzk2smt.Language.Core.Semantics.Basic.toSigned, h, if_true]

/-- The signed value of a small literal Nat cast into the field is just the literal itself. -/
theorem toSigned_natCast_of_lt {c : ZKConfig} (n : Nat) (hp : n < c.p) (hmid : n < c.midpoint) :
    toSigned ((n : Nat) : FF c) = (n : Int) := by
  have hval : ((n : Nat) : FF c).val = n := by
    rw [val_natCast_eq]; exact Nat.mod_eq_of_lt hp
  have hval_lt : ((n : Nat) : FF c).val < c.midpoint := by rw [hval]; exact hmid
  rw [toSigned_of_val_lt_midpoint _ hval_lt, hval]

/-- `evalFormula` on a `.range` node reduces to a plain pair of `toSigned` inequalities once the
    term underneath evaluates -- `evalLe`'s own `if`-based definition unwound. -/
theorem evalFormula_range_iff {c : ZKConfig} (gconf : GlobalConfig c) (assignment : Assignment c)
    (ms : List (FFMacro c)) (t : FFTerm c) (l u v : FF c)
    (ht : evalTerm gconf assignment t ms = Except.ok v) :
    evalFormula gconf assignment (FFFormula.range t l u) ms = Except.ok true ↔
      toSigned l ≤ toSigned v ∧ toSigned v ≤ toSigned u := by
  simp only [evalFormula, ht, Corellzk2smt.Language.Core.Semantics.Basic.evalLe]
  by_cases h1 : toSigned l ≤ toSigned v <;> by_cases h2 : toSigned v ≤ toSigned u <;>
    simp [h1, h2]

/-- The field-level image of `Nat.div_add_mod`: casting `m`'s quotient/remainder by `n` back into
    the field and recombining them (`(m/n)*n + m%n`) gives back `m` itself -- bridges the plain
    `Nat` division identity into the exact shape `.uidiv`'s tie-back equation needs. -/
theorem cast_div_add_mod_eq {c : ZKConfig} (m n : Nat) :
    ((m / n : Nat) : FF c) * ((n : Nat) : FF c) + ((m % n : Nat) : FF c) = ((m : Nat) : FF c) := by
  have hdm : (m / n) * n + m % n = m := Nat.div_add_mod' m n
  calc ((m / n : Nat) : FF c) * ((n : Nat) : FF c) + ((m % n : Nat) : FF c)
      = (((m / n) * n + m % n : Nat) : FF c) := by push_cast; ring
    _ = ((m : Nat) : FF c) := by rw [hdm]

/-- `cast_div_add_mod_eq`, multiplying by the field element `Bv` itself instead of a fresh cast
    of its own `.val` -- the shape `.uidiv`'s tie-back equation actually needs, since the gadget's
    formula multiplies by the divisor's own symbolic value, not a re-cast of it. Isolating the
    `Bv = ((Bv.val : Nat) : FF c)` rewrite to a one-line `congrArg` (rather than a blanket `rw`)
    avoids corrupting the *other*, unrelated occurrences of `Bv` buried inside `m / Bv.val`/
    `m % Bv.val`'s own `.val` computations. -/
theorem cast_div_add_mod_eq' {c : ZKConfig} (m : Nat) (Bv : FF c) :
    ((m / Bv.val : Nat) : FF c) * Bv + ((m % Bv.val : Nat) : FF c) = ((m : Nat) : FF c) := by
  have hstep : ((m / Bv.val : Nat) : FF c) * Bv
      = ((m / Bv.val : Nat) : FF c) * ((Bv.val : Nat) : FF c) :=
    congrArg (((m / Bv.val : Nat) : FF c) * ·) (ZMod.natCast_rightInverse Bv).symm
  rw [hstep, cast_div_add_mod_eq m Bv.val]

/-- `evalFormula` on a `.and` node reduces to a plain pair once both sides evaluate -- the
    `evalFormula_range_iff`-style unwinding, but for conjunction instead of `.range`. -/
theorem evalFormula_and_elim {c : ZKConfig} (gconf : GlobalConfig c) (assignment : Assignment c)
    (ms : List (FFMacro c)) (a b : FFFormula c)
    (hab : evalFormula gconf assignment (FFFormula.and a b) ms = Except.ok true) :
    evalFormula gconf assignment a ms = Except.ok true ∧
      evalFormula gconf assignment b ms = Except.ok true := by
  cases ha : evalFormula gconf assignment a ms with
  | error msg => simp [evalFormula, ha] at hab
  | ok va =>
      cases hb : evalFormula gconf assignment b ms with
      | error msg => simp [evalFormula, ha, hb] at hab
      | ok vb =>
          simp only [evalFormula, ha, hb] at hab
          injection hab with hab
          rw [Bool.and_eq_true] at hab
          exact ⟨congrArg Except.ok hab.1, congrArg Except.ok hab.2⟩

/-- `evalFormula` on a `.eq` node reduces to plain equality of the two terms' values, once both
    evaluate. -/
theorem evalFormula_eq_iff {c : ZKConfig} (gconf : GlobalConfig c) (assignment : Assignment c)
    (ms : List (FFMacro c)) (a b : FFTerm c) (va vb : FF c)
    (ha : evalTerm gconf assignment a ms = Except.ok va)
    (hb : evalTerm gconf assignment b ms = Except.ok vb) :
    evalFormula gconf assignment (FFFormula.eq a b) ms = Except.ok true ↔ va = vb := by
  simp only [evalFormula, ha, hb, Except.ok.injEq, beq_iff_eq]

/-- Building `evalFormula`'s `.and` node from two already-`true` sides -- the introduction-form
    counterpart of `evalFormula_and_elim`. -/
theorem evalFormula_and_intro {c : ZKConfig} (gconf : GlobalConfig c) (assignment : Assignment c)
    (ms : List (FFMacro c)) (a b : FFFormula c)
    (ha : evalFormula gconf assignment a ms = Except.ok true)
    (hb : evalFormula gconf assignment b ms = Except.ok true) :
    evalFormula gconf assignment (FFFormula.and a b) ms = Except.ok true := by
  simp [evalFormula, ha, hb]

/-- Building `evalFormula`'s `.ite` node when the condition is `true` -- picks the `then` branch,
    which just needs to itself already be `true`. -/
theorem evalFormula_ite_true {c : ZKConfig} (gconf : GlobalConfig c) (assignment : Assignment c)
    (ms : List (FFMacro c)) (cnd t e : FFFormula c)
    (hc : evalFormula gconf assignment cnd ms = Except.ok true)
    (ht : evalFormula gconf assignment t ms = Except.ok true) :
    evalFormula gconf assignment (FFFormula.ite cnd t e) ms = Except.ok true := by
  simp [evalFormula, hc, ht]

/-- `evalFormula_ite_true`'s `false`-condition counterpart -- picks the `else` branch. -/
theorem evalFormula_ite_false {c : ZKConfig} (gconf : GlobalConfig c) (assignment : Assignment c)
    (ms : List (FFMacro c)) (cnd t e : FFFormula c)
    (hc : evalFormula gconf assignment cnd ms = Except.ok false)
    (he : evalFormula gconf assignment e ms = Except.ok true) :
    evalFormula gconf assignment (FFFormula.ite cnd t e) ms = Except.ok true := by
  simp [evalFormula, hc, he]

/-- Plain `Nat` fact: reducing the left summand mod `n` first doesn't change the sum's own
    residue mod `n`. -/
theorem nat_mod_add_mod (a b n : Nat) : (a % n + b) % n = (a + b) % n := by
  rw [Nat.add_mod (a % n) b n, Nat.mod_mod, ← Nat.add_mod]

/-- The completeness-direction counterpart of `cast_div_add_mod_eq`/`nat_eq_div_mod_of_eq`: given
    a satisfied field equation `A = Q*B+R`, `Q.val*B.val+R.val` known to stay below `2*c.p` (so it
    wraps around the field's modulus at most once), and a proof ruling out the "wrapped once" case
    (`hne`, discharged differently by the low/high branch -- the low branch's own bound already
    keeps the raw sum below `c.p` so `hne` is vacuous there, the high branch instead uses
    `A.val ≥ c.midpoint` to show the wrapped residue `sum - c.p` is too small to be `A.val`), the
    raw `Nat` sum equals `A.val` exactly -- letting `nat_eq_div_mod_of_eq` read off `Q`/`R` as the
    real quotient/remainder of `A.val` by `B.val`. -/
theorem QBR_val_eq_of_no_wrap {c : ZKConfig} (Q B R A : FF c) (heq : A = Q * B + R)
    (hlt2p : Q.val * B.val + R.val < 2 * c.p)
    (hne : c.p ≤ Q.val * B.val + R.val → A.val ≠ Q.val * B.val + R.val - c.p) :
    Q.val * B.val + R.val = A.val := by
  have hmodeq : A.val = (Q.val * B.val + R.val) % c.p := by
    rw [heq, ZMod.val_add, ZMod.val_mul, nat_mod_add_mod]
  by_cases hge : c.p ≤ Q.val * B.val + R.val
  · exfalso
    have hcancel : Q.val * B.val + R.val - c.p + c.p = Q.val * B.val + R.val :=
      Nat.sub_add_cancel hge
    have hmod2 : (Q.val * B.val + R.val) % c.p = (Q.val * B.val + R.val - c.p) % c.p := by
      conv_lhs => rw [← hcancel]
      exact Nat.add_mod_right _ _
    have hlt : Q.val * B.val + R.val - c.p < c.p := by omega
    rw [hmod2, Nat.mod_eq_of_lt hlt] at hmodeq
    exact hne hge hmodeq
  · push_neg at hge
    rw [Nat.mod_eq_of_lt hge] at hmodeq
    omega

/-- `seExprUIDivWithConstantDivisor`'s `B.val = 1` case: division by one is the
    identity, for *any* dividend -- no fresh variable, no formula content, structurally identical
    to `seExprId_correct`. -/
theorem seExprUIDivWithConstantDivisor_correct {c : ZKConfig} (gconf : GlobalConfig c)
    (specs : List (FuncSpec c)) (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD)
    (e1 e2 : SimpleExpr c) :
    TranslatesExprCorrectly gconf sconf specs ctx
      (fun env => Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env
        (Expr.bop BinOp.uidiv e1 e2))
      (fun symEnv =>
        seExprUIDivWithConstantDivisor md gconf sconf symEnv specs e1 e2) := by
  intro symEnv hbelow _hvalid espec hspec_eq
  simp only [seExprUIDivWithConstantDivisor] at hspec_eq
  cases hB : tryEvalSimpleExprToFFValue symEnv e2 with
  | error msg => rw [hB] at hspec_eq; simp at hspec_eq
  | ok B =>
    rw [hB] at hspec_eq
    simp only [] at hspec_eq
    by_cases hB1 : B.val = 1
    · rw [if_pos hB1] at hspec_eq
      cases hres1 : resolveSimpleExpr symEnv e1 with
      | error msg => rw [hres1] at hspec_eq; simp at hspec_eq
      | ok v =>
          rw [hres1] at hspec_eq
          injection hspec_eq with hspec_eq
          subst hspec_eq
          have hsub1 := Corellzk2smt.SymExec.Correctness.Lemmas.resolveSimpleExpr_vars_subset
            symEnv e1 v hres1
          have hBne0 : B ≠ (0 : FF c) := by
            intro hB0; rw [hB0] at hB1; simp at hB1
          refine ⟨le_refl _, fun v' hv' => Or.inl (hsub1 v' hv'), ?_, ?_, hbelow,
            fun v' hv' => Or.inl hv', ValidBinRep_trivial gconf _ _, ?_, ?_⟩
          · intro v' hv'
            rcases Std.TreeSet.mem_union_iff.mp hv' with h | h <;>
              simp only [ffVarsOfFormula, bVarsOfFormula] at h <;>
              exact absurd h Std.TreeSet.not_mem_emptyc
          · intro v' hv'
            rcases Std.TreeSet.mem_union_iff.mp hv' with h | h <;>
              simp only [ffVarsOfFormula, bVarsOfFormula] at h <;>
              exact absurd h Std.TreeSet.not_mem_emptyc
          · intro env assignment hmatch val hval
            obtain ⟨val', hval', hm⟩ :=
              resolveSimpleExpr_correct symEnv e1 env assignment v hmatch hres1
            have hB' := tryEvalSimpleExprToFFValue_correct symEnv e2 env assignment B hmatch hB
            have hround : ((val'.val : Nat) : FF c) = val' := ZMod.natCast_rightInverse val'
            simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval', hB',
              evalUidiv, if_neg hBne0, hB1, Nat.div_one, hround] at hval
            injection hval with hval
            subst hval
            exact ⟨assignment, (fun n _ => rfl), (fun n _ => rfl), (fun n _ => rfl),
              (fun n _ => rfl), by simp only [evalFormula], hmatch, hm⟩
          · intro env assignment hmatch assignment' hagree _heval
            obtain ⟨val, hval, hm⟩ :=
              resolveSimpleExpr_correct symEnv e1 env assignment v hmatch hres1
            have hB' := tryEvalSimpleExprToFFValue_correct symEnv e2 env assignment B hmatch hB
            have hround : ((val.val : Nat) : FF c) = val := ZMod.natCast_rightInverse val
            refine ⟨val, ?_, EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env
              hagree hmatch, simpleValMatches_agreesOnFF_preserves assignment assignment' v val
                (symEnvVars symEnv) hsub1 hagree hm⟩
            simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval, hB',
              evalUidiv, if_neg hBne0, hB1, Nat.div_one, hround]
    · rw [if_neg hB1] at hspec_eq
      by_cases hBrange : 1 < B.val ∧ B.val < c.midpoint
      · have hcond : (B.val > 1 && B.val < c.midpoint) = true := by
          simp only [Bool.and_eq_true, decide_eq_true_eq, gt_iff_lt]
          exact hBrange
        simp only [hcond, if_true] at hspec_eq
        cases hres1 : resolveSimpleExpr symEnv e1 with
        | error msg => rw [hres1] at hspec_eq; simp at hspec_eq
        | ok A =>
            rw [hres1] at hspec_eq
            simp only [uiDivModGadget] at hspec_eq
            injection hspec_eq with hspec_eq
            subst hspec_eq
            obtain ⟨hB2, hBmid⟩ := hBrange
            have hsubA := Corellzk2smt.SymExec.Correctness.Lemmas.resolveSimpleExpr_vars_subset
              symEnv e1 A hres1
            have hBne0 : B ≠ (0 : FF c) := by
              intro hB0; rw [hB0] at hB2; simp at hB2
            have h2mid := two_mul_midpoint_eq B.val hB2 hBmid
            have hlow_nowrap := uidiv_low_no_wrap B.val hB2 hBmid
            have hhigh_nowrap := uidiv_high_no_wrap B.val hB2 hBmid
            have hmemQeqn : Var.ffv sconf.nextVarId ∈
                ffVarsOfFormula (FFFormula.eq (simpleSymValToTerm A)
                  (FFTerm.add (FFTerm.mul (FFTerm.var sconf.nextVarId) (FFTerm.val B))
                    (FFTerm.var (sconf.nextVarId + 1)))) := by
              simp only [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_union_iff]
              exact Or.inr (Or.inl (Or.inl (Std.TreeSet.mem_insert_self ..)))
            have hmemReqn : Var.ffv (sconf.nextVarId + 1) ∈
                ffVarsOfFormula (FFFormula.eq (simpleSymValToTerm A)
                  (FFTerm.add (FFTerm.mul (FFTerm.var sconf.nextVarId) (FFTerm.val B))
                    (FFTerm.var (sconf.nextVarId + 1)))) := by
              simp only [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_union_iff]
              exact Or.inr (Or.inr (Std.TreeSet.mem_insert_self ..))
            have hffdisj : ∀ (l u : FF c) (v' : Var), v' ∈ ffVarsOfFormula (FFFormula.and
                (FFFormula.eq (simpleSymValToTerm A)
                  (FFTerm.add (FFTerm.mul (FFTerm.var sconf.nextVarId) (FFTerm.val B))
                    (FFTerm.var (sconf.nextVarId + 1))))
                (FFFormula.and
                  (FFFormula.range (FFTerm.var (sconf.nextVarId + 1)) 0 (B.val - 1 : FF c))
                  (FFFormula.range (FFTerm.var sconf.nextVarId) l u))) →
                v' = Var.ffv sconf.nextVarId ∨ v' = Var.ffv (sconf.nextVarId + 1) ∨
                  v' ∈ simpleValOwnVars A := by
              intro l u v' hv'
              simp only [ffVarsOfFormula, ffVarsOfTerm, ffVarsOfTerm_simpleSymValToTerm,
                Std.TreeSet.mem_union_iff] at hv'
              rcases hv' with (hA | (hQ | hE) | hR) | (hR2 | hQ2)
              · exact Or.inr (Or.inr hA)
              · rcases Std.TreeSet.mem_insert.mp hQ with heq | hmem
                · exact Or.inl (Var_compare_eq_iff_eq.mp heq).symm
                · exact absurd hmem Std.TreeSet.not_mem_emptyc
              · exact absurd hE Std.TreeSet.not_mem_emptyc
              · rcases Std.TreeSet.mem_insert.mp hR with heq | hmem
                · exact Or.inr (Or.inl (Var_compare_eq_iff_eq.mp heq).symm)
                · exact absurd hmem Std.TreeSet.not_mem_emptyc
              · rcases Std.TreeSet.mem_insert.mp hR2 with heq | hmem
                · exact Or.inr (Or.inl (Var_compare_eq_iff_eq.mp heq).symm)
                · exact absurd hmem Std.TreeSet.not_mem_emptyc
              · rcases Std.TreeSet.mem_insert.mp hQ2 with heq | hmem
                · exact Or.inl (Var_compare_eq_iff_eq.mp heq).symm
                · exact absurd hmem Std.TreeSet.not_mem_emptyc
            have hbdisj : ∀ (l u : FF c) (v' : Var), v' ∈ bVarsOfFormula (FFFormula.and
                (FFFormula.eq (simpleSymValToTerm A)
                  (FFTerm.add (FFTerm.mul (FFTerm.var sconf.nextVarId) (FFTerm.val B))
                    (FFTerm.var (sconf.nextVarId + 1))))
                (FFFormula.and
                  (FFFormula.range (FFTerm.var (sconf.nextVarId + 1)) 0 (B.val - 1 : FF c))
                  (FFFormula.range (FFTerm.var sconf.nextVarId) l u))) → False := by
              intro l u v' hv'
              simp only [bVarsOfFormula, bVarsOfTerm, bVarsOfTerm_simpleSymValToTerm,
                Std.TreeSet.mem_union_iff] at hv'
              rcases hv' with (h | (h | h) | h) | (h | h) <;>
                exact absurd h Std.TreeSet.not_mem_emptyc
            have hmemQ_f : Var.ffv sconf.nextVarId ∈
                ffVarsOfFormula (FFFormula.ite
                  (FFFormula.range (simpleSymValToTerm A) 0 (c.midpoint - 1 : FF c))
                  (FFFormula.and (FFFormula.eq (simpleSymValToTerm A)
                      (FFTerm.add (FFTerm.mul (FFTerm.var sconf.nextVarId) (FFTerm.val B))
                        (FFTerm.var (sconf.nextVarId + 1))))
                    (FFFormula.and
                      (FFFormula.range (FFTerm.var (sconf.nextVarId + 1)) 0 (B.val - 1 : FF c))
                      (FFFormula.range (FFTerm.var sconf.nextVarId) 0
                        (((c.midpoint - 1) / B.val : Nat) : FF c))))
                  (FFFormula.and (FFFormula.eq (simpleSymValToTerm A)
                      (FFTerm.add (FFTerm.mul (FFTerm.var sconf.nextVarId) (FFTerm.val B))
                        (FFTerm.var (sconf.nextVarId + 1))))
                    (FFFormula.and
                      (FFFormula.range (FFTerm.var (sconf.nextVarId + 1)) 0 (B.val - 1 : FF c))
                      (FFFormula.range (FFTerm.var sconf.nextVarId)
                        ((c.midpoint / B.val : Nat) : FF c)
                        (((c.p - 1) / B.val : Nat) : FF c))))) :=
              Std.TreeSet.mem_union_of_left
                (Std.TreeSet.mem_union_of_right (Std.TreeSet.mem_union_of_left hmemQeqn))
            have hmemR_f : Var.ffv (sconf.nextVarId + 1) ∈
                ffVarsOfFormula (FFFormula.ite
                  (FFFormula.range (simpleSymValToTerm A) 0 (c.midpoint - 1 : FF c))
                  (FFFormula.and (FFFormula.eq (simpleSymValToTerm A)
                      (FFTerm.add (FFTerm.mul (FFTerm.var sconf.nextVarId) (FFTerm.val B))
                        (FFTerm.var (sconf.nextVarId + 1))))
                    (FFFormula.and
                      (FFFormula.range (FFTerm.var (sconf.nextVarId + 1)) 0 (B.val - 1 : FF c))
                      (FFFormula.range (FFTerm.var sconf.nextVarId) 0
                        (((c.midpoint - 1) / B.val : Nat) : FF c))))
                  (FFFormula.and (FFFormula.eq (simpleSymValToTerm A)
                      (FFTerm.add (FFTerm.mul (FFTerm.var sconf.nextVarId) (FFTerm.val B))
                        (FFTerm.var (sconf.nextVarId + 1))))
                    (FFFormula.and
                      (FFFormula.range (FFTerm.var (sconf.nextVarId + 1)) 0 (B.val - 1 : FF c))
                      (FFFormula.range (FFTerm.var sconf.nextVarId)
                        ((c.midpoint / B.val : Nat) : FF c)
                        (((c.p - 1) / B.val : Nat) : FF c))))) :=
              Std.TreeSet.mem_union_of_left
                (Std.TreeSet.mem_union_of_right (Std.TreeSet.mem_union_of_left hmemReqn))
            set isLowExpr : FFFormula c :=
              FFFormula.range (simpleSymValToTerm A) 0 (c.midpoint - 1 : FF c)
              with hisLowExpr_def
            set eqnExpr : FFFormula c := FFFormula.eq (simpleSymValToTerm A)
                (FFTerm.add (FFTerm.mul (FFTerm.var sconf.nextVarId) (FFTerm.val B))
                  (FFTerm.var (sconf.nextVarId + 1)))
              with heqnExpr_def
            set rRangeExpr : FFFormula c :=
              FFFormula.range (FFTerm.var (sconf.nextVarId + 1)) 0 (B.val - 1 : FF c)
              with hrRangeExpr_def
            set qLowExpr : FFFormula c :=
              FFFormula.range (FFTerm.var sconf.nextVarId) 0
                (((c.midpoint - 1) / B.val : Nat) : FF c)
              with hqLowExpr_def
            set qHighExpr : FFFormula c :=
              FFFormula.range (FFTerm.var sconf.nextVarId) ((c.midpoint / B.val : Nat) : FF c)
                (((c.p - 1) / B.val : Nat) : FF c)
              with hqHighExpr_def
            set lowBranchExpr : FFFormula c :=
              FFFormula.and eqnExpr (FFFormula.and rRangeExpr qLowExpr) with hlowBranchExpr_def
            set highBranchExpr : FFFormula c :=
              FFFormula.and eqnExpr (FFFormula.and rRangeExpr qHighExpr) with hhighBranchExpr_def
            set fExpr : FFFormula c := FFFormula.ite isLowExpr lowBranchExpr highBranchExpr
              with hfExpr_def
            refine ⟨Nat.le_add_right sconf.nextVarId 2, ?_, ?_, ?_,
              varSetBelow_mono (Nat.le_add_right sconf.nextVarId 2) hbelow,
              fun v' hv' => Or.inl hv', ValidBinRep_trivial gconf _ _, ?_, ?_⟩
            · intro v' hv'
              simp only [simpleValVars, simpleValOwnVars, Option.map_none, Option.getD_none,
                Std.TreeSet.mem_union_iff] at hv'
              rcases hv' with h | h
              · rcases Std.TreeSet.mem_insert.mp h with heq | hmem
                · rw [← Var_compare_eq_iff_eq.mp heq]
                  exact Or.inr (Std.TreeSet.mem_union_of_left hmemQ_f)
                · exact absurd hmem Std.TreeSet.not_mem_emptyc
              · exact absurd h Std.TreeSet.not_mem_emptyc
            · intro v' hv'
              simp only [exprSpecVars] at hv'
              rcases Std.TreeSet.mem_union_iff.mp hv' with hff | hb
              · simp only [hfExpr_def, ffVarsOfFormula, Std.TreeSet.mem_union_iff] at hff
                rcases hff with hff' | hhigh
                · rcases hff' with hisLow | hlow
                  · rw [hisLowExpr_def, ffVarsOfFormula, ffVarsOfTerm_simpleSymValToTerm] at hisLow
                    exact Or.inl (hsubA v' (simpleValOwnVars_subset_simpleValVars A v' hisLow))
                  · rcases hffdisj 0 (((c.midpoint - 1) / B.val : Nat) : FF c) v' hlow with
                      heq | heq | h
                    · rw [heq]; exact Or.inr (le_refl _)
                    · rw [heq]; refine Or.inr ?_; simp only [varIndex]; omega
                    · exact Or.inl (hsubA v' (simpleValOwnVars_subset_simpleValVars A v' h))
                · rcases hffdisj ((c.midpoint / B.val : Nat) : FF c)
                    (((c.p - 1) / B.val : Nat) : FF c) v' hhigh with heq | heq | h
                  · rw [heq]; exact Or.inr (le_refl _)
                  · rw [heq]; refine Or.inr ?_; simp only [varIndex]; omega
                  · exact Or.inl (hsubA v' (simpleValOwnVars_subset_simpleValVars A v' h))
              · exfalso
                simp only [hfExpr_def, bVarsOfFormula, Std.TreeSet.mem_union_iff] at hb
                rcases hb with hb' | hbhigh
                · rcases hb' with hbisLow | hblow
                  · rw [hisLowExpr_def, bVarsOfFormula, bVarsOfTerm_simpleSymValToTerm] at hbisLow
                    exact absurd hbisLow Std.TreeSet.not_mem_emptyc
                  · exact hbdisj 0 (((c.midpoint - 1) / B.val : Nat) : FF c) v' hblow
                · exact hbdisj ((c.midpoint / B.val : Nat) : FF c)
                    (((c.p - 1) / B.val : Nat) : FF c) v' hbhigh
            · intro v' hv'
              simp only [exprSpecVars] at hv'
              rcases Std.TreeSet.mem_union_iff.mp hv' with hff | hb
              · simp only [hfExpr_def, ffVarsOfFormula, Std.TreeSet.mem_union_iff] at hff
                rcases hff with hff' | hhigh
                · rcases hff' with hisLow | hlow
                  · rw [hisLowExpr_def, ffVarsOfFormula, ffVarsOfTerm_simpleSymValToTerm] at hisLow
                    exact lt_of_lt_of_le
                      (hbelow v' (hsubA v' (simpleValOwnVars_subset_simpleValVars A v' hisLow)))
                      (Nat.le_add_right sconf.nextVarId 2)
                  · rcases hffdisj 0 (((c.midpoint - 1) / B.val : Nat) : FF c) v' hlow with
                      heq | heq | h
                    · rw [heq]; simp only [varIndex]; omega
                    · rw [heq]; simp only [varIndex]; omega
                    · exact lt_of_lt_of_le
                        (hbelow v' (hsubA v' (simpleValOwnVars_subset_simpleValVars A v' h)))
                        (Nat.le_add_right sconf.nextVarId 2)
                · rcases hffdisj ((c.midpoint / B.val : Nat) : FF c)
                    (((c.p - 1) / B.val : Nat) : FF c) v' hhigh with heq | heq | h
                  · rw [heq]; simp only [varIndex]; omega
                  · rw [heq]; simp only [varIndex]; omega
                  · exact lt_of_lt_of_le
                      (hbelow v' (hsubA v' (simpleValOwnVars_subset_simpleValVars A v' h)))
                      (Nat.le_add_right sconf.nextVarId 2)
              · exfalso
                simp only [hfExpr_def, bVarsOfFormula, Std.TreeSet.mem_union_iff] at hb
                rcases hb with hb' | hbhigh
                · rcases hb' with hbisLow | hblow
                  · rw [hisLowExpr_def, bVarsOfFormula, bVarsOfTerm_simpleSymValToTerm] at hbisLow
                    exact absurd hbisLow Std.TreeSet.not_mem_emptyc
                  · exact hbdisj 0 (((c.midpoint - 1) / B.val : Nat) : FF c) v' hblow
                · exact hbdisj ((c.midpoint / B.val : Nat) : FF c)
                    (((c.p - 1) / B.val : Nat) : FF c) v' hbhigh
            · intro env assignment hmatch val hval
              obtain ⟨Aval, hAval, hmA⟩ :=
                resolveSimpleExpr_correct symEnv e1 env assignment A hmatch hres1
              have hB' := tryEvalSimpleExprToFFValue_correct symEnv e2 env assignment B hmatch hB
              simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hAval, hB',
                evalUidiv, if_neg hBne0] at hval
              injection hval with hval
              set assignment' : Assignment c :=
                { assignment with
                  ff := fun n => if n = sconf.nextVarId then ((Aval.val / B.val : Nat) : FF c)
                    else if n = sconf.nextVarId + 1 then ((Aval.val % B.val : Nat) : FF c)
                    else assignment.ff n }
                with hassignment'_def
              have hagreeff : agreesOnFF (symEnvVars symEnv) assignment assignment' := by
                intro n hn
                have hne1 : n ≠ sconf.nextVarId := Nat.ne_of_lt (hbelow (Var.ffv n) hn)
                have hne2 : n ≠ sconf.nextVarId + 1 := by
                  have h : n < sconf.nextVarId := by
                    have h' := hbelow (Var.ffv n) hn
                    simpa only [varIndex] using h'
                  exact Nat.ne_of_lt (lt_trans h (Nat.lt_succ_self _))
                simp only [hassignment'_def, if_neg hne1, if_neg hne2]
              have hagreebool : agreesOnBool (symEnvVars symEnv) assignment assignment' :=
                fun n _ => rfl
              have hframeff : ∀ n, Var.ffv n ∉ (ffVarsOfFormula fExpr ∪ bVarsOfFormula fExpr) →
                  assignment'.ff n = assignment.ff n := by
                intro n hn
                have hne1 : n ≠ sconf.nextVarId := by
                  intro heqn; apply hn; rw [heqn]
                  exact Std.TreeSet.mem_union_of_left hmemQ_f
                have hne2 : n ≠ sconf.nextVarId + 1 := by
                  intro heqn; apply hn; rw [heqn]
                  exact Std.TreeSet.mem_union_of_left hmemR_f
                simp only [hassignment'_def, if_neg hne1, if_neg hne2]
              have hframebool : ∀ n, Var.boolv n ∉ (ffVarsOfFormula fExpr ∪ bVarsOfFormula fExpr) →
                  assignment'.bool n = assignment.bool n := fun n _ => rfl
              have hAterm_eval : evalTerm gconf assignment' (simpleSymValToTerm A)
                  (specs.map (·.f)) = Except.ok Aval := by
                have hmA' : simpleValMatches assignment' A Aval :=
                  simpleValMatches_agreesOnFF_preserves assignment assignment' A Aval
                    (symEnvVars symEnv) hsubA hagreeff hmA
                exact evalTerm_simpleSymValToTerm gconf assignment' A Aval (specs.map (·.f)) hmA'
              have hqeval : assignment'.ff sconf.nextVarId = ((Aval.val / B.val : Nat) : FF c) := by
                simp [hassignment'_def]
              have hreval : assignment'.ff (sconf.nextVarId + 1)
                  = ((Aval.val % B.val : Nat) : FF c) := by
                simp [hassignment'_def]
              have heqn_true : evalFormula gconf assignment' eqnExpr (specs.map (·.f))
                  = Except.ok true := by
                rw [heqnExpr_def]
                simp only [evalFormula, evalTerm, hAterm_eval, hqeval, hreval]
                rw [cast_div_add_mod_eq' Aval.val B, ZMod.natCast_rightInverse Aval]
                simp
              have hrRange_true : evalFormula gconf assignment' rRangeExpr (specs.map (·.f))
                  = Except.ok true := by
                rw [hrRangeExpr_def]
                rw [evalFormula_range_iff gconf assignment' (specs.map (·.f))
                  (FFTerm.var (sconf.nextVarId + 1)) 0 (B.val - 1 : FF c)
                  (((Aval.val % B.val : Nat) : FF c)) (by simp only [evalTerm, hreval])]
                have h0 : toSigned (0 : FF c) = 0 := by
                  have : (0 : FF c) = ((0 : Nat) : FF c) := by norm_num
                  rw [this, toSigned_natCast_of_lt 0 (by have := c.p_prime.two_le; omega)
                    (by omega)]
                  simp
                have hB1 : toSigned (B.val - 1 : FF c) = ((B.val - 1 : Nat) : Int) := by
                  rw [cast_sub_one_eq B.val (by omega),
                    toSigned_natCast_of_lt (B.val - 1) (by omega) (by omega)]
                have hRmod : toSigned (((Aval.val % B.val : Nat) : FF c))
                    = ((Aval.val % B.val : Nat) : Int) :=
                  toSigned_natCast_of_lt (Aval.val % B.val)
                    (by have := Nat.mod_lt Aval.val (show 0 < B.val by omega); omega)
                    (by have := Nat.mod_lt Aval.val (show 0 < B.val by omega); omega)
                rw [h0, hB1, hRmod]
                constructor
                · exact Int.ofNat_nonneg _
                · have := Nat.mod_lt Aval.val (show 0 < B.val by omega)
                  exact_mod_cast (by omega : Aval.val % B.val ≤ B.val - 1)
              refine ⟨assignment', hagreeff, hagreebool, hframeff, hframebool, ?_,
                EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagreeff hmatch,
                ?_⟩
              · rw [hfExpr_def]
                by_cases hAlow : Aval.val < c.midpoint
                · have hisLow_true : evalFormula gconf assignment' isLowExpr (specs.map (·.f))
                      = Except.ok true := by
                    rw [hisLowExpr_def]
                    rw [evalFormula_range_iff gconf assignment' (specs.map (·.f))
                      (simpleSymValToTerm A) 0 (c.midpoint - 1 : FF c) Aval hAterm_eval]
                    have h0 : toSigned (0 : FF c) = 0 := by
                      have : (0 : FF c) = ((0 : Nat) : FF c) := by norm_num
                      rw [this, toSigned_natCast_of_lt 0 (by have := c.p_prime.two_le; omega)
                        (by omega)]
                      simp
                    have hmid1 : toSigned (c.midpoint - 1 : FF c)
                        = ((c.midpoint - 1 : Nat) : Int) := by
                      rw [cast_sub_one_eq c.midpoint (by omega),
                        toSigned_natCast_of_lt (c.midpoint - 1) (by omega) (by omega)]
                    rw [h0, hmid1, toSigned_of_val_lt_midpoint Aval hAlow]
                    exact ⟨Int.ofNat_nonneg _, by exact_mod_cast (by omega : Aval.val ≤
                      c.midpoint - 1)⟩
                  have hqLow_true : evalFormula gconf assignment' qLowExpr (specs.map (·.f))
                      = Except.ok true := by
                    rw [hqLowExpr_def]
                    rw [evalFormula_range_iff gconf assignment' (specs.map (·.f))
                      (FFTerm.var sconf.nextVarId) 0 (((c.midpoint - 1) / B.val : Nat) : FF c)
                      (((Aval.val / B.val : Nat) : FF c)) (by simp only [evalTerm, hqeval])]
                    have h0 : toSigned (0 : FF c) = 0 := by
                      have : (0 : FF c) = ((0 : Nat) : FF c) := by norm_num
                      rw [this, toSigned_natCast_of_lt 0 (by have := c.p_prime.two_le; omega)
                        (by omega)]
                      simp
                    have hqLowBound := uidiv_qLow_bound B.val hB2 hBmid
                    have huLo : toSigned (((c.midpoint - 1) / B.val : Nat) : FF c)
                        = (((c.midpoint - 1) / B.val : Nat) : Int) :=
                      toSigned_natCast_of_lt _ (by omega) hqLowBound
                    have hQdvd : Aval.val / B.val ≤ (c.midpoint - 1) / B.val :=
                      Nat.div_le_div_right (by omega)
                    have hQval : toSigned (((Aval.val / B.val : Nat) : FF c))
                        = ((Aval.val / B.val : Nat) : Int) :=
                      toSigned_natCast_of_lt _ (by omega) (by omega)
                    rw [h0, huLo, hQval]
                    exact ⟨Int.ofNat_nonneg _, by exact_mod_cast hQdvd⟩
                  refine evalFormula_ite_true gconf assignment' (specs.map (·.f)) isLowExpr
                    lowBranchExpr highBranchExpr hisLow_true ?_
                  rw [hlowBranchExpr_def]
                  exact evalFormula_and_intro gconf assignment' (specs.map (·.f)) eqnExpr
                    (FFFormula.and rRangeExpr qLowExpr) heqn_true
                    (evalFormula_and_intro gconf assignment' (specs.map (·.f)) rRangeExpr qLowExpr
                      hrRange_true hqLow_true)
                · have hisLow_false : evalFormula gconf assignment' isLowExpr (specs.map (·.f))
                      = Except.ok false := by
                    rw [hisLowExpr_def]
                    have hiff := evalFormula_range_iff gconf assignment' (specs.map (·.f))
                      (simpleSymValToTerm A) 0 (c.midpoint - 1 : FF c) Aval hAterm_eval
                    cases hres : evalFormula gconf assignment'
                        (FFFormula.range (simpleSymValToTerm A) 0 (c.midpoint - 1 : FF c))
                        (specs.map (·.f)) with
                    | error msg =>
                        simp [evalFormula, hAterm_eval] at hres
                    | ok b =>
                        cases b with
                        | true =>
                            exfalso
                            have h0 : toSigned (0 : FF c) = 0 := by
                              have : (0 : FF c) = ((0 : Nat) : FF c) := by norm_num
                              rw [this, toSigned_natCast_of_lt 0
                                (by have := c.p_prime.two_le; omega) (by omega)]
                              simp
                            have hmid1 : toSigned (c.midpoint - 1 : FF c)
                                = ((c.midpoint - 1 : Nat) : Int) := by
                              rw [cast_sub_one_eq c.midpoint (by omega),
                                toSigned_natCast_of_lt (c.midpoint - 1) (by omega) (by omega)]
                            have := hiff.mp hres
                            rw [hmid1] at this
                            have hAvalSigned : c.midpoint ≤ Aval.val := by omega
                            have : toSigned Aval < 0 := by
                              simp only [Corellzk2smt.Language.Core.Semantics.Basic.toSigned,
                                if_neg (by omega : ¬ Aval.val < c.midpoint)]
                              have := ZMod.val_lt Aval
                              omega
                            omega
                        | false => rfl
                  have hqHigh_true : evalFormula gconf assignment' qHighExpr (specs.map (·.f))
                      = Except.ok true := by
                    rw [hqHighExpr_def]
                    rw [evalFormula_range_iff gconf assignment' (specs.map (·.f))
                      (FFTerm.var sconf.nextVarId) ((c.midpoint / B.val : Nat) : FF c)
                      (((c.p - 1) / B.val : Nat) : FF c) (((Aval.val / B.val : Nat) : FF c))
                      (by simp only [evalTerm, hqeval])]
                    have hqHighLoBound := uidiv_qHighLo_bound B.val hB2 hBmid
                    have hqHighHiBound := uidiv_qHighHi_bound B.val hB2 hBmid
                    have hlo : toSigned ((c.midpoint / B.val : Nat) : FF c)
                        = ((c.midpoint / B.val : Nat) : Int) :=
                      toSigned_natCast_of_lt _ (by omega) hqHighLoBound
                    have hhi : toSigned (((c.p - 1) / B.val : Nat) : FF c)
                        = (((c.p - 1) / B.val : Nat) : Int) :=
                      toSigned_natCast_of_lt _ (by omega) hqHighHiBound
                    have hAvalLtP := ZMod.val_lt Aval
                    have hAvalB_le_hi : Aval.val / B.val ≤ (c.p - 1) / B.val :=
                      Nat.div_le_div_right (by omega)
                    have hAvalB_ge_lo : c.midpoint / B.val ≤ Aval.val / B.val :=
                      Nat.div_le_div_right (by omega)
                    have hQval : toSigned (((Aval.val / B.val : Nat) : FF c))
                        = ((Aval.val / B.val : Nat) : Int) :=
                      toSigned_natCast_of_lt _ (by omega) (by omega)
                    rw [hlo, hhi, hQval]
                    exact ⟨by exact_mod_cast hAvalB_ge_lo, by exact_mod_cast hAvalB_le_hi⟩
                  refine evalFormula_ite_false gconf assignment' (specs.map (·.f)) isLowExpr
                    lowBranchExpr highBranchExpr hisLow_false ?_
                  rw [hhighBranchExpr_def]
                  exact evalFormula_and_intro gconf assignment' (specs.map (·.f)) eqnExpr
                    (FFFormula.and rRangeExpr qHighExpr) heqn_true
                    (evalFormula_and_intro gconf assignment' (specs.map (·.f)) rRangeExpr qHighExpr
                      hrRange_true hqHigh_true)
              · simp only [simpleValMatches, hqeval]
                exact hval
            · intro env assignment hmatch assignment' hagree heval_f
              have hmatch' : EnvMatches assignment' symEnv env :=
                EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagree hmatch
              obtain ⟨Aval, hAval, hmA'⟩ :=
                resolveSimpleExpr_correct symEnv e1 env assignment' A hmatch' hres1
              have hB' := tryEvalSimpleExprToFFValue_correct symEnv e2 env assignment' B hmatch'
                hB
              have hAterm_eval : evalTerm gconf assignment' (simpleSymValToTerm A)
                  (specs.map (·.f)) = Except.ok Aval :=
                evalTerm_simpleSymValToTerm gconf assignment' A Aval (specs.map (·.f)) hmA'
              have hrange_extract : ∀ (t : FFVar) (lo hi tval : FF c),
                  lo.val < c.midpoint → hi.val < c.midpoint → assignment'.ff t = tval →
                  evalFormula gconf assignment'
                      (FFFormula.range (FFTerm.var t) lo hi)
                      (specs.map (·.f)) = Except.ok true →
                  lo.val ≤ tval.val ∧ tval.val ≤ hi.val := by
                intro t lo hi tval hlo hhi htval heval
                have hEvalT : evalTerm gconf assignment' (FFTerm.var t) (specs.map (·.f))
                    = Except.ok tval := by simp only [evalTerm, htval]
                rw [evalFormula_range_iff gconf assignment' (specs.map (·.f)) (FFTerm.var t)
                  lo hi tval hEvalT] at heval
                have hlo_signed : toSigned lo = (lo.val : Int) := toSigned_of_val_lt_midpoint lo hlo
                have hhi_signed : toSigned hi = (hi.val : Int) := toSigned_of_val_lt_midpoint hi hhi
                rw [hlo_signed, hhi_signed] at heval
                have htval_lt_mid : tval.val < c.midpoint := by
                  by_contra hcon
                  push_neg at hcon
                  have hneg : toSigned tval < 0 := by
                    simp only [Corellzk2smt.Language.Core.Semantics.Basic.toSigned,
                      if_neg (show ¬tval.val < c.midpoint by omega)]
                    have := ZMod.val_lt tval
                    omega
                  have hlo_nonneg : (0:Int) ≤ (lo.val:Int) := by exact_mod_cast Nat.zero_le lo.val
                  omega
                rw [toSigned_of_val_lt_midpoint tval htval_lt_mid] at heval
                exact ⟨by exact_mod_cast heval.1, by exact_mod_cast heval.2⟩
              have hzero_eq : (0 : FF c).val = 0 := ZMod.val_zero
              have hzero_bound : (0 : FF c).val < c.midpoint := by
                rw [hzero_eq]; have := c.p_prime.two_le; omega
              have hRupper_eq : (B.val - 1 : FF c).val = B.val - 1 := by
                rw [cast_sub_one_eq B.val (by omega), val_natCast_eq]
                exact Nat.mod_eq_of_lt (by omega)
              have hRupper_bound : (B.val - 1 : FF c).val < c.midpoint := by
                rw [hRupper_eq]; omega
              rw [hfExpr_def] at heval_f
              set Qfield : FF c := assignment'.ff sconf.nextVarId with hQfield_def
              set Rfield : FF c := assignment'.ff (sconf.nextVarId + 1) with hRfield_def
              have hrhs_eval : evalTerm gconf assignment'
                  (FFTerm.add (FFTerm.mul (FFTerm.var sconf.nextVarId) (FFTerm.val B))
                    (FFTerm.var (sconf.nextVarId + 1))) (specs.map (·.f))
                  = Except.ok (Qfield * B + Rfield) := by
                simp only [evalTerm, hQfield_def, hRfield_def]
              cases hisLow_eval : evalFormula gconf assignment' isLowExpr (specs.map (·.f)) with
              | error msg =>
                  rw [hisLowExpr_def] at hisLow_eval
                  simp [evalFormula, hAterm_eval] at hisLow_eval
              | ok b =>
                  simp only [evalFormula, hisLow_eval] at heval_f
                  cases b with
                  | true =>
                      simp only [if_true] at heval_f
                      rw [hlowBranchExpr_def] at heval_f
                      obtain ⟨heqn, hrest⟩ :=
                        evalFormula_and_elim gconf assignment' (specs.map (·.f)) eqnExpr
                          (FFFormula.and rRangeExpr qLowExpr) heval_f
                      obtain ⟨hrR, hqR⟩ :=
                        evalFormula_and_elim gconf assignment' (specs.map (·.f)) rRangeExpr
                          qLowExpr hrest
                      have hRbound := hrange_extract (sconf.nextVarId + 1) 0 (B.val - 1 : FF c)
                        Rfield hzero_bound hRupper_bound rfl
                        (by rw [← hrRangeExpr_def]; exact hrR)
                      rw [hzero_eq, hRupper_eq] at hRbound
                      have hqLow_eq : (((c.midpoint - 1) / B.val : Nat) : FF c).val
                          = (c.midpoint - 1) / B.val := by
                        rw [val_natCast_eq]
                        exact Nat.mod_eq_of_lt (by
                          have := uidiv_qLow_bound B.val hB2 hBmid; omega)
                      have hqLowUpper : (((c.midpoint - 1) / B.val : Nat) : FF c).val
                          < c.midpoint := by
                        rw [hqLow_eq]; exact uidiv_qLow_bound B.val hB2 hBmid
                      have hQbound := hrange_extract sconf.nextVarId 0
                        (((c.midpoint - 1) / B.val : Nat) : FF c) Qfield hzero_bound hqLowUpper
                        rfl (by rw [← hqLowExpr_def]; exact hqR)
                      rw [hzero_eq, hqLow_eq] at hQbound
                      have heqn_field : Aval = Qfield * B + Rfield := by
                        rw [heqnExpr_def] at heqn
                        exact (evalFormula_eq_iff gconf assignment' (specs.map (·.f))
                          (simpleSymValToTerm A) _ Aval (Qfield * B + Rfield) hAterm_eval
                          hrhs_eval).mp heqn
                      have hmul : Qfield.val * B.val ≤ (c.midpoint - 1) / B.val * B.val :=
                        Nat.mul_le_mul_right B.val hQbound.2
                      have hSlt2p : Qfield.val * B.val + Rfield.val < 2 * c.p := by omega
                      have hSeq : Qfield.val * B.val + Rfield.val = Aval.val :=
                        QBR_val_eq_of_no_wrap Qfield B Rfield Aval heqn_field hSlt2p
                          (fun hge => absurd hge (by omega))
                      obtain ⟨hQeq, hReq⟩ := nat_eq_div_mod_of_eq (show 0 < B.val by omega)
                        hSeq (by omega)
                      have hQfield_eq : Qfield = ((Aval.val / B.val : Nat) : FF c) := by
                        have hround : ((Qfield.val : Nat) : FF c) = Qfield :=
                          ZMod.natCast_rightInverse Qfield
                        rw [← hQeq] at hround
                        exact hround.symm
                      refine ⟨Qfield, ?_, hmatch', ?_⟩
                      · simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hAval,
                          hB', evalUidiv, if_neg hBne0]
                        rw [hQfield_eq]
                      · simp only [simpleValMatches]
                        exact hQfield_def.symm
                  | false =>
                      simp only [Bool.false_eq_true, if_false] at heval_f
                      rw [hhighBranchExpr_def] at heval_f
                      obtain ⟨heqn, hrest⟩ :=
                        evalFormula_and_elim gconf assignment' (specs.map (·.f)) eqnExpr
                          (FFFormula.and rRangeExpr qHighExpr) heval_f
                      obtain ⟨hrR, hqR⟩ :=
                        evalFormula_and_elim gconf assignment' (specs.map (·.f)) rRangeExpr
                          qHighExpr hrest
                      have hRbound := hrange_extract (sconf.nextVarId + 1) 0 (B.val - 1 : FF c)
                        Rfield hzero_bound hRupper_bound rfl
                        (by rw [← hrRangeExpr_def]; exact hrR)
                      rw [hzero_eq, hRupper_eq] at hRbound
                      have hqHighLo_eq : ((c.midpoint / B.val : Nat) : FF c).val
                          = c.midpoint / B.val := by
                        rw [val_natCast_eq]
                        exact Nat.mod_eq_of_lt (by
                          have := uidiv_qHighLo_bound B.val hB2 hBmid; omega)
                      have hqHighLoUpper : ((c.midpoint / B.val : Nat) : FF c).val
                          < c.midpoint := by
                        rw [hqHighLo_eq]; exact uidiv_qHighLo_bound B.val hB2 hBmid
                      have hqHighHi_eq : (((c.p - 1) / B.val : Nat) : FF c).val
                          = (c.p - 1) / B.val := by
                        rw [val_natCast_eq]
                        exact Nat.mod_eq_of_lt (by
                          have := uidiv_qHighHi_bound B.val hB2 hBmid; omega)
                      have hqHighHiUpper : (((c.p - 1) / B.val : Nat) : FF c).val
                          < c.midpoint := by
                        rw [hqHighHi_eq]; exact uidiv_qHighHi_bound B.val hB2 hBmid
                      have hQbound := hrange_extract sconf.nextVarId
                        ((c.midpoint / B.val : Nat) : FF c) (((c.p - 1) / B.val : Nat) : FF c)
                        Qfield hqHighLoUpper hqHighHiUpper rfl
                        (by rw [← hqHighExpr_def]; exact hqR)
                      rw [hqHighLo_eq, hqHighHi_eq] at hQbound
                      have hAval_hi : c.midpoint ≤ Aval.val := by
                        by_contra hcon
                        push_neg at hcon
                        have htrue : evalFormula gconf assignment' isLowExpr (specs.map (·.f))
                            = Except.ok true := by
                          rw [hisLowExpr_def]
                          rw [evalFormula_range_iff gconf assignment' (specs.map (·.f))
                            (simpleSymValToTerm A) 0 (c.midpoint - 1 : FF c) Aval hAterm_eval]
                          have h0 : toSigned (0 : FF c) = 0 := by
                            have : (0 : FF c) = ((0 : Nat) : FF c) := by norm_num
                            rw [this, toSigned_natCast_of_lt 0
                              (by have := c.p_prime.two_le; omega) (by omega)]
                            simp
                          have hmid1 : toSigned (c.midpoint - 1 : FF c)
                              = ((c.midpoint - 1 : Nat) : Int) := by
                            rw [cast_sub_one_eq c.midpoint (by omega),
                              toSigned_natCast_of_lt (c.midpoint - 1) (by omega) (by omega)]
                          rw [h0, hmid1, toSigned_of_val_lt_midpoint Aval hcon]
                          exact ⟨Int.ofNat_nonneg _, by exact_mod_cast
                            (by omega : Aval.val ≤ c.midpoint - 1)⟩
                        rw [htrue] at hisLow_eval
                        simp at hisLow_eval
                      have heqn_field : Aval = Qfield * B + Rfield := by
                        rw [heqnExpr_def] at heqn
                        exact (evalFormula_eq_iff gconf assignment' (specs.map (·.f))
                          (simpleSymValToTerm A) _ Aval (Qfield * B + Rfield) hAterm_eval
                          hrhs_eval).mp heqn
                      have hmul : Qfield.val * B.val ≤ (c.p - 1) / B.val * B.val :=
                        Nat.mul_le_mul_right B.val hQbound.2
                      have hSlt2p : Qfield.val * B.val + Rfield.val < 2 * c.p := by omega
                      have hSeq : Qfield.val * B.val + Rfield.val = Aval.val :=
                        QBR_val_eq_of_no_wrap Qfield B Rfield Aval heqn_field hSlt2p
                          (fun _ => by omega)
                      obtain ⟨hQeq, hReq⟩ := nat_eq_div_mod_of_eq (show 0 < B.val by omega)
                        hSeq (by omega)
                      have hQfield_eq : Qfield = ((Aval.val / B.val : Nat) : FF c) := by
                        have hround : ((Qfield.val : Nat) : FF c) = Qfield :=
                          ZMod.natCast_rightInverse Qfield
                        rw [← hQeq] at hround
                        exact hround.symm
                      refine ⟨Qfield, ?_, hmatch', ?_⟩
                      · simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hAval,
                          hB', evalUidiv, if_neg hBne0]
                        rw [hQfield_eq]
                      · simp only [simpleValMatches]
                        exact hQfield_def.symm
      · have hcond : (B.val > 1 && B.val < c.midpoint) = false := by
          simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, gt_iff_lt, not_lt]
          omega
        simp only [hcond, if_false] at hspec_eq
        by_cases hBge : B.val ≥ c.midpoint
        · rw [if_pos hBge] at hspec_eq
          sorry
        · exfalso
          rw [if_neg hBge] at hspec_eq
          simp at hspec_eq

theorem seExprUIDiv_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD) (e1 e2 : SimpleExpr c) :
    TranslatesExprCorrectly gconf sconf specs ctx
      (fun env => Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env
        (Expr.bop BinOp.uidiv e1 e2))
      (fun symEnv => seExprUIDiv md gconf sconf symEnv specs e1 e2) := by
  intro symEnv hbelow hvalid espec hspec_eq
  simp only [seExprUIDiv] at hspec_eq
  cases hconst : seExprUIDivWithConstantDivisor md gconf sconf symEnv specs e1 e2 with
  | ok result =>
      rw [hconst] at hspec_eq
      injection hspec_eq with hspec_eq
      subst hspec_eq
      exact seExprUIDivWithConstantDivisor_correct gconf specs sconf ctx md e1 e2 symEnv
        hbelow hvalid result hconst
  | error msg =>
      rw [hconst] at hspec_eq
      simp [seExprUIDivWithNonConstantDivisor] at hspec_eq

/-- `seExprUIModWithConstantDivisor`'s `B.val = 1` case: modulo one is always zero, for
    *any* dividend -- `e1` is still resolved (so a malformed dividend is still caught), but its
    value is discarded; no fresh variable, no real formula content. -/
theorem seExprUIModWithConstantDivisor_correct {c : ZKConfig} (gconf : GlobalConfig c)
    (specs : List (FuncSpec c)) (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD)
    (e1 e2 : SimpleExpr c) :
    TranslatesExprCorrectly gconf sconf specs ctx
      (fun env => Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env
        (Expr.bop BinOp.uimod e1 e2))
      (fun symEnv =>
        seExprUIModWithConstantDivisor md gconf sconf symEnv specs e1 e2) := by
  intro symEnv hbelow _hvalid espec hspec_eq
  simp only [seExprUIModWithConstantDivisor] at hspec_eq
  cases hB : tryEvalSimpleExprToFFValue symEnv e2 with
  | error msg => rw [hB] at hspec_eq; simp at hspec_eq
  | ok B =>
    rw [hB] at hspec_eq
    simp only [] at hspec_eq
    by_cases hB1 : B.val = 1
    · rw [if_pos hB1] at hspec_eq
      cases hres1 : resolveSimpleExpr symEnv e1 with
      | error msg => rw [hres1] at hspec_eq; simp at hspec_eq
      | ok v =>
          rw [hres1] at hspec_eq
          injection hspec_eq with hspec_eq
          subst hspec_eq
          have hBne0 : B ≠ (0 : FF c) := by
            intro hB0; rw [hB0] at hB1; simp at hB1
          refine ⟨le_refl _, ?_, ?_, ?_, hbelow,
            fun v' hv' => Or.inl hv', ValidBinRep_trivial gconf _ _, ?_, ?_⟩
          · intro v' hv'
            simp only [simpleValVars] at hv'
            exact absurd hv' Std.TreeSet.not_mem_emptyc
          · intro v' hv'
            rcases Std.TreeSet.mem_union_iff.mp hv' with h | h <;>
              simp only [ffVarsOfFormula, bVarsOfFormula] at h <;>
              exact absurd h Std.TreeSet.not_mem_emptyc
          · intro v' hv'
            rcases Std.TreeSet.mem_union_iff.mp hv' with h | h <;>
              simp only [ffVarsOfFormula, bVarsOfFormula] at h <;>
              exact absurd h Std.TreeSet.not_mem_emptyc
          · intro env assignment hmatch val hval
            obtain ⟨val', hval', _hm⟩ :=
              resolveSimpleExpr_correct symEnv e1 env assignment v hmatch hres1
            have hB' := tryEvalSimpleExprToFFValue_correct symEnv e2 env assignment B hmatch hB
            simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval', hB',
              evalUimod, if_neg hBne0, hB1, Nat.mod_one] at hval
            injection hval with hval
            subst hval
            exact ⟨assignment, (fun n _ => rfl), (fun n _ => rfl), (fun n _ => rfl),
              (fun n _ => rfl), by simp only [evalFormula], hmatch, by
                simp [simpleValMatches]⟩
          · intro env assignment hmatch assignment' hagree _heval
            refine ⟨0, ?_, EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env
              hagree hmatch, by simp [simpleValMatches]⟩
            obtain ⟨val, hval, _hm⟩ :=
              resolveSimpleExpr_correct symEnv e1 env assignment v hmatch hres1
            have hB' := tryEvalSimpleExprToFFValue_correct symEnv e2 env assignment B hmatch hB
            simp [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval, hB',
              evalUimod, if_neg hBne0, hB1, Nat.mod_one]
    · rw [if_neg hB1] at hspec_eq
      by_cases hBrange : 1 < B.val ∧ B.val < c.midpoint
      · have hcond : (B.val > 1 && B.val < c.midpoint) = true := by
          simp only [Bool.and_eq_true, decide_eq_true_eq, gt_iff_lt]
          exact hBrange
        simp only [hcond, if_true] at hspec_eq
        cases hres1 : resolveSimpleExpr symEnv e1 with
        | error msg => rw [hres1] at hspec_eq; simp at hspec_eq
        | ok A =>
            rw [hres1] at hspec_eq
            simp only [uiDivModGadget] at hspec_eq
            injection hspec_eq with hspec_eq
            subst hspec_eq
            obtain ⟨hB2, hBmid⟩ := hBrange
            have hsubA := Corellzk2smt.SymExec.Correctness.Lemmas.resolveSimpleExpr_vars_subset
              symEnv e1 A hres1
            have hBne0 : B ≠ (0 : FF c) := by
              intro hB0; rw [hB0] at hB2; simp at hB2
            have h2mid := two_mul_midpoint_eq B.val hB2 hBmid
            have hlow_nowrap := uidiv_low_no_wrap B.val hB2 hBmid
            have hhigh_nowrap := uidiv_high_no_wrap B.val hB2 hBmid
            have hmemQeqn : Var.ffv sconf.nextVarId ∈
                ffVarsOfFormula (FFFormula.eq (simpleSymValToTerm A)
                  (FFTerm.add (FFTerm.mul (FFTerm.var sconf.nextVarId) (FFTerm.val B))
                    (FFTerm.var (sconf.nextVarId + 1)))) := by
              simp only [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_union_iff]
              exact Or.inr (Or.inl (Or.inl (Std.TreeSet.mem_insert_self ..)))
            have hmemReqn : Var.ffv (sconf.nextVarId + 1) ∈
                ffVarsOfFormula (FFFormula.eq (simpleSymValToTerm A)
                  (FFTerm.add (FFTerm.mul (FFTerm.var sconf.nextVarId) (FFTerm.val B))
                    (FFTerm.var (sconf.nextVarId + 1)))) := by
              simp only [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_union_iff]
              exact Or.inr (Or.inr (Std.TreeSet.mem_insert_self ..))
            have hffdisj : ∀ (l u : FF c) (v' : Var), v' ∈ ffVarsOfFormula (FFFormula.and
                (FFFormula.eq (simpleSymValToTerm A)
                  (FFTerm.add (FFTerm.mul (FFTerm.var sconf.nextVarId) (FFTerm.val B))
                    (FFTerm.var (sconf.nextVarId + 1))))
                (FFFormula.and
                  (FFFormula.range (FFTerm.var (sconf.nextVarId + 1)) 0 (B.val - 1 : FF c))
                  (FFFormula.range (FFTerm.var sconf.nextVarId) l u))) →
                v' = Var.ffv sconf.nextVarId ∨ v' = Var.ffv (sconf.nextVarId + 1) ∨
                  v' ∈ simpleValOwnVars A := by
              intro l u v' hv'
              simp only [ffVarsOfFormula, ffVarsOfTerm, ffVarsOfTerm_simpleSymValToTerm,
                Std.TreeSet.mem_union_iff] at hv'
              rcases hv' with (hA | (hQ | hE) | hR) | (hR2 | hQ2)
              · exact Or.inr (Or.inr hA)
              · rcases Std.TreeSet.mem_insert.mp hQ with heq | hmem
                · exact Or.inl (Var_compare_eq_iff_eq.mp heq).symm
                · exact absurd hmem Std.TreeSet.not_mem_emptyc
              · exact absurd hE Std.TreeSet.not_mem_emptyc
              · rcases Std.TreeSet.mem_insert.mp hR with heq | hmem
                · exact Or.inr (Or.inl (Var_compare_eq_iff_eq.mp heq).symm)
                · exact absurd hmem Std.TreeSet.not_mem_emptyc
              · rcases Std.TreeSet.mem_insert.mp hR2 with heq | hmem
                · exact Or.inr (Or.inl (Var_compare_eq_iff_eq.mp heq).symm)
                · exact absurd hmem Std.TreeSet.not_mem_emptyc
              · rcases Std.TreeSet.mem_insert.mp hQ2 with heq | hmem
                · exact Or.inl (Var_compare_eq_iff_eq.mp heq).symm
                · exact absurd hmem Std.TreeSet.not_mem_emptyc
            have hbdisj : ∀ (l u : FF c) (v' : Var), v' ∈ bVarsOfFormula (FFFormula.and
                (FFFormula.eq (simpleSymValToTerm A)
                  (FFTerm.add (FFTerm.mul (FFTerm.var sconf.nextVarId) (FFTerm.val B))
                    (FFTerm.var (sconf.nextVarId + 1))))
                (FFFormula.and
                  (FFFormula.range (FFTerm.var (sconf.nextVarId + 1)) 0 (B.val - 1 : FF c))
                  (FFFormula.range (FFTerm.var sconf.nextVarId) l u))) → False := by
              intro l u v' hv'
              simp only [bVarsOfFormula, bVarsOfTerm, bVarsOfTerm_simpleSymValToTerm,
                Std.TreeSet.mem_union_iff] at hv'
              rcases hv' with (h | (h | h) | h) | (h | h) <;>
                exact absurd h Std.TreeSet.not_mem_emptyc
            have hmemQ_f : Var.ffv sconf.nextVarId ∈
                ffVarsOfFormula (FFFormula.ite
                  (FFFormula.range (simpleSymValToTerm A) 0 (c.midpoint - 1 : FF c))
                  (FFFormula.and (FFFormula.eq (simpleSymValToTerm A)
                      (FFTerm.add (FFTerm.mul (FFTerm.var sconf.nextVarId) (FFTerm.val B))
                        (FFTerm.var (sconf.nextVarId + 1))))
                    (FFFormula.and
                      (FFFormula.range (FFTerm.var (sconf.nextVarId + 1)) 0 (B.val - 1 : FF c))
                      (FFFormula.range (FFTerm.var sconf.nextVarId) 0
                        (((c.midpoint - 1) / B.val : Nat) : FF c))))
                  (FFFormula.and (FFFormula.eq (simpleSymValToTerm A)
                      (FFTerm.add (FFTerm.mul (FFTerm.var sconf.nextVarId) (FFTerm.val B))
                        (FFTerm.var (sconf.nextVarId + 1))))
                    (FFFormula.and
                      (FFFormula.range (FFTerm.var (sconf.nextVarId + 1)) 0 (B.val - 1 : FF c))
                      (FFFormula.range (FFTerm.var sconf.nextVarId)
                        ((c.midpoint / B.val : Nat) : FF c)
                        (((c.p - 1) / B.val : Nat) : FF c))))) :=
              Std.TreeSet.mem_union_of_left
                (Std.TreeSet.mem_union_of_right (Std.TreeSet.mem_union_of_left hmemQeqn))
            have hmemR_f : Var.ffv (sconf.nextVarId + 1) ∈
                ffVarsOfFormula (FFFormula.ite
                  (FFFormula.range (simpleSymValToTerm A) 0 (c.midpoint - 1 : FF c))
                  (FFFormula.and (FFFormula.eq (simpleSymValToTerm A)
                      (FFTerm.add (FFTerm.mul (FFTerm.var sconf.nextVarId) (FFTerm.val B))
                        (FFTerm.var (sconf.nextVarId + 1))))
                    (FFFormula.and
                      (FFFormula.range (FFTerm.var (sconf.nextVarId + 1)) 0 (B.val - 1 : FF c))
                      (FFFormula.range (FFTerm.var sconf.nextVarId) 0
                        (((c.midpoint - 1) / B.val : Nat) : FF c))))
                  (FFFormula.and (FFFormula.eq (simpleSymValToTerm A)
                      (FFTerm.add (FFTerm.mul (FFTerm.var sconf.nextVarId) (FFTerm.val B))
                        (FFTerm.var (sconf.nextVarId + 1))))
                    (FFFormula.and
                      (FFFormula.range (FFTerm.var (sconf.nextVarId + 1)) 0 (B.val - 1 : FF c))
                      (FFFormula.range (FFTerm.var sconf.nextVarId)
                        ((c.midpoint / B.val : Nat) : FF c)
                        (((c.p - 1) / B.val : Nat) : FF c))))) :=
              Std.TreeSet.mem_union_of_left
                (Std.TreeSet.mem_union_of_right (Std.TreeSet.mem_union_of_left hmemReqn))
            set isLowExpr : FFFormula c :=
              FFFormula.range (simpleSymValToTerm A) 0 (c.midpoint - 1 : FF c)
              with hisLowExpr_def
            set eqnExpr : FFFormula c := FFFormula.eq (simpleSymValToTerm A)
                (FFTerm.add (FFTerm.mul (FFTerm.var sconf.nextVarId) (FFTerm.val B))
                  (FFTerm.var (sconf.nextVarId + 1)))
              with heqnExpr_def
            set rRangeExpr : FFFormula c :=
              FFFormula.range (FFTerm.var (sconf.nextVarId + 1)) 0 (B.val - 1 : FF c)
              with hrRangeExpr_def
            set qLowExpr : FFFormula c :=
              FFFormula.range (FFTerm.var sconf.nextVarId) 0
                (((c.midpoint - 1) / B.val : Nat) : FF c)
              with hqLowExpr_def
            set qHighExpr : FFFormula c :=
              FFFormula.range (FFTerm.var sconf.nextVarId) ((c.midpoint / B.val : Nat) : FF c)
                (((c.p - 1) / B.val : Nat) : FF c)
              with hqHighExpr_def
            set lowBranchExpr : FFFormula c :=
              FFFormula.and eqnExpr (FFFormula.and rRangeExpr qLowExpr) with hlowBranchExpr_def
            set highBranchExpr : FFFormula c :=
              FFFormula.and eqnExpr (FFFormula.and rRangeExpr qHighExpr) with hhighBranchExpr_def
            set fExpr : FFFormula c := FFFormula.ite isLowExpr lowBranchExpr highBranchExpr
              with hfExpr_def
            refine ⟨Nat.le_add_right sconf.nextVarId 2, ?_, ?_, ?_,
              varSetBelow_mono (Nat.le_add_right sconf.nextVarId 2) hbelow,
              fun v' hv' => Or.inl hv', ValidBinRep_trivial gconf _ _, ?_, ?_⟩
            · intro v' hv'
              simp only [simpleValVars, simpleValOwnVars, Option.map_none, Option.getD_none,
                Std.TreeSet.mem_union_iff] at hv'
              rcases hv' with h | h
              · rcases Std.TreeSet.mem_insert.mp h with heq | hmem
                · rw [← Var_compare_eq_iff_eq.mp heq]
                  exact Or.inr (Std.TreeSet.mem_union_of_left hmemR_f)
                · exact absurd hmem Std.TreeSet.not_mem_emptyc
              · exact absurd h Std.TreeSet.not_mem_emptyc
            · intro v' hv'
              simp only [exprSpecVars] at hv'
              rcases Std.TreeSet.mem_union_iff.mp hv' with hff | hb
              · simp only [hfExpr_def, ffVarsOfFormula, Std.TreeSet.mem_union_iff] at hff
                rcases hff with hff' | hhigh
                · rcases hff' with hisLow | hlow
                  · rw [hisLowExpr_def, ffVarsOfFormula, ffVarsOfTerm_simpleSymValToTerm] at hisLow
                    exact Or.inl (hsubA v' (simpleValOwnVars_subset_simpleValVars A v' hisLow))
                  · rcases hffdisj 0 (((c.midpoint - 1) / B.val : Nat) : FF c) v' hlow with
                      heq | heq | h
                    · rw [heq]; exact Or.inr (le_refl _)
                    · rw [heq]; refine Or.inr ?_; simp only [varIndex]; omega
                    · exact Or.inl (hsubA v' (simpleValOwnVars_subset_simpleValVars A v' h))
                · rcases hffdisj ((c.midpoint / B.val : Nat) : FF c)
                    (((c.p - 1) / B.val : Nat) : FF c) v' hhigh with heq | heq | h
                  · rw [heq]; exact Or.inr (le_refl _)
                  · rw [heq]; refine Or.inr ?_; simp only [varIndex]; omega
                  · exact Or.inl (hsubA v' (simpleValOwnVars_subset_simpleValVars A v' h))
              · exfalso
                simp only [hfExpr_def, bVarsOfFormula, Std.TreeSet.mem_union_iff] at hb
                rcases hb with hb' | hbhigh
                · rcases hb' with hbisLow | hblow
                  · rw [hisLowExpr_def, bVarsOfFormula, bVarsOfTerm_simpleSymValToTerm] at hbisLow
                    exact absurd hbisLow Std.TreeSet.not_mem_emptyc
                  · exact hbdisj 0 (((c.midpoint - 1) / B.val : Nat) : FF c) v' hblow
                · exact hbdisj ((c.midpoint / B.val : Nat) : FF c)
                    (((c.p - 1) / B.val : Nat) : FF c) v' hbhigh
            · intro v' hv'
              simp only [exprSpecVars] at hv'
              rcases Std.TreeSet.mem_union_iff.mp hv' with hff | hb
              · simp only [hfExpr_def, ffVarsOfFormula, Std.TreeSet.mem_union_iff] at hff
                rcases hff with hff' | hhigh
                · rcases hff' with hisLow | hlow
                  · rw [hisLowExpr_def, ffVarsOfFormula, ffVarsOfTerm_simpleSymValToTerm] at hisLow
                    exact lt_of_lt_of_le
                      (hbelow v' (hsubA v' (simpleValOwnVars_subset_simpleValVars A v' hisLow)))
                      (Nat.le_add_right sconf.nextVarId 2)
                  · rcases hffdisj 0 (((c.midpoint - 1) / B.val : Nat) : FF c) v' hlow with
                      heq | heq | h
                    · rw [heq]; simp only [varIndex]; omega
                    · rw [heq]; simp only [varIndex]; omega
                    · exact lt_of_lt_of_le
                        (hbelow v' (hsubA v' (simpleValOwnVars_subset_simpleValVars A v' h)))
                        (Nat.le_add_right sconf.nextVarId 2)
                · rcases hffdisj ((c.midpoint / B.val : Nat) : FF c)
                    (((c.p - 1) / B.val : Nat) : FF c) v' hhigh with heq | heq | h
                  · rw [heq]; simp only [varIndex]; omega
                  · rw [heq]; simp only [varIndex]; omega
                  · exact lt_of_lt_of_le
                      (hbelow v' (hsubA v' (simpleValOwnVars_subset_simpleValVars A v' h)))
                      (Nat.le_add_right sconf.nextVarId 2)
              · exfalso
                simp only [hfExpr_def, bVarsOfFormula, Std.TreeSet.mem_union_iff] at hb
                rcases hb with hb' | hbhigh
                · rcases hb' with hbisLow | hblow
                  · rw [hisLowExpr_def, bVarsOfFormula, bVarsOfTerm_simpleSymValToTerm] at hbisLow
                    exact absurd hbisLow Std.TreeSet.not_mem_emptyc
                  · exact hbdisj 0 (((c.midpoint - 1) / B.val : Nat) : FF c) v' hblow
                · exact hbdisj ((c.midpoint / B.val : Nat) : FF c)
                    (((c.p - 1) / B.val : Nat) : FF c) v' hbhigh
            · intro env assignment hmatch val hval
              obtain ⟨Aval, hAval, hmA⟩ :=
                resolveSimpleExpr_correct symEnv e1 env assignment A hmatch hres1
              have hB' := tryEvalSimpleExprToFFValue_correct symEnv e2 env assignment B hmatch hB
              simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hAval, hB',
                evalUimod, if_neg hBne0] at hval
              injection hval with hval
              set assignment' : Assignment c :=
                { assignment with
                  ff := fun n => if n = sconf.nextVarId then ((Aval.val / B.val : Nat) : FF c)
                    else if n = sconf.nextVarId + 1 then ((Aval.val % B.val : Nat) : FF c)
                    else assignment.ff n }
                with hassignment'_def
              have hagreeff : agreesOnFF (symEnvVars symEnv) assignment assignment' := by
                intro n hn
                have hne1 : n ≠ sconf.nextVarId := Nat.ne_of_lt (hbelow (Var.ffv n) hn)
                have hne2 : n ≠ sconf.nextVarId + 1 := by
                  have h : n < sconf.nextVarId := by
                    have h' := hbelow (Var.ffv n) hn
                    simpa only [varIndex] using h'
                  exact Nat.ne_of_lt (lt_trans h (Nat.lt_succ_self _))
                simp only [hassignment'_def, if_neg hne1, if_neg hne2]
              have hagreebool : agreesOnBool (symEnvVars symEnv) assignment assignment' :=
                fun n _ => rfl
              have hframeff : ∀ n, Var.ffv n ∉ (ffVarsOfFormula fExpr ∪ bVarsOfFormula fExpr) →
                  assignment'.ff n = assignment.ff n := by
                intro n hn
                have hne1 : n ≠ sconf.nextVarId := by
                  intro heqn; apply hn; rw [heqn]
                  exact Std.TreeSet.mem_union_of_left hmemQ_f
                have hne2 : n ≠ sconf.nextVarId + 1 := by
                  intro heqn; apply hn; rw [heqn]
                  exact Std.TreeSet.mem_union_of_left hmemR_f
                simp only [hassignment'_def, if_neg hne1, if_neg hne2]
              have hframebool : ∀ n, Var.boolv n ∉ (ffVarsOfFormula fExpr ∪ bVarsOfFormula fExpr) →
                  assignment'.bool n = assignment.bool n := fun n _ => rfl
              have hAterm_eval : evalTerm gconf assignment' (simpleSymValToTerm A)
                  (specs.map (·.f)) = Except.ok Aval := by
                have hmA' : simpleValMatches assignment' A Aval :=
                  simpleValMatches_agreesOnFF_preserves assignment assignment' A Aval
                    (symEnvVars symEnv) hsubA hagreeff hmA
                exact evalTerm_simpleSymValToTerm gconf assignment' A Aval (specs.map (·.f)) hmA'
              have hqeval : assignment'.ff sconf.nextVarId = ((Aval.val / B.val : Nat) : FF c) := by
                simp [hassignment'_def]
              have hreval : assignment'.ff (sconf.nextVarId + 1)
                  = ((Aval.val % B.val : Nat) : FF c) := by
                simp [hassignment'_def]
              have heqn_true : evalFormula gconf assignment' eqnExpr (specs.map (·.f))
                  = Except.ok true := by
                rw [heqnExpr_def]
                simp only [evalFormula, evalTerm, hAterm_eval, hqeval, hreval]
                rw [cast_div_add_mod_eq' Aval.val B, ZMod.natCast_rightInverse Aval]
                simp
              have hrRange_true : evalFormula gconf assignment' rRangeExpr (specs.map (·.f))
                  = Except.ok true := by
                rw [hrRangeExpr_def]
                rw [evalFormula_range_iff gconf assignment' (specs.map (·.f))
                  (FFTerm.var (sconf.nextVarId + 1)) 0 (B.val - 1 : FF c)
                  (((Aval.val % B.val : Nat) : FF c)) (by simp only [evalTerm, hreval])]
                have h0 : toSigned (0 : FF c) = 0 := by
                  have : (0 : FF c) = ((0 : Nat) : FF c) := by norm_num
                  rw [this, toSigned_natCast_of_lt 0 (by have := c.p_prime.two_le; omega)
                    (by omega)]
                  simp
                have hB1 : toSigned (B.val - 1 : FF c) = ((B.val - 1 : Nat) : Int) := by
                  rw [cast_sub_one_eq B.val (by omega),
                    toSigned_natCast_of_lt (B.val - 1) (by omega) (by omega)]
                have hRmod : toSigned (((Aval.val % B.val : Nat) : FF c))
                    = ((Aval.val % B.val : Nat) : Int) :=
                  toSigned_natCast_of_lt (Aval.val % B.val)
                    (by have := Nat.mod_lt Aval.val (show 0 < B.val by omega); omega)
                    (by have := Nat.mod_lt Aval.val (show 0 < B.val by omega); omega)
                rw [h0, hB1, hRmod]
                constructor
                · exact Int.ofNat_nonneg _
                · have := Nat.mod_lt Aval.val (show 0 < B.val by omega)
                  exact_mod_cast (by omega : Aval.val % B.val ≤ B.val - 1)
              refine ⟨assignment', hagreeff, hagreebool, hframeff, hframebool, ?_,
                EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagreeff hmatch,
                ?_⟩
              · rw [hfExpr_def]
                by_cases hAlow : Aval.val < c.midpoint
                · have hisLow_true : evalFormula gconf assignment' isLowExpr (specs.map (·.f))
                      = Except.ok true := by
                    rw [hisLowExpr_def]
                    rw [evalFormula_range_iff gconf assignment' (specs.map (·.f))
                      (simpleSymValToTerm A) 0 (c.midpoint - 1 : FF c) Aval hAterm_eval]
                    have h0 : toSigned (0 : FF c) = 0 := by
                      have : (0 : FF c) = ((0 : Nat) : FF c) := by norm_num
                      rw [this, toSigned_natCast_of_lt 0 (by have := c.p_prime.two_le; omega)
                        (by omega)]
                      simp
                    have hmid1 : toSigned (c.midpoint - 1 : FF c)
                        = ((c.midpoint - 1 : Nat) : Int) := by
                      rw [cast_sub_one_eq c.midpoint (by omega),
                        toSigned_natCast_of_lt (c.midpoint - 1) (by omega) (by omega)]
                    rw [h0, hmid1, toSigned_of_val_lt_midpoint Aval hAlow]
                    exact ⟨Int.ofNat_nonneg _, by exact_mod_cast (by omega : Aval.val ≤
                      c.midpoint - 1)⟩
                  have hqLow_true : evalFormula gconf assignment' qLowExpr (specs.map (·.f))
                      = Except.ok true := by
                    rw [hqLowExpr_def]
                    rw [evalFormula_range_iff gconf assignment' (specs.map (·.f))
                      (FFTerm.var sconf.nextVarId) 0 (((c.midpoint - 1) / B.val : Nat) : FF c)
                      (((Aval.val / B.val : Nat) : FF c)) (by simp only [evalTerm, hqeval])]
                    have h0 : toSigned (0 : FF c) = 0 := by
                      have : (0 : FF c) = ((0 : Nat) : FF c) := by norm_num
                      rw [this, toSigned_natCast_of_lt 0 (by have := c.p_prime.two_le; omega)
                        (by omega)]
                      simp
                    have hqLowBound := uidiv_qLow_bound B.val hB2 hBmid
                    have huLo : toSigned (((c.midpoint - 1) / B.val : Nat) : FF c)
                        = (((c.midpoint - 1) / B.val : Nat) : Int) :=
                      toSigned_natCast_of_lt _ (by omega) hqLowBound
                    have hQdvd : Aval.val / B.val ≤ (c.midpoint - 1) / B.val :=
                      Nat.div_le_div_right (by omega)
                    have hQval : toSigned (((Aval.val / B.val : Nat) : FF c))
                        = ((Aval.val / B.val : Nat) : Int) :=
                      toSigned_natCast_of_lt _ (by omega) (by omega)
                    rw [h0, huLo, hQval]
                    exact ⟨Int.ofNat_nonneg _, by exact_mod_cast hQdvd⟩
                  refine evalFormula_ite_true gconf assignment' (specs.map (·.f)) isLowExpr
                    lowBranchExpr highBranchExpr hisLow_true ?_
                  rw [hlowBranchExpr_def]
                  exact evalFormula_and_intro gconf assignment' (specs.map (·.f)) eqnExpr
                    (FFFormula.and rRangeExpr qLowExpr) heqn_true
                    (evalFormula_and_intro gconf assignment' (specs.map (·.f)) rRangeExpr qLowExpr
                      hrRange_true hqLow_true)
                · have hisLow_false : evalFormula gconf assignment' isLowExpr (specs.map (·.f))
                      = Except.ok false := by
                    rw [hisLowExpr_def]
                    have hiff := evalFormula_range_iff gconf assignment' (specs.map (·.f))
                      (simpleSymValToTerm A) 0 (c.midpoint - 1 : FF c) Aval hAterm_eval
                    cases hres : evalFormula gconf assignment'
                        (FFFormula.range (simpleSymValToTerm A) 0 (c.midpoint - 1 : FF c))
                        (specs.map (·.f)) with
                    | error msg =>
                        simp [evalFormula, hAterm_eval] at hres
                    | ok b =>
                        cases b with
                        | true =>
                            exfalso
                            have h0 : toSigned (0 : FF c) = 0 := by
                              have : (0 : FF c) = ((0 : Nat) : FF c) := by norm_num
                              rw [this, toSigned_natCast_of_lt 0
                                (by have := c.p_prime.two_le; omega) (by omega)]
                              simp
                            have hmid1 : toSigned (c.midpoint - 1 : FF c)
                                = ((c.midpoint - 1 : Nat) : Int) := by
                              rw [cast_sub_one_eq c.midpoint (by omega),
                                toSigned_natCast_of_lt (c.midpoint - 1) (by omega) (by omega)]
                            have := hiff.mp hres
                            rw [hmid1] at this
                            have hAvalSigned : c.midpoint ≤ Aval.val := by omega
                            have : toSigned Aval < 0 := by
                              simp only [Corellzk2smt.Language.Core.Semantics.Basic.toSigned,
                                if_neg (by omega : ¬ Aval.val < c.midpoint)]
                              have := ZMod.val_lt Aval
                              omega
                            omega
                        | false => rfl
                  have hqHigh_true : evalFormula gconf assignment' qHighExpr (specs.map (·.f))
                      = Except.ok true := by
                    rw [hqHighExpr_def]
                    rw [evalFormula_range_iff gconf assignment' (specs.map (·.f))
                      (FFTerm.var sconf.nextVarId) ((c.midpoint / B.val : Nat) : FF c)
                      (((c.p - 1) / B.val : Nat) : FF c) (((Aval.val / B.val : Nat) : FF c))
                      (by simp only [evalTerm, hqeval])]
                    have hqHighLoBound := uidiv_qHighLo_bound B.val hB2 hBmid
                    have hqHighHiBound := uidiv_qHighHi_bound B.val hB2 hBmid
                    have hlo : toSigned ((c.midpoint / B.val : Nat) : FF c)
                        = ((c.midpoint / B.val : Nat) : Int) :=
                      toSigned_natCast_of_lt _ (by omega) hqHighLoBound
                    have hhi : toSigned (((c.p - 1) / B.val : Nat) : FF c)
                        = (((c.p - 1) / B.val : Nat) : Int) :=
                      toSigned_natCast_of_lt _ (by omega) hqHighHiBound
                    have hAvalLtP := ZMod.val_lt Aval
                    have hAvalB_le_hi : Aval.val / B.val ≤ (c.p - 1) / B.val :=
                      Nat.div_le_div_right (by omega)
                    have hAvalB_ge_lo : c.midpoint / B.val ≤ Aval.val / B.val :=
                      Nat.div_le_div_right (by omega)
                    have hQval : toSigned (((Aval.val / B.val : Nat) : FF c))
                        = ((Aval.val / B.val : Nat) : Int) :=
                      toSigned_natCast_of_lt _ (by omega) (by omega)
                    rw [hlo, hhi, hQval]
                    exact ⟨by exact_mod_cast hAvalB_ge_lo, by exact_mod_cast hAvalB_le_hi⟩
                  refine evalFormula_ite_false gconf assignment' (specs.map (·.f)) isLowExpr
                    lowBranchExpr highBranchExpr hisLow_false ?_
                  rw [hhighBranchExpr_def]
                  exact evalFormula_and_intro gconf assignment' (specs.map (·.f)) eqnExpr
                    (FFFormula.and rRangeExpr qHighExpr) heqn_true
                    (evalFormula_and_intro gconf assignment' (specs.map (·.f)) rRangeExpr qHighExpr
                      hrRange_true hqHigh_true)
              · simp only [simpleValMatches, hreval]
                exact hval
            · intro env assignment hmatch assignment' hagree heval_f
              have hmatch' : EnvMatches assignment' symEnv env :=
                EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagree hmatch
              obtain ⟨Aval, hAval, hmA'⟩ :=
                resolveSimpleExpr_correct symEnv e1 env assignment' A hmatch' hres1
              have hB' := tryEvalSimpleExprToFFValue_correct symEnv e2 env assignment' B hmatch'
                hB
              have hAterm_eval : evalTerm gconf assignment' (simpleSymValToTerm A)
                  (specs.map (·.f)) = Except.ok Aval :=
                evalTerm_simpleSymValToTerm gconf assignment' A Aval (specs.map (·.f)) hmA'
              have hrange_extract : ∀ (t : FFVar) (lo hi tval : FF c),
                  lo.val < c.midpoint → hi.val < c.midpoint → assignment'.ff t = tval →
                  evalFormula gconf assignment'
                      (FFFormula.range (FFTerm.var t) lo hi)
                      (specs.map (·.f)) = Except.ok true →
                  lo.val ≤ tval.val ∧ tval.val ≤ hi.val := by
                intro t lo hi tval hlo hhi htval heval
                have hEvalT : evalTerm gconf assignment' (FFTerm.var t) (specs.map (·.f))
                    = Except.ok tval := by simp only [evalTerm, htval]
                rw [evalFormula_range_iff gconf assignment' (specs.map (·.f)) (FFTerm.var t)
                  lo hi tval hEvalT] at heval
                have hlo_signed : toSigned lo = (lo.val : Int) := toSigned_of_val_lt_midpoint lo hlo
                have hhi_signed : toSigned hi = (hi.val : Int) := toSigned_of_val_lt_midpoint hi hhi
                rw [hlo_signed, hhi_signed] at heval
                have htval_lt_mid : tval.val < c.midpoint := by
                  by_contra hcon
                  push_neg at hcon
                  have hneg : toSigned tval < 0 := by
                    simp only [Corellzk2smt.Language.Core.Semantics.Basic.toSigned,
                      if_neg (show ¬tval.val < c.midpoint by omega)]
                    have := ZMod.val_lt tval
                    omega
                  have hlo_nonneg : (0:Int) ≤ (lo.val:Int) := by exact_mod_cast Nat.zero_le lo.val
                  omega
                rw [toSigned_of_val_lt_midpoint tval htval_lt_mid] at heval
                exact ⟨by exact_mod_cast heval.1, by exact_mod_cast heval.2⟩
              have hzero_eq : (0 : FF c).val = 0 := ZMod.val_zero
              have hzero_bound : (0 : FF c).val < c.midpoint := by
                rw [hzero_eq]; have := c.p_prime.two_le; omega
              have hRupper_eq : (B.val - 1 : FF c).val = B.val - 1 := by
                rw [cast_sub_one_eq B.val (by omega), val_natCast_eq]
                exact Nat.mod_eq_of_lt (by omega)
              have hRupper_bound : (B.val - 1 : FF c).val < c.midpoint := by
                rw [hRupper_eq]; omega
              rw [hfExpr_def] at heval_f
              set Qfield : FF c := assignment'.ff sconf.nextVarId with hQfield_def
              set Rfield : FF c := assignment'.ff (sconf.nextVarId + 1) with hRfield_def
              have hrhs_eval : evalTerm gconf assignment'
                  (FFTerm.add (FFTerm.mul (FFTerm.var sconf.nextVarId) (FFTerm.val B))
                    (FFTerm.var (sconf.nextVarId + 1))) (specs.map (·.f))
                  = Except.ok (Qfield * B + Rfield) := by
                simp only [evalTerm, hQfield_def, hRfield_def]
              cases hisLow_eval : evalFormula gconf assignment' isLowExpr (specs.map (·.f)) with
              | error msg =>
                  rw [hisLowExpr_def] at hisLow_eval
                  simp [evalFormula, hAterm_eval] at hisLow_eval
              | ok b =>
                  simp only [evalFormula, hisLow_eval] at heval_f
                  cases b with
                  | true =>
                      simp only [if_true] at heval_f
                      rw [hlowBranchExpr_def] at heval_f
                      obtain ⟨heqn, hrest⟩ :=
                        evalFormula_and_elim gconf assignment' (specs.map (·.f)) eqnExpr
                          (FFFormula.and rRangeExpr qLowExpr) heval_f
                      obtain ⟨hrR, hqR⟩ :=
                        evalFormula_and_elim gconf assignment' (specs.map (·.f)) rRangeExpr
                          qLowExpr hrest
                      have hRbound := hrange_extract (sconf.nextVarId + 1) 0 (B.val - 1 : FF c)
                        Rfield hzero_bound hRupper_bound rfl
                        (by rw [← hrRangeExpr_def]; exact hrR)
                      rw [hzero_eq, hRupper_eq] at hRbound
                      have hqLow_eq : (((c.midpoint - 1) / B.val : Nat) : FF c).val
                          = (c.midpoint - 1) / B.val := by
                        rw [val_natCast_eq]
                        exact Nat.mod_eq_of_lt (by
                          have := uidiv_qLow_bound B.val hB2 hBmid; omega)
                      have hqLowUpper : (((c.midpoint - 1) / B.val : Nat) : FF c).val
                          < c.midpoint := by
                        rw [hqLow_eq]; exact uidiv_qLow_bound B.val hB2 hBmid
                      have hQbound := hrange_extract sconf.nextVarId 0
                        (((c.midpoint - 1) / B.val : Nat) : FF c) Qfield hzero_bound hqLowUpper
                        rfl (by rw [← hqLowExpr_def]; exact hqR)
                      rw [hzero_eq, hqLow_eq] at hQbound
                      have heqn_field : Aval = Qfield * B + Rfield := by
                        rw [heqnExpr_def] at heqn
                        exact (evalFormula_eq_iff gconf assignment' (specs.map (·.f))
                          (simpleSymValToTerm A) _ Aval (Qfield * B + Rfield) hAterm_eval
                          hrhs_eval).mp heqn
                      have hmul : Qfield.val * B.val ≤ (c.midpoint - 1) / B.val * B.val :=
                        Nat.mul_le_mul_right B.val hQbound.2
                      have hSlt2p : Qfield.val * B.val + Rfield.val < 2 * c.p := by omega
                      have hSeq : Qfield.val * B.val + Rfield.val = Aval.val :=
                        QBR_val_eq_of_no_wrap Qfield B Rfield Aval heqn_field hSlt2p
                          (fun hge => absurd hge (by omega))
                      obtain ⟨hQeq, hReq⟩ := nat_eq_div_mod_of_eq (show 0 < B.val by omega)
                        hSeq (by omega)
                      have hRfield_eq : Rfield = ((Aval.val % B.val : Nat) : FF c) := by
                        have hround : ((Rfield.val : Nat) : FF c) = Rfield :=
                          ZMod.natCast_rightInverse Rfield
                        rw [← hReq] at hround
                        exact hround.symm
                      refine ⟨Rfield, ?_, hmatch', ?_⟩
                      · simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hAval,
                          hB', evalUimod, if_neg hBne0]
                        rw [hRfield_eq]
                      · simp only [simpleValMatches]
                        exact hRfield_def.symm
                  | false =>
                      simp only [Bool.false_eq_true, if_false] at heval_f
                      rw [hhighBranchExpr_def] at heval_f
                      obtain ⟨heqn, hrest⟩ :=
                        evalFormula_and_elim gconf assignment' (specs.map (·.f)) eqnExpr
                          (FFFormula.and rRangeExpr qHighExpr) heval_f
                      obtain ⟨hrR, hqR⟩ :=
                        evalFormula_and_elim gconf assignment' (specs.map (·.f)) rRangeExpr
                          qHighExpr hrest
                      have hRbound := hrange_extract (sconf.nextVarId + 1) 0 (B.val - 1 : FF c)
                        Rfield hzero_bound hRupper_bound rfl
                        (by rw [← hrRangeExpr_def]; exact hrR)
                      rw [hzero_eq, hRupper_eq] at hRbound
                      have hqHighLo_eq : ((c.midpoint / B.val : Nat) : FF c).val
                          = c.midpoint / B.val := by
                        rw [val_natCast_eq]
                        exact Nat.mod_eq_of_lt (by
                          have := uidiv_qHighLo_bound B.val hB2 hBmid; omega)
                      have hqHighLoUpper : ((c.midpoint / B.val : Nat) : FF c).val
                          < c.midpoint := by
                        rw [hqHighLo_eq]; exact uidiv_qHighLo_bound B.val hB2 hBmid
                      have hqHighHi_eq : (((c.p - 1) / B.val : Nat) : FF c).val
                          = (c.p - 1) / B.val := by
                        rw [val_natCast_eq]
                        exact Nat.mod_eq_of_lt (by
                          have := uidiv_qHighHi_bound B.val hB2 hBmid; omega)
                      have hqHighHiUpper : (((c.p - 1) / B.val : Nat) : FF c).val
                          < c.midpoint := by
                        rw [hqHighHi_eq]; exact uidiv_qHighHi_bound B.val hB2 hBmid
                      have hQbound := hrange_extract sconf.nextVarId
                        ((c.midpoint / B.val : Nat) : FF c) (((c.p - 1) / B.val : Nat) : FF c)
                        Qfield hqHighLoUpper hqHighHiUpper rfl
                        (by rw [← hqHighExpr_def]; exact hqR)
                      rw [hqHighLo_eq, hqHighHi_eq] at hQbound
                      have hAval_hi : c.midpoint ≤ Aval.val := by
                        by_contra hcon
                        push_neg at hcon
                        have htrue : evalFormula gconf assignment' isLowExpr (specs.map (·.f))
                            = Except.ok true := by
                          rw [hisLowExpr_def]
                          rw [evalFormula_range_iff gconf assignment' (specs.map (·.f))
                            (simpleSymValToTerm A) 0 (c.midpoint - 1 : FF c) Aval hAterm_eval]
                          have h0 : toSigned (0 : FF c) = 0 := by
                            have : (0 : FF c) = ((0 : Nat) : FF c) := by norm_num
                            rw [this, toSigned_natCast_of_lt 0
                              (by have := c.p_prime.two_le; omega) (by omega)]
                            simp
                          have hmid1 : toSigned (c.midpoint - 1 : FF c)
                              = ((c.midpoint - 1 : Nat) : Int) := by
                            rw [cast_sub_one_eq c.midpoint (by omega),
                              toSigned_natCast_of_lt (c.midpoint - 1) (by omega) (by omega)]
                          rw [h0, hmid1, toSigned_of_val_lt_midpoint Aval hcon]
                          exact ⟨Int.ofNat_nonneg _, by exact_mod_cast
                            (by omega : Aval.val ≤ c.midpoint - 1)⟩
                        rw [htrue] at hisLow_eval
                        simp at hisLow_eval
                      have heqn_field : Aval = Qfield * B + Rfield := by
                        rw [heqnExpr_def] at heqn
                        exact (evalFormula_eq_iff gconf assignment' (specs.map (·.f))
                          (simpleSymValToTerm A) _ Aval (Qfield * B + Rfield) hAterm_eval
                          hrhs_eval).mp heqn
                      have hmul : Qfield.val * B.val ≤ (c.p - 1) / B.val * B.val :=
                        Nat.mul_le_mul_right B.val hQbound.2
                      have hSlt2p : Qfield.val * B.val + Rfield.val < 2 * c.p := by omega
                      have hSeq : Qfield.val * B.val + Rfield.val = Aval.val :=
                        QBR_val_eq_of_no_wrap Qfield B Rfield Aval heqn_field hSlt2p
                          (fun _ => by omega)
                      obtain ⟨hQeq, hReq⟩ := nat_eq_div_mod_of_eq (show 0 < B.val by omega)
                        hSeq (by omega)
                      have hRfield_eq : Rfield = ((Aval.val % B.val : Nat) : FF c) := by
                        have hround : ((Rfield.val : Nat) : FF c) = Rfield :=
                          ZMod.natCast_rightInverse Rfield
                        rw [← hReq] at hround
                        exact hround.symm
                      refine ⟨Rfield, ?_, hmatch', ?_⟩
                      · simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hAval,
                          hB', evalUimod, if_neg hBne0]
                        rw [hRfield_eq]
                      · simp only [simpleValMatches]
                        exact hRfield_def.symm
      · have hcond : (B.val > 1 && B.val < c.midpoint) = false := by
          simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, gt_iff_lt, not_lt]
          omega
        simp only [hcond, if_false] at hspec_eq
        by_cases hBge : B.val ≥ c.midpoint
        · rw [if_pos hBge] at hspec_eq
          sorry
        · exfalso
          rw [if_neg hBge] at hspec_eq
          simp at hspec_eq

theorem seExprUIMod_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD) (e1 e2 : SimpleExpr c) :
    TranslatesExprCorrectly gconf sconf specs ctx
      (fun env => Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env
        (Expr.bop BinOp.uimod e1 e2))
      (fun symEnv => seExprUIMod md gconf sconf symEnv specs e1 e2) := by
  intro symEnv hbelow hvalid espec hspec_eq
  simp only [seExprUIMod] at hspec_eq
  cases hconst : seExprUIModWithConstantDivisor md gconf sconf symEnv specs e1 e2 with
  | ok result =>
      rw [hconst] at hspec_eq
      injection hspec_eq with hspec_eq
      subst hspec_eq
      exact seExprUIModWithConstantDivisor_correct gconf specs sconf ctx md e1 e2 symEnv
        hbelow hvalid result hconst
  | error msg =>
      rw [hconst] at hspec_eq
      simp [seExprUIModWithNonConstantDivisor] at hspec_eq

/-- `seExprNeg` resolves `e1`'s own symbolic value `v`, mints one fresh var tied to it via
    `outVar = -v`, and reports that fresh var as the result -- structurally identical to the
    `mergeSimpleSymVal`-style "mint one fresh var, tie it down with an `.eq` formula" pattern used
    throughout `Lemmas.lean`. Soundness picks a witness assignment that only changes the fresh
    slot (`sconf.nextVarId`) relative to the base one, so every "outside my own footprint" frame
    condition holds by construction (the fresh var is exactly what makes `Var.ffv sconf.nextVarId ∈
    exprSpecVars espec` true, so the implication in each frame clause is vacuous there and
    unaffected everywhere else); completeness runs the same equation backwards via
    `beq_iff_eq`. -/
theorem seExprNeg_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD) (e1 : SimpleExpr c) :
    TranslatesExprCorrectly gconf sconf specs ctx
      (fun env => Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env (Expr.uop UnOp.neg e1))
      (fun symEnv => seExprNeg md gconf sconf symEnv specs e1) := by
  intro symEnv hbelow _hvalid espec hspec_eq
  simp only [seExprNeg] at hspec_eq
  cases hres : resolveSimpleExpr symEnv e1 with
  | error msg => rw [hres] at hspec_eq; simp at hspec_eq
  | ok v =>
      rw [hres] at hspec_eq
      injection hspec_eq with hspec_eq
      subst hspec_eq
      have hsub := Corellzk2smt.SymExec.Correctness.Lemmas.resolveSimpleExpr_vars_subset
        symEnv e1 v hres
      have hmemF : Var.ffv sconf.nextVarId ∈
          ffVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
            (FFTerm.neg (simpleSymValToTerm v))) := by
        simp only [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_union_iff]
        exact Or.inl (Std.TreeSet.mem_insert_self ..)
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
        rcases Std.TreeSet.mem_union_iff.mp hv' with hff | hb
        · simp only [ffVarsOfFormula, ffVarsOfTerm, ffVarsOfTerm_simpleSymValToTerm,
            Std.TreeSet.mem_union_iff] at hff
          rcases hff with h1 | h2
          · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
            · rw [← Var_compare_eq_iff_eq.mp heq]
              exact Or.inr (le_refl _)
            · exact absurd hmem Std.TreeSet.not_mem_emptyc
          · exact Or.inl (hsub v' (simpleValOwnVars_subset_simpleValVars v v' h2))
        · simp only [bVarsOfFormula, bVarsOfTerm, bVarsOfTerm_simpleSymValToTerm,
            Std.TreeSet.mem_union_iff] at hb
          rcases hb with h | h <;> exact absurd h Std.TreeSet.not_mem_emptyc
      · intro v' hv'
        simp only [exprSpecVars] at hv'
        rcases Std.TreeSet.mem_union_iff.mp hv' with hff | hb
        · simp only [ffVarsOfFormula, ffVarsOfTerm, ffVarsOfTerm_simpleSymValToTerm,
            Std.TreeSet.mem_union_iff] at hff
          rcases hff with h1 | h2
          · rcases Std.TreeSet.mem_insert.mp h1 with heq | hmem
            · rw [← Var_compare_eq_iff_eq.mp heq]
              simp only [varIndex]
              omega
            · exact absurd hmem Std.TreeSet.not_mem_emptyc
          · exact lt_of_lt_of_le
              (hbelow v' (hsub v' (simpleValOwnVars_subset_simpleValVars v v' h2)))
              (Nat.le_succ _)
        · simp only [bVarsOfFormula, bVarsOfTerm, bVarsOfTerm_simpleSymValToTerm,
            Std.TreeSet.mem_union_iff] at hb
          rcases hb with h | h <;> exact absurd h Std.TreeSet.not_mem_emptyc
      · intro env assignment hmatch val hval
        obtain ⟨val', hval', hm⟩ :=
          resolveSimpleExpr_correct symEnv e1 env assignment v hmatch hres
        simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval', evalNeg] at hval
        injection hval with hval
        subst hval
        set assignment' : Assignment c :=
          { assignment with ff := fun n => if n = sconf.nextVarId then -val' else assignment.ff n }
          with hassignment'_def
        have hagreeff : agreesOnFF (symEnvVars symEnv) assignment assignment' := by
          intro n hn
          have hne : n ≠ sconf.nextVarId := Nat.ne_of_lt (hbelow (Var.ffv n) hn)
          simp only [hassignment'_def, if_neg hne]
        have hagreebool : agreesOnBool (symEnvVars symEnv) assignment assignment' :=
          fun n _ => rfl
        have hframeff : ∀ n, Var.ffv n ∉
            (ffVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
              (FFTerm.neg (simpleSymValToTerm v))) ∪
             bVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
              (FFTerm.neg (simpleSymValToTerm v)))) →
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
              (FFTerm.neg (simpleSymValToTerm v))) ∪
             bVarsOfFormula (FFFormula.eq (FFTerm.var sconf.nextVarId)
              (FFTerm.neg (simpleSymValToTerm v)))) →
            assignment'.bool n = assignment.bool n := fun n _ => rfl
        have hsimpleMatch' : simpleValMatches assignment' v val' :=
          simpleValMatches_agreesOnFF_preserves assignment assignment' v val' (symEnvVars symEnv)
            hsub hagreeff hm
        have hevalTerm' : evalTerm gconf assignment' (simpleSymValToTerm v) (specs.map (·.f))
            = Except.ok val' :=
          evalTerm_simpleSymValToTerm gconf assignment' v val' (specs.map (·.f)) hsimpleMatch'
        have hffeval : assignment'.ff sconf.nextVarId = -val' := by
          simp [hassignment'_def]
        refine ⟨assignment', hagreeff, hagreebool, hframeff, hframebool, ?_,
          EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagreeff hmatch, ?_⟩
        · simp [evalFormula, evalTerm, hevalTerm', hffeval]
        · simp only [simpleValMatches, hffeval]
      · intro env assignment hmatch assignment' hagree heval_f
        have hmatch' : EnvMatches assignment' symEnv env :=
          EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagree hmatch
        obtain ⟨val', hval', hm'⟩ :=
          resolveSimpleExpr_correct symEnv e1 env assignment' v hmatch' hres
        have hevalTerm' : evalTerm gconf assignment' (simpleSymValToTerm v) (specs.map (·.f))
            = Except.ok val' :=
          evalTerm_simpleSymValToTerm gconf assignment' v val' (specs.map (·.f)) hm'
        simp only [evalFormula, evalTerm, hevalTerm', Except.ok.injEq] at heval_f
        have hffeq : assignment'.ff sconf.nextVarId = -val' := (beq_iff_eq ..).mp heval_f
        refine ⟨-val', ?_, hmatch', ?_⟩
        · simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval', evalNeg]
        · simp only [simpleValMatches, hffeq]

/-- `seExprId` just resolves `e1`'s own symbolic representation (`resolveSimpleExpr`) and passes
    it through unchanged -- no fresh variable minted, no formula content (`f := FFFormula.true`),
    `outSymEnv` untouched. So the witness assignment never needs to change: soundness holds with
    `assignment' := assignment` directly, and completeness transports `resolveSimpleExpr_correct`'s
    match along `agreesOnFF` (`simpleValMatches_agreesOnFF_preserves`), since `e1`'s resolved value
    only ever mentions vars already in `symEnv` (`resolveSimpleExpr_vars_subset`) -- exactly the
    "existing variable passthrough" disjunct `TranslatesExprCorrectly`'s result-freshness conjunct
    was widened to allow. -/
theorem seExprId_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD) (e1 : SimpleExpr c) :
    TranslatesExprCorrectly gconf sconf specs ctx
      (fun env => Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env (Expr.id e1))
      (fun symEnv => seExprId md gconf sconf symEnv specs e1) := by
  intro symEnv hbelow _hvalid espec hspec_eq
  simp only [seExprId] at hspec_eq
  cases hres : resolveSimpleExpr symEnv e1 with
  | error msg => rw [hres] at hspec_eq; simp at hspec_eq
  | ok v =>
      rw [hres] at hspec_eq
      injection hspec_eq with hspec_eq
      subst hspec_eq
      have hsub := Corellzk2smt.SymExec.Correctness.Lemmas.resolveSimpleExpr_vars_subset
        symEnv e1 v hres
      refine ⟨le_refl _, fun v' hv' => Or.inl (hsub v' hv'), ?_, ?_, hbelow,
        fun v' hv' => Or.inl hv', ValidBinRep_trivial gconf _ _, ?_, ?_⟩
      · intro v' hv'
        rcases Std.TreeSet.mem_union_iff.mp hv' with h | h <;>
          simp only [ffVarsOfFormula, bVarsOfFormula] at h <;>
          exact absurd h Std.TreeSet.not_mem_emptyc
      · intro v' hv'
        rcases Std.TreeSet.mem_union_iff.mp hv' with h | h <;>
          simp only [ffVarsOfFormula, bVarsOfFormula] at h <;>
          exact absurd h Std.TreeSet.not_mem_emptyc
      · intro env assignment hmatch val hval
        obtain ⟨val', hval', hm⟩ :=
          resolveSimpleExpr_correct symEnv e1 env assignment v hmatch hres
        simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval', evalId] at hval
        injection hval with hval
        subst hval
        exact ⟨assignment, (fun n _ => rfl), (fun n _ => rfl), (fun n _ => rfl),
          (fun n _ => rfl), by simp only [evalFormula], hmatch, hm⟩
      · intro env assignment hmatch assignment' hagree _heval
        obtain ⟨val, hval, hm⟩ :=
          resolveSimpleExpr_correct symEnv e1 env assignment v hmatch hres
        refine ⟨val, ?_, EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env
          hagree hmatch, simpleValMatches_agreesOnFF_preserves assignment assignment' v val
            (symEnvVars symEnv) hsub hagree hm⟩
        simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hval, evalId]

end Corellzk2smt.SymExec.Correctness.ArithExprCorrectness
