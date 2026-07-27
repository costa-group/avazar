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

theorem seExprUIMod_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD) (e1 e2 : SimpleExpr c) :
    TranslatesExprCorrectly gconf sconf specs ctx
      (fun env => Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env
        (Expr.bop BinOp.uimod e1 e2))
      (fun symEnv => seExprUIMod md gconf sconf symEnv specs e1 e2) := by
  sorry

theorem seExprUIDiv_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD) (e1 e2 : SimpleExpr c) :
    TranslatesExprCorrectly gconf sconf specs ctx
      (fun env => Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env
        (Expr.bop BinOp.uidiv e1 e2))
      (fun symEnv => seExprUIDiv md gconf sconf symEnv specs e1 e2) := by
  sorry

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
