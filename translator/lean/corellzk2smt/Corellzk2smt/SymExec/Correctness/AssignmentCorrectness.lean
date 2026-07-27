import Corellzk2smt.SymExec.Correctness.Lemmas
import Corellzk2smt.SymExec.Correctness.FuncCallCorrectness
import Corellzk2smt.SymExec.Correctness.ArithExprCorrectness
import Corellzk2smt.SymExec.Correctness.BoolExprCorrectness
import Corellzk2smt.SymExec.Correctness.BitwiseExprCorrectness

/-!
Correctness statement for `seEvalAssignment` (`SymExec/Assignment.lean`) against its concrete
counterpart `evalAssign` (`Language/Core/Semantics/Basic.lean`). Split into pieces, mirroring the
`seEvalAssignmentConst`/`seEvalAssignmentNonConst`/`seEvalAssignment` split in `Assignment.lean`
itself:

- `seEvalAssignmentConst_correct` -- the constant-folding path. `seEvalAssignmentConst` only ever
  succeeds when both operands fully constant-fold, in which case it writes the result directly
  into the symbolic environment as a `SimpleSymVal.const` (no fresh variable, no real formula
  content -- `f := FFFormula.true`), sharing the exact same `evalAdd`/`evalSub`/... functions the
  concrete side uses. That sharing is what makes soundness/completeness hold with the *same*
  assignment throughout (see `seEvalExprConcreteValue_correct`).
- `seEvalAssignmentNonConst_correct` -- the general path, built directly from `seEvalExpr_correct`
  (below), not from `seEvalExpr_isError`'s current vacuity -- so it keeps working unchanged once
  `seEvalExpr_correct` is discharged for real.
- `seEvalAssignment_correct` -- pure dispatch: `seEvalAssignment` tries `Const` first and only
  ever falls back to `NonConst` on error, so its success cases coincide exactly with `Const`'s.

Together these compose (via `SimpleCmdCorrectness.lean`) into `H_simple_holds`.

Also states `seEvalExpr_correct` -- the `TranslatesExprCorrectly` contract `seEvalExpr` needs to
satisfy, proved by pure dispatch to each `seExprXXX_correct` (`ArithExprCorrectness.lean`/
`BoolExprCorrectness.lean`/`BitwiseExprCorrectness.lean`) -- each of those is its own honest
`sorry`, since every `seExprXXX` is still a permanent `"Not implemented yet"` stub, but no `sorry`
lives directly in this file.
-/

namespace Corellzk2smt.SymExec.Correctness.AssignmentCorrectness

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
open Corellzk2smt.SymExec.Correctness.ArithExprCorrectness
open Corellzk2smt.SymExec.Correctness.BoolExprCorrectness
open Corellzk2smt.SymExec.Correctness.BitwiseExprCorrectness

/-- `evalExpr`'s (symbolic) only ever succeeds by fully constant-folding, so its result is always
    a bare `SimpleSymVal.const` -- never a fresh `.ffvar`. Purely structural: doesn't need any
    concrete environment or assignment at all. -/
theorem seEvalExprConcreteValue_isConst {c : ZKConfig} (md : CmdMD) (gconf : GlobalConfig c)
    (sconf : SymExecConfig c) (symEnv : SymEnv c) (specs : List (FuncSpec c))
    (id : VarID) (e : Expr c) (r : SimpleSymVal c)
    (heq : Corellzk2smt.SymExec.BigStep.evalExpr md gconf sconf symEnv specs id e
      = Except.ok r) :
    ∃ v, r = SimpleSymVal.const v := by
  cases e with
  | bop op s1 s2 =>
      simp only [Corellzk2smt.SymExec.BigStep.evalExpr] at heq
      cases h1 : tryEvalSimpleExprToFFValue symEnv s1 with
      | error msg => rw [h1] at heq; simp at heq
      | ok v1 =>
      cases h2 : tryEvalSimpleExprToFFValue symEnv s2 with
      | error msg => rw [h1, h2] at heq; simp at heq
      | ok v2 =>
      rw [h1, h2] at heq
      cases op with
      | div =>
          simp only [] at heq
          cases hdiv : evalDiv v1 v2 with
          | error msg => rw [hdiv] at heq; simp at heq
          | ok r => rw [hdiv] at heq; injection heq with heq; exact ⟨_, heq.symm⟩
      | uimod =>
          simp only [] at heq
          cases hmod : evalUimod v1 v2 with
          | error msg => rw [hmod] at heq; simp at heq
          | ok r => rw [hmod] at heq; injection heq with heq; exact ⟨_, heq.symm⟩
      | uidiv =>
          simp only [] at heq
          cases hdiv : evalUidiv v1 v2 with
          | error msg => rw [hdiv] at heq; simp at heq
          | ok r => rw [hdiv] at heq; injection heq with heq; exact ⟨_, heq.symm⟩
      | _ => (injection heq with heq; exact ⟨_, heq.symm⟩)
  | uop op s =>
      simp only [Corellzk2smt.SymExec.BigStep.evalExpr] at heq
      cases h1 : tryEvalSimpleExprToFFValue symEnv s with
      | error msg => rw [h1] at heq; simp at heq
      | ok v1 =>
      rw [h1] at heq
      cases op <;> (injection heq with heq; exact ⟨_, heq.symm⟩)
  | id s =>
      simp [Corellzk2smt.SymExec.BigStep.evalExpr] at heq

/-- `evalExpr`'s (symbolic) success value agrees with concrete `evalExpr`, under any assignment
    matching the symbolic environment it ran against. This is where the fact that both sides
    share the exact same `evalAdd`/`evalSub`/`evalMul`/... functions actually gets used: once the
    operands agree (`tryEvalSimpleExprToFFValue_correct`), the two sides compute *the same*
    function of *the same* values, so no new assignment is ever needed to make them match. -/
theorem seEvalExprConcreteValue_correct {c : ZKConfig} (md : CmdMD) (gconf : GlobalConfig c)
    (sconf : SymExecConfig c) (symEnv : SymEnv c) (specs : List (FuncSpec c))
    (id : VarID) (e : Expr c) (v : FF c)
    (heq : Corellzk2smt.SymExec.BigStep.evalExpr md gconf sconf symEnv specs id e
      = Except.ok (SimpleSymVal.const v))
    (env : Env c) (assignment : Assignment c) (hmatch : EnvMatches assignment symEnv env) :
    Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env e = Except.ok v := by
  cases e with
  | bop op s1 s2 =>
      simp only [Corellzk2smt.SymExec.BigStep.evalExpr] at heq
      cases h1 : tryEvalSimpleExprToFFValue symEnv s1 with
      | error msg => rw [h1] at heq; simp at heq
      | ok v1 =>
      cases h2 : tryEvalSimpleExprToFFValue symEnv s2 with
      | error msg => rw [h1, h2] at heq; simp at heq
      | ok v2 =>
      rw [h1, h2] at heq
      have hc1 := tryEvalSimpleExprToFFValue_correct symEnv s1 env assignment v1 hmatch h1
      have hc2 := tryEvalSimpleExprToFFValue_correct symEnv s2 env assignment v2 hmatch h2
      simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hc1, hc2]
      cases op with
      | div =>
          simp only [] at heq
          cases hdiv : evalDiv v1 v2 with
          | error msg => rw [hdiv] at heq; simp at heq
          | ok r =>
              rw [hdiv] at heq
              injection heq with heq
              injection heq with heq
              simp [heq]
      | uimod =>
          simp only [] at heq
          cases hmod : evalUimod v1 v2 with
          | error msg => rw [hmod] at heq; simp at heq
          | ok r =>
              rw [hmod] at heq
              injection heq with heq
              injection heq with heq
              simp [heq]
      | uidiv =>
          simp only [] at heq
          cases hdiv : evalUidiv v1 v2 with
          | error msg => rw [hdiv] at heq; simp at heq
          | ok r =>
              rw [hdiv] at heq
              injection heq with heq
              injection heq with heq
              simp [heq]
      | _ => (injection heq with heq; injection heq with heq; simp [heq])
  | uop op s =>
      simp only [Corellzk2smt.SymExec.BigStep.evalExpr] at heq
      cases h1 : tryEvalSimpleExprToFFValue symEnv s with
      | error msg => rw [h1] at heq; simp at heq
      | ok v1 =>
      rw [h1] at heq
      have hc1 := tryEvalSimpleExprToFFValue_correct symEnv s env assignment v1 hmatch h1
      simp only [Corellzk2smt.Language.Core.Semantics.Basic.evalExpr, hc1]
      cases op <;> (injection heq with heq; injection heq with heq; simp [heq])
  | id s =>
      simp [Corellzk2smt.SymExec.BigStep.evalExpr] at heq

/-- What `seEvalExpr` needs to satisfy against concrete `evalExpr` for `seEvalAssignmentNonConst`
    to be provable in general: the expression-level analogue of `H_simple`/`TranslatesCorrectly`,
    i.e. a `TranslatesExprCorrectly` fact. Pure dispatch on `e`'s shape/operator to the matching
    `seExprXXX_correct` (`ArithExprCorrectness.lean`/`BoolExprCorrectness.lean`/
    `BitwiseExprCorrectness.lean`), exactly mirroring `seEvalExpr`'s own dispatch -- each of those
    is still an honest `sorry` (every `seExprXXX` is a permanent `"Not implemented yet"` stub), so
    no `sorry` lives directly in this proof, but it isn't vacuous either: discharging any one
    `seExprXXX_correct` immediately upgrades this theorem's coverage of that operator, and once
    all 24 are real, so is this. -/
theorem seEvalExpr_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD) (e : Expr c) :
    TranslatesExprCorrectly gconf sconf specs ctx
      (fun env => Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env e)
      (fun symEnv => seEvalExpr md gconf sconf symEnv specs e) := by
  match e with
  | .bop op s1 s2 =>
      match op with
      | .add => simp only [seEvalExpr]; exact seExprAdd_correct gconf specs sconf ctx md s1 s2
      | .sub => simp only [seEvalExpr]; exact seExprSub_correct gconf specs sconf ctx md s1 s2
      | .mul => simp only [seEvalExpr]; exact seExprMul_correct gconf specs sconf ctx md s1 s2
      | .div => simp only [seEvalExpr]; exact seExprDiv_correct gconf specs sconf ctx md s1 s2
      | .pow => simp only [seEvalExpr]; exact seExprPow_correct gconf specs sconf ctx md s1 s2
      | .uimod =>
          simp only [seEvalExpr]; exact seExprUIMod_correct gconf specs sconf ctx md s1 s2
      | .uidiv =>
          simp only [seEvalExpr]; exact seExprUIDiv_correct gconf specs sconf ctx md s1 s2
      | .bor => simp only [seEvalExpr]; exact seExprBor_correct gconf specs sconf ctx md s1 s2
      | .band => simp only [seEvalExpr]; exact seExprBAnd_correct gconf specs sconf ctx md s1 s2
      | .eq => simp only [seEvalExpr]; exact seExprEq_correct gconf specs sconf ctx md s1 s2
      | .neq => simp only [seEvalExpr]; exact seExprNeq_correct gconf specs sconf ctx md s1 s2
      | .lt =>
          simp only [seEvalExpr]; exact seExprLtSigned_correct gconf specs sconf ctx md s1 s2
      | .le =>
          simp only [seEvalExpr]; exact seExprLeSigned_correct gconf specs sconf ctx md s1 s2
      | .gt =>
          simp only [seEvalExpr]; exact seExprGtSigned_correct gconf specs sconf ctx md s1 s2
      | .ge =>
          simp only [seEvalExpr]; exact seExprGeSigned_correct gconf specs sconf ctx md s1 s2
      | .and =>
          simp only [seEvalExpr]; exact seExprBitwiseAND_correct gconf specs sconf ctx md s1 s2
      | .or =>
          simp only [seEvalExpr]; exact seExprBitwiseOR_correct gconf specs sconf ctx md s1 s2
      | .xor =>
          simp only [seEvalExpr]; exact seExprBitwiseXOR_correct gconf specs sconf ctx md s1 s2
      | .shl =>
          simp only [seEvalExpr]; exact seExprBitwiseSHL_correct gconf specs sconf ctx md s1 s2
      | .shr =>
          simp only [seEvalExpr]; exact seExprBitwiseSHR_correct gconf specs sconf ctx md s1 s2
  | .uop op s =>
      match op with
      | .neg => simp only [seEvalExpr]; exact seExprNeg_correct gconf specs sconf ctx md s
      | .bneg => simp only [seEvalExpr]; exact seExprBNeg_correct gconf specs sconf ctx md s
      | .not => simp only [seEvalExpr]; exact seExprBitwiseNOT_correct gconf specs sconf ctx md s
  | .id s =>
      simp only [seEvalExpr]; exact seExprId_correct gconf specs sconf ctx md s

/-- `seEvalExpr` never succeeds on a `.bop` shape *other than* `.add`/`.sub`/`.mul` today -- every
    remaining dispatch target (`seExprDiv`, `seExprPow`, ...) is still a permanent `"Not
    implemented yet"` stub. Scoped away from those three (via the `hop1`/`hop2`/`hop3` hypotheses),
    unlike an earlier single lemma covering every `Expr` shape: `.add`/`.sub`/`.mul` dispatch to
    `seExprAdd`/`seExprSub`/`seExprMul`, none of which are stubs anymore (see
    `seExprAdd_correct`/`seExprSub_correct`/`seExprMul_correct`), so a lemma claiming `seEvalExpr`
    *always* fails on `.bop` can no longer cover those cases. This will need to shrink further as
    each remaining `.bop`/`.uop` operator gets implemented for real. -/
theorem seEvalExpr_bop_isError {c : ZKConfig} (md : CmdMD) (gconf : GlobalConfig c)
    (sconf : SymExecConfig c) (symEnv : SymEnv c) (specs : List (FuncSpec c))
    (op : BinOp) (hop1 : op ≠ BinOp.add) (hop2 : op ≠ BinOp.sub) (hop3 : op ≠ BinOp.mul)
    (hop4 : op ≠ BinOp.div) (s1 s2 : SimpleExpr c) (exprSpec : ExprSpec c)
    (heq : seEvalExpr md gconf sconf symEnv specs (Expr.bop op s1 s2) = Except.ok exprSpec) :
    False := by
  cases op <;>
    first
    | exact absurd rfl hop1
    | exact absurd rfl hop2
    | exact absurd rfl hop3
    | exact absurd rfl hop4
    | simp [seEvalExpr, seExprPow,
        seExprUIMod, seExprUIDiv, seExprBor, seExprBAnd, seExprEq, seExprNeq, seExprLtSigned,
        seExprLeSigned, seExprGtSigned, seExprGeSigned, seExprBitwiseAND, seExprBitwiseOR,
        seExprBitwiseXOR, seExprBitwiseSHL, seExprBitwiseSHR] at heq

/-- `seEvalExpr` on `.bop .div s1 s2`, when it succeeds, does so via `seExprDiv`'s exact defining
    shape -- output symbolic environment unchanged, formula the "safe division" tie-back equation
    `outVar * v2 = v1`. Stated directly against `seExprDiv`'s implementation, purely for the
    domain-of-defined/names-below bookkeeping `SimpleCmdCorrectness.lean` needs -- unlike
    `seEvalExpr_add_eq`/`seEvalExpr_sub_eq`/`seEvalExpr_mul_eq`, no `seExprDiv_correct` is proved
    from this yet (the encoding's `v2 = 0` behavior doesn't yet match `evalDiv`'s own, so
    `seExprDiv_correct` is deliberately left open -- see the discussion at `seExprDiv`'s call
    site). -/
theorem seEvalExpr_div_eq {c : ZKConfig} (md : CmdMD) (gconf : GlobalConfig c)
    (sconf : SymExecConfig c) (symEnv : SymEnv c) (specs : List (FuncSpec c))
    (s1 s2 : SimpleExpr c) (exprSpec : ExprSpec c)
    (heq : seEvalExpr md gconf sconf symEnv specs (Expr.bop BinOp.div s1 s2)
      = Except.ok exprSpec) :
    ∃ v1 v2, resolveSimpleExpr symEnv s1 = Except.ok v1 ∧
      resolveSimpleExpr symEnv s2 = Except.ok v2 ∧
      exprSpec.outSymEnv = symEnv ∧
      exprSpec.f = FFFormula.eq (FFTerm.mul (FFTerm.var sconf.nextVarId) (simpleSymValToTerm v2))
        (simpleSymValToTerm v1) := by
  simp only [seEvalExpr, seExprDiv] at heq
  cases hres1 : resolveSimpleExpr symEnv s1 with
  | error msg => rw [hres1] at heq; simp at heq
  | ok v1 =>
      rw [hres1] at heq
      cases hres2 : resolveSimpleExpr symEnv s2 with
      | error msg => rw [hres2] at heq; simp at heq
      | ok v2 =>
          rw [hres2] at heq
          injection heq with heq
          subst heq
          exact ⟨v1, v2, rfl, rfl, rfl, rfl⟩

/-- Mirror of `seEvalExpr_add_eq`, for `seExprSub` (`outVar = v1 - v2`). -/
theorem seEvalExpr_sub_eq {c : ZKConfig} (md : CmdMD) (gconf : GlobalConfig c)
    (sconf : SymExecConfig c) (symEnv : SymEnv c) (specs : List (FuncSpec c))
    (s1 s2 : SimpleExpr c) (exprSpec : ExprSpec c)
    (heq : seEvalExpr md gconf sconf symEnv specs (Expr.bop BinOp.sub s1 s2)
      = Except.ok exprSpec) :
    ∃ v1 v2, resolveSimpleExpr symEnv s1 = Except.ok v1 ∧
      resolveSimpleExpr symEnv s2 = Except.ok v2 ∧
      exprSpec.outSymEnv = symEnv ∧
      exprSpec.f = FFFormula.eq (FFTerm.var sconf.nextVarId)
        (FFTerm.sub (simpleSymValToTerm v1) (simpleSymValToTerm v2)) := by
  simp only [seEvalExpr, seExprSub] at heq
  cases hres1 : resolveSimpleExpr symEnv s1 with
  | error msg => rw [hres1] at heq; simp at heq
  | ok v1 =>
      rw [hres1] at heq
      cases hres2 : resolveSimpleExpr symEnv s2 with
      | error msg => rw [hres2] at heq; simp at heq
      | ok v2 =>
          rw [hres2] at heq
          injection heq with heq
          subst heq
          exact ⟨v1, v2, rfl, rfl, rfl, rfl⟩

/-- Mirror of `seEvalExpr_add_eq`, for `seExprMul` (`outVar = v1 * v2`). -/
theorem seEvalExpr_mul_eq {c : ZKConfig} (md : CmdMD) (gconf : GlobalConfig c)
    (sconf : SymExecConfig c) (symEnv : SymEnv c) (specs : List (FuncSpec c))
    (s1 s2 : SimpleExpr c) (exprSpec : ExprSpec c)
    (heq : seEvalExpr md gconf sconf symEnv specs (Expr.bop BinOp.mul s1 s2)
      = Except.ok exprSpec) :
    ∃ v1 v2, resolveSimpleExpr symEnv s1 = Except.ok v1 ∧
      resolveSimpleExpr symEnv s2 = Except.ok v2 ∧
      exprSpec.outSymEnv = symEnv ∧
      exprSpec.f = FFFormula.eq (FFTerm.var sconf.nextVarId)
        (FFTerm.mul (simpleSymValToTerm v1) (simpleSymValToTerm v2)) := by
  simp only [seEvalExpr, seExprMul] at heq
  cases hres1 : resolveSimpleExpr symEnv s1 with
  | error msg => rw [hres1] at heq; simp at heq
  | ok v1 =>
      rw [hres1] at heq
      cases hres2 : resolveSimpleExpr symEnv s2 with
      | error msg => rw [hres2] at heq; simp at heq
      | ok v2 =>
          rw [hres2] at heq
          injection heq with heq
          subst heq
          exact ⟨v1, v2, rfl, rfl, rfl, rfl⟩

/-- `seEvalExpr` on `.bop .add s1 s2`, when it succeeds, does so via `seExprAdd`'s exact defining
    shape -- output symbolic environment unchanged, formula the fresh-var tie-back equation
    `outVar = v1 + v2` for whatever `v1`/`v2` `s1`/`s2` resolve to. Stated directly against
    `seExprAdd`'s implementation, same reason as `seEvalExpr_id_eq`/`seEvalExpr_neg_eq`. -/
theorem seEvalExpr_add_eq {c : ZKConfig} (md : CmdMD) (gconf : GlobalConfig c)
    (sconf : SymExecConfig c) (symEnv : SymEnv c) (specs : List (FuncSpec c))
    (s1 s2 : SimpleExpr c) (exprSpec : ExprSpec c)
    (heq : seEvalExpr md gconf sconf symEnv specs (Expr.bop BinOp.add s1 s2)
      = Except.ok exprSpec) :
    ∃ v1 v2, resolveSimpleExpr symEnv s1 = Except.ok v1 ∧
      resolveSimpleExpr symEnv s2 = Except.ok v2 ∧
      exprSpec.outSymEnv = symEnv ∧
      exprSpec.f = FFFormula.eq (FFTerm.var sconf.nextVarId)
        (FFTerm.add (simpleSymValToTerm v1) (simpleSymValToTerm v2)) := by
  simp only [seEvalExpr, seExprAdd] at heq
  cases hres1 : resolveSimpleExpr symEnv s1 with
  | error msg => rw [hres1] at heq; simp at heq
  | ok v1 =>
      rw [hres1] at heq
      cases hres2 : resolveSimpleExpr symEnv s2 with
      | error msg => rw [hres2] at heq; simp at heq
      | ok v2 =>
          rw [hres2] at heq
          injection heq with heq
          subst heq
          exact ⟨v1, v2, rfl, rfl, rfl, rfl⟩

/-- `seEvalExpr` never succeeds on `.uop .bneg` today -- `seExprBNeg` is still a permanent
    `"Not implemented yet"` stub. Scoped to `.bneg` only: `.neg` dispatches to `seExprNeg`, which
    is no longer a stub (see `seExprNeg_correct`), so a single lemma covering all of `.uop` can no
    longer claim `seEvalExpr` always fails there. -/
theorem seEvalExpr_bneg_isError {c : ZKConfig} (md : CmdMD) (gconf : GlobalConfig c)
    (sconf : SymExecConfig c) (symEnv : SymEnv c) (specs : List (FuncSpec c))
    (s : SimpleExpr c) (exprSpec : ExprSpec c)
    (heq : seEvalExpr md gconf sconf symEnv specs (Expr.uop UnOp.bneg s) = Except.ok exprSpec) :
    False := by
  simp [seEvalExpr, seExprBNeg] at heq

/-- Mirror of `seEvalExpr_bneg_isError`, for `.uop .not`. -/
theorem seEvalExpr_not_isError {c : ZKConfig} (md : CmdMD) (gconf : GlobalConfig c)
    (sconf : SymExecConfig c) (symEnv : SymEnv c) (specs : List (FuncSpec c))
    (s : SimpleExpr c) (exprSpec : ExprSpec c)
    (heq : seEvalExpr md gconf sconf symEnv specs (Expr.uop UnOp.not s) = Except.ok exprSpec) :
    False := by
  simp [seEvalExpr, seExprBitwiseNOT] at heq

/-- `seEvalExpr` on `.id s`, when it succeeds, does so via `seExprId`'s exact defining shape --
    output symbolic environment unchanged, formula trivial. Stated directly against `seExprId`'s
    implementation (not through `TranslatesExprCorrectly`, which says nothing about `outSymEnv`'s
    domain/`f`'s shape specifically) since domain-of-defined/names-below bookkeeping is already
    handled this way for the `.assign` `Const` path -- see
    `H_simple_domain_holds`/`H_simple_names_below_holds`. -/
theorem seEvalExpr_id_eq {c : ZKConfig} (md : CmdMD) (gconf : GlobalConfig c)
    (sconf : SymExecConfig c) (symEnv : SymEnv c) (specs : List (FuncSpec c))
    (s : SimpleExpr c) (exprSpec : ExprSpec c)
    (heq : seEvalExpr md gconf sconf symEnv specs (Expr.id s) = Except.ok exprSpec) :
    exprSpec.outSymEnv = symEnv ∧ exprSpec.f = FFFormula.true := by
  simp only [seEvalExpr, seExprId] at heq
  cases hres : resolveSimpleExpr symEnv s with
  | error msg => rw [hres] at heq; simp at heq
  | ok v =>
      rw [hres] at heq
      injection heq with heq
      subst heq
      exact ⟨rfl, rfl⟩

/-- `seEvalExpr` on `.uop .neg s`, when it succeeds, does so via `seExprNeg`'s exact defining
    shape -- output symbolic environment unchanged, formula the fresh-var tie-back equation
    `outVar = -v` for whatever `v` `s` resolves to. Stated directly against `seExprNeg`'s
    implementation, same reason as `seEvalExpr_id_eq`. -/
theorem seEvalExpr_neg_eq {c : ZKConfig} (md : CmdMD) (gconf : GlobalConfig c)
    (sconf : SymExecConfig c) (symEnv : SymEnv c) (specs : List (FuncSpec c))
    (s : SimpleExpr c) (exprSpec : ExprSpec c)
    (heq : seEvalExpr md gconf sconf symEnv specs (Expr.uop UnOp.neg s) = Except.ok exprSpec) :
    ∃ v, resolveSimpleExpr symEnv s = Except.ok v ∧ exprSpec.outSymEnv = symEnv ∧
      exprSpec.f = FFFormula.eq (FFTerm.var sconf.nextVarId) (FFTerm.neg (simpleSymValToTerm v)) := by
  simp only [seEvalExpr, seExprNeg] at heq
  cases hres : resolveSimpleExpr symEnv s with
  | error msg => rw [hres] at heq; simp at heq
  | ok v =>
      rw [hres] at heq
      injection heq with heq
      subst heq
      exact ⟨v, rfl, rfl, rfl⟩

/-- `seEvalAssignmentNonConst` correctly translates `evalAssign`, *given* `seEvalExpr_correct`'s
    contract -- built directly from it (not from `seEvalExpr_isError`'s current vacuity), so this
    proof keeps working unchanged once that `sorry` is discharged for real: binding `exprSpec`'s
    result to `id` (`EnvMatches_setVar`) is the only new step over what `seEvalExpr_correct`
    itself already provides. -/
theorem seEvalAssignmentNonConst_correct {c : ZKConfig} (gconf : GlobalConfig c)
    (specs : List (FuncSpec c)) (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD)
    (id : VarID) (e : Expr c) :
    TranslatesCorrectly gconf sconf specs ctx
      (fun env => evalAssign md gconf env id e)
      (fun symEnv => seEvalAssignmentNonConst md gconf sconf symEnv specs id e) := by
  intro symEnv hbelow hvalid spec hspec_eq
  have hcontract := seEvalExpr_correct gconf specs sconf ctx md e symEnv hbelow hvalid
  cases hexpr : seEvalExpr md gconf sconf symEnv specs e with
  | error msg => simp [seEvalAssignmentNonConst, hexpr] at hspec_eq
  | ok espec =>
  obtain ⟨hnv, hresult_sub, hfresh, hfbelow, houtbelow, houtfresh, _hvalidbin, hsound, hcomplete⟩ :=
    hcontract espec hexpr
  simp only [seEvalAssignmentNonConst, hexpr] at hspec_eq
  injection hspec_eq with hspec_eq
  subst hspec_eq
  refine ⟨rfl, hnv, hfresh, hfbelow, ?_, ?_, ValidBinRep_trivial gconf _ _, ?_, ?_⟩
  · intro v hv
    rcases symEnvVars_setVar_subset espec.outSymEnv id (SymValue.simple espec.result) v hv
      with h | h
    · exact houtbelow v h
    · simp only [symValVars] at h
      rcases hresult_sub v h with h2 | h2
      · exact lt_of_lt_of_le (hbelow v h2) hnv
      · exact hfbelow v h2
  · intro v hv
    rcases symEnvVars_setVar_subset espec.outSymEnv id (SymValue.simple espec.result) v hv
      with h | h
    · exact houtfresh v h
    · simp only [symValVars] at h
      rcases hresult_sub v h with h2 | h2
      · exact Or.inl h2
      · exact hfresh v h2
  · intro env assignment hmatch env' hc
    simp only [evalAssign] at hc
    cases hce : Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env e with
    | error msg => rw [hce] at hc; simp at hc
    | ok val =>
        rw [hce] at hc
        injection hc with hc
        obtain ⟨assignment', hagreeff, hagreebool, hframeff, hframebool, hf, houtmatch,
          hresmatch⟩ := hsound env assignment hmatch val hce
        refine ⟨assignment', hagreeff, hagreebool, hframeff, hframebool, hf, ?_⟩
        rw [← hc]
        exact EnvMatches_setVar assignment' espec.outSymEnv env id (SymValue.simple espec.result)
          (Value.scalar val) houtmatch (by simp only [symValMatches]; exact hresmatch)
  · intro env assignment hmatch assignment' hagree heval_f
    obtain ⟨val, hval_ok, houtmatch, hresmatch⟩ :=
      hcomplete env assignment hmatch assignment' hagree heval_f
    refine ⟨Corellzk2smt.Language.Core.Semantics.Basic.setVar env id (Value.scalar val), ?_, ?_⟩
    · simp only [evalAssign, hval_ok]
    · exact EnvMatches_setVar assignment' espec.outSymEnv env id (SymValue.simple espec.result)
        (Value.scalar val) houtmatch (by simp only [symValMatches]; exact hresmatch)

/-- `seEvalAssignmentConst` correctly translates `evalAssign`, when it succeeds: both sides
    constant-fold via the shared `evalAdd`/`evalSub`/.../`evalNeg`/... functions, so soundness
    and completeness both go through with the witness assignment *unchanged* --
    `f := FFFormula.true` means there's no real constraint to satisfy, and the newly-bound `id` is
    a bare constant, not a fresh variable, so nothing needs solving for. -/
theorem seEvalAssignmentConst_correct {c : ZKConfig} (gconf : GlobalConfig c)
    (specs : List (FuncSpec c)) (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD)
    (id : VarID) (e : Expr c) :
    TranslatesCorrectly gconf sconf specs ctx
      (fun env => evalAssign md gconf env id e)
      (fun symEnv => seEvalAssignmentConst md gconf sconf symEnv specs id e) := by
  intro symEnv hbelow _hvalid spec hspec_eq
  cases heval : Corellzk2smt.SymExec.BigStep.evalExpr md gconf sconf symEnv specs id e with
  | error msg => simp [seEvalAssignmentConst, heval] at hspec_eq
  | ok r =>
  obtain ⟨v, hv⟩ := seEvalExprConcreteValue_isConst md gconf sconf symEnv specs id e r heval
  subst hv
  simp only [seEvalAssignmentConst, heval] at hspec_eq
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
    rcases symEnvVars_setVar_subset symEnv id (SymValue.simple (SimpleSymVal.const v)) v' hv'
      with h | h
    · exact hbelow v' h
    · simp only [symValVars, simpleValVars] at h
      exact absurd h Std.TreeSet.not_mem_emptyc
  · intro v' hv'
    rcases symEnvVars_setVar_subset symEnv id (SymValue.simple (SimpleSymVal.const v)) v' hv'
      with h | h
    · exact Or.inl h
    · simp only [symValVars, simpleValVars] at h
      exact absurd h Std.TreeSet.not_mem_emptyc
  · intro env assignment hmatch env' hc
    simp only [evalAssign] at hc
    cases hce : Corellzk2smt.Language.Core.Semantics.Basic.evalExpr env e with
    | error msg => rw [hce] at hc; simp at hc
    | ok val =>
        rw [hce] at hc
        injection hc with hc
        have hcv := seEvalExprConcreteValue_correct md gconf sconf symEnv specs id e v heval env
          assignment hmatch
        rw [hcv] at hce
        injection hce with hce
        subst hce
        refine ⟨assignment, (fun n _ => rfl), (fun n _ => rfl), (fun n _ => rfl),
          (fun n _ => rfl), ?_, ?_⟩
        · simp only [evalFormula]
        · rw [← hc]; exact EnvMatches_setVar_const assignment symEnv env id v hmatch
  · intro env assignment hmatch assignment' hagree _heval_f
    refine ⟨Corellzk2smt.Language.Core.Semantics.Basic.setVar env id (Value.scalar v), ?_, ?_⟩
    · simp only [evalAssign, seEvalExprConcreteValue_correct md gconf sconf symEnv specs id e v
        heval env assignment hmatch]
    · exact EnvMatches_setVar_const assignment' symEnv env id v
        (EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env hagree hmatch)

/-- `seEvalAssignment` correctly translates `evalAssign` -- pure dispatch: `seEvalAssignment`
    tries `seEvalAssignmentConst` first and only falls back to `seEvalAssignmentNonConst` when
    that errors, so its success cases coincide exactly with one or the other's own. -/
theorem seEvalAssignment_correct {c : ZKConfig} (gconf : GlobalConfig c)
    (specs : List (FuncSpec c)) (sconf : SymExecConfig c) (ctx : FFFormula c) (md : CmdMD)
    (id : VarID) (e : Expr c) :
    TranslatesCorrectly gconf sconf specs ctx
      (fun env => evalAssign md gconf env id e)
      (fun symEnv => seEvalAssignment md gconf sconf symEnv specs id e) := by
  intro symEnv hbelow hvalid spec hspec_eq
  simp only [seEvalAssignment] at hspec_eq
  cases hconst : seEvalAssignmentConst md gconf sconf symEnv specs id e with
  | ok spec' =>
      rw [hconst] at hspec_eq
      injection hspec_eq with hspec_eq
      subst hspec_eq
      exact seEvalAssignmentConst_correct gconf specs sconf ctx md id e symEnv hbelow hvalid
        spec' hconst
  | error msg =>
      rw [hconst] at hspec_eq
      exact seEvalAssignmentNonConst_correct gconf specs sconf ctx md id e symEnv hbelow hvalid
        spec hspec_eq

end Corellzk2smt.SymExec.Correctness.AssignmentCorrectness
