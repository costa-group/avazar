import Corellzk2smt.Basic
import Corellzk2smt.Config
import Corellzk2smt.SymExec.Basic
import Corellzk2smt.SymExec.Common
import Corellzk2smt.SymExec.ArithExpr
import Corellzk2smt.SymExec.BoolExpr
import Corellzk2smt.SymExec.BitwiseExpr
import Corellzk2smt.FFConstraints.Basic
import Corellzk2smt.Language.Core.Syntax.AST
import Corellzk2smt.Language.Core.Semantics.Basic


namespace Corellzk2smt.SymExec.BigStep


open Corellzk2smt.Config (GlobalConfig)
open Corellzk2smt.Language.Core.Syntax.AST
open Corellzk2smt.Language.Core.Semantics.Basic
open Corellzk2smt.SymExec.Basic
open Corellzk2smt.FFConstraints.Basic



/- Try to evaluate an expression to a finite field value. This is used for constant propagation when
   possible.
-/
def evalExpr {c : ZKConfig}
    (_md : CmdMD)
    (_gconf : GlobalConfig c)
    (_sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (_specs : List (FuncSpec c))
    (_id : VarID)
    (e : Expr c)
  : Except String (SimpleSymVal c) :=
  match e with
  | .bop op op1 op2 =>
    match tryEvalSimpleExprToFFValue symEnv op1, tryEvalSimpleExprToFFValue symEnv op2 with
    | Except.ok v1, Except.ok v2 =>
      match op with
      | .add => Except.ok (SimpleSymVal.const (evalAdd v1 v2))
      | .sub => Except.ok (SimpleSymVal.const (evalSub v1 v2))
      | .mul => Except.ok (SimpleSymVal.const (evalMul v1 v2))
      | .div => Except.ok (SimpleSymVal.const (evalDiv v1 v2))
      | .pow => Except.ok (SimpleSymVal.const (evalPow v1 v2))
      | .uimod => Except.ok (SimpleSymVal.const (evalUimod v1 v2))
      | .uidiv => Except.ok (SimpleSymVal.const (evalUidiv v1 v2))
      | .shl => Except.ok (SimpleSymVal.const (evalShl v1 v2))
      | .shr => Except.ok (SimpleSymVal.const (evalShr v1 v2))
      | .and => Except.ok (SimpleSymVal.const (evalAnd v1 v2))
      | .or => Except.ok (SimpleSymVal.const (evalOr v1 v2))
      | .xor => Except.ok (SimpleSymVal.const (evalXor v1 v2))
      | .eq => Except.ok (SimpleSymVal.const (evalEq v1 v2))
      | .neq => Except.ok (SimpleSymVal.const (evalNeq v1 v2))
      | .lt => Except.ok (SimpleSymVal.const (evalLt v1 v2))
      | .gt => Except.ok (SimpleSymVal.const (evalGt v1 v2))
      | .le => Except.ok (SimpleSymVal.const (evalLe v1 v2))
      | .ge => Except.ok (SimpleSymVal.const (evalGe v1 v2))
      | .bor => Except.ok (SimpleSymVal.const (evalBor v1 v2))
      | .band => Except.ok (SimpleSymVal.const (evalBand v1 v2))
    | _, _ => Except.error s!"Failed to evaluate operands of '{op}' to concrete values"
  | .uop op s =>
    match tryEvalSimpleExprToFFValue symEnv s with
    | Except.ok v =>
      match op with
      | .neg => Except.ok (SimpleSymVal.const (evalNeg v))
      | .not => Except.ok (SimpleSymVal.const (evalNot v))
      | .bneg => Except.ok (SimpleSymVal.const (evalBneg v))
    | _ => Except.error s!"Failed to evaluate operand of '{op}' to concrete value"
  | .id _ =>
      Except.error "Should be handled by sEvalExpr."


/- Symbolic execution of constant assignment -/
def seEvalAssignmentConst {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (_specs : List (FuncSpec c))
    (id : VarID)
    (e : Expr c)
  : Except String (CmdsSpec c) :=
  match evalExpr md gconf sconf symEnv _specs id e with
  | Except.ok r =>
    let newSymEnv := Corellzk2smt.SymExec.Basic.setVar symEnv id (SymValue.simple r)
    Except.ok { inSymEnv := symEnv,
                outSymEnv := newSymEnv,
                f := FFFormula.true,
                nextVarId := sconf.nextVarId
    }
  | Except.error msg => Except.error msg


/- Symbolic evaluation of an expression: dispatches on `e`'s shape/operator to the matching
   `seExprXXX`, none of which need `id` -- binding the result to a variable is
   `seEvalAssignmentNonConst`'s job alone, done once, after this returns. -/
def seEvalExpr {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (e : Expr c)
  : Except String (ExprSpec c) :=
  match e with
    | .bop op s1 s2 =>
      match op with
      | .add => seExprAdd md gconf sconf symEnv specs s1 s2 -- arith
      | .sub => seExprSub md gconf sconf symEnv specs s1 s2 -- arith
      | .mul => seExprMul md gconf sconf symEnv specs s1 s2 -- arith
      | .div => seExprDiv md gconf sconf symEnv specs s1 s2 -- arith
      | .pow => seExprPow md gconf sconf symEnv specs s1 s2 -- arith
      | .uimod => seExprUIMod md gconf sconf symEnv specs s1 s2 -- arith
      | .uidiv => seExprUIDiv md gconf sconf symEnv specs s1 s2 -- arith
      -- boolean
      | .bor => seExprBor md gconf sconf symEnv specs s1 s2 -- bool
      | .band => seExprBAnd md gconf sconf symEnv specs s1 s2 -- bool
      | .eq => seExprEq md gconf sconf symEnv specs s1 s2 -- bool
      | .neq => seExprNeq md gconf sconf symEnv specs s1 s2 -- bool
      | .lt => seExprLtSigned md gconf sconf symEnv specs s1 s2 -- bool
      | .le => seExprLeSigned md gconf sconf symEnv specs s1 s2 -- bool
      | .gt => seExprGtSigned md gconf sconf symEnv specs s1 s2 -- bool
      | .ge => seExprGeSigned md gconf sconf symEnv specs s1 s2 -- bool
      -- bitwise
      | .and => seExprBitwiseAND md gconf sconf symEnv specs s1 s2 -- bitwise
      | .or => seExprBitwiseOR md gconf sconf symEnv specs s1 s2 -- bitwise
      | .xor => seExprBitwiseXOR md gconf sconf symEnv specs s1 s2 -- bitwise
      | .shl => seExprBitwiseSHL md gconf sconf symEnv specs s1 s2 -- bitwise
      | .shr => seExprBitwiseSHR md gconf sconf symEnv specs s1 s2 -- bitwise
    | .uop op s =>
      match op with
      | .neg => seExprNeg md gconf sconf symEnv specs s -- arith
      | .bneg => seExprBNeg md gconf sconf symEnv specs s -- bool
      | .not => seExprBitwiseNOT md gconf sconf symEnv specs s -- bitwise
    | .id s =>
        seExprId md gconf sconf symEnv specs s -- arith

/- Symbolic execution of non-constant assignment: evaluate `e` via `seEvalExpr`, then bind its
   result to `id` -- the one place this file actually calls `setVar`/assembles a `CmdsSpec` for
   the non-constant path. -/
def seEvalAssignmentNonConst {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (id : VarID)
    (e : Expr c)
  : Except String (CmdsSpec c) :=
  match seEvalExpr md gconf sconf symEnv specs e with
  | Except.ok exprSpec =>
    let newSymEnv :=
      Corellzk2smt.SymExec.Basic.setVar exprSpec.outSymEnv id (SymValue.simple exprSpec.result)
    Except.ok { inSymEnv := symEnv,
                outSymEnv := newSymEnv,
                f := exprSpec.f,
                nextVarId := exprSpec.nextVarId
    }
  | Except.error msg => Except.error msg

def seEvalAssignment {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (id : VarID)
    (e : Expr c)
    : Except String (CmdsSpec c) :=
  match seEvalAssignmentConst md gconf sconf symEnv specs id e with
  | Except.ok spec => Except.ok spec
  | Except.error _ =>
    seEvalAssignmentNonConst md gconf sconf symEnv specs id e

end Corellzk2smt.SymExec.BigStep
