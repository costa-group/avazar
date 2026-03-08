import Llzk.Language.Core.Syntax.AST
import Llzk.Language.Core.Syntax.Printer
import Llzk.FFConstraints.Basic
import Llzk.SymExec.Basic
import Llzk.SymExec.Common
import Llzk.SymExec.Expr


namespace Llzk.SymExec.SymInstr

open Llzk.Language.Core.Syntax.AST
open Llzk.FFConstraints.Basic
open Llzk.Language.Core.Semantics.Basic
open Llzk.SymExec.Basic

/- Try to evaluate an expression to a finite field value. This is used for constant propagation when
   possible.
-/
def evalExpr {c : ZKConfig}
  (senv : SymEnv c) (e : Expr c)
  : Except String (SymFFVar c) := do
  match e with
  | .bop op op1 op2 =>
    let v1 ← simpleExprToFF senv op1
    let v2 ← simpleExprToFF senv op2
    match op with
    | .add => Except.ok (SymFFVar.const (evalAdd v1 v2))
    | .sub => Except.ok (SymFFVar.const (evalSub v1 v2))
    | .mul => Except.ok (SymFFVar.const (evalMul v1 v2))
    | .div => Except.ok (SymFFVar.const (evalDiv v1 v2))
    | .shl => Except.ok (SymFFVar.const (evalShl v1 v2))
    | .shr => Except.ok (SymFFVar.const (evalShr v1 v2))
    | .and => Except.ok (SymFFVar.const (evalAnd v1 v2))
    | .or => Except.ok (SymFFVar.const (evalOr v1 v2))
    | .xor => Except.ok (SymFFVar.const (evalXor v1 v2))
    | .eq => Except.ok (SymFFVar.const (evalEq v1 v2))
    | .neq => Except.ok (SymFFVar.const (evalNeq v1 v2))
    | .lt => Except.ok (SymFFVar.const (evalLt v1 v2))
    | .gt => Except.ok (SymFFVar.const (evalGt v1 v2))
    | .le => Except.ok (SymFFVar.const (evalLe v1 v2))
    | .ge => Except.ok (SymFFVar.const (evalGe v1 v2))
    | .bor => Except.ok (SymFFVar.const (evalBor v1 v2))
    | .band => Except.ok (SymFFVar.const (evalBand v1 v2))
  | .uop op s =>
    let v ← simpleExprToFF senv s
    match op with
    | .neg => Except.ok (SymFFVar.const (evalNeg v))
    | .not => Except.ok (SymFFVar.const (evalNot v))
    | .bneg => Except.ok (SymFFVar.const (evalBneg v))
  | .id s =>
    simpleExprToSymFFVar senv s



/- Symbolic execution of constant assignment -/
def seAssignmentConst {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD) (symEnv : SymEnv c) (id : String) (e : Expr c)
  : Except String (CmdsSpec c) := do
  let r ← evalExpr symEnv e
  let newSymEnv := setVar symEnv id (SymValue.ffVar r)
  return { inSymEnv := symEnv,
           outSymEnv := newSymEnv,
           f := FFFormula.true,
           nextId := cfg.nextId,
           newFFVars := emptyFFVarSet,
           newBoolVars := emptyBoolVarSet
  }

/- Symbolic execution of non-constant assignment -/
def seAssignmentNonConst {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD) (symEnv : SymEnv c) (id : VarID) (e : Expr c)
  : Except String (CmdsSpec c) := do
  -- new variable for the result of the expression
  let outFFVar : FFVar := { id := cfg.nextId,
                            meta_data := { src_info := md.src_info, orig_name := id}
                          }
  -- increment the nextId in the config for the next variable
  let cfg' : SymExecConfig c := { cfg with nextId := cfg.nextId + 1 }
  -- calculate the spec for the expression
  let exprSpec ← sEvalExpr cfg' md symEnv e outFFVar
  -- update the symbolic environment with the new variable
  let newSymEnv := setVar symEnv id (SymValue.ffVar (SymFFVar.var outFFVar))
  -- the command spec
  return { inSymEnv := symEnv,
           outSymEnv := newSymEnv,
           f := exprSpec.f,
           nextId := exprSpec.nextId,
           newFFVars := exprSpec.newFFVars.insert outFFVar,
           newBoolVars := exprSpec.newBoolVars }

/- Symbolic execution of assignment -/
def seAssignment {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD) (symEnv : SymEnv c) (id : VarID) (e : Expr c)
  : Except String (CmdsSpec c) := do
  match seAssignmentConst cfg md symEnv id e with -- try to do constant propagation first
  | Except.ok spec => return spec
  | Except.error _ => seAssignmentNonConst cfg md symEnv id e


end Llzk.SymExec.SymInstr
