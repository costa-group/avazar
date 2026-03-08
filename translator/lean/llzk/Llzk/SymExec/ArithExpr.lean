import Llzk.Language.Core.Syntax.AST
import Llzk.Language.Core.Syntax.Printer
import Llzk.FFConstraints.Basic
import Llzk.SymExec.Basic
import Llzk.SymExec.Common

namespace Llzk.SymExec.SymInstr

open Llzk.Language.Core.Syntax.AST
open Llzk.FFConstraints.Basic
open Llzk.Language.Core.Semantics.Basic
open Llzk.SymExec.Basic

/- Symbolic expression of .neg expression -/
def sEvalExprNeg {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (s : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v ← simpleExprToTerm senv s
  return {
          inSymEnv := senv,
          f := FFFormula.eq (FFTerm.var outFFVar) (FFTerm.neg v), -- outVar = -v
          resVar := outFFVar,
          nextId := cfg.nextId
  }

/- Symbolic expression of .add expression -/
def sEvalExprAdd {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  return {
          inSymEnv := senv,
          f := FFFormula.eq (FFTerm.var outFFVar) (FFTerm.add v1 v2), -- outVar = v1 + v2
          resVar := outFFVar,
          nextId := cfg.nextId
  }

/- Symbolic expression of .sub expression -/
def sEvalExprSub {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  return {
          inSymEnv := senv,
          f := FFFormula.eq (FFTerm.var outFFVar) (FFTerm.sub v1 v2), -- outVar = v1 - v2
          resVar := outFFVar,
          nextId := cfg.nextId
  }

/- Symbolic expression of .mul expression -/
def sEvalExprMul {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  return {
          inSymEnv := senv,
          f := FFFormula.eq (FFTerm.var outFFVar) (FFTerm.mul v1 v2), -- outVar = v1 * v2
          resVar := outFFVar,
          nextId := cfg.nextId
  }

/- Symbolic expression of .div expression -/
def sEvalExprDiv {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  return {
          inSymEnv := senv,
          -- outVar*v2 = v1
          f := FFFormula.eq (FFTerm.mul (FFTerm.var outFFVar) v2) v1,  -- (outVar = v1 / v2)
          resVar := outFFVar,
          nextId := cfg.nextId
  }

end Llzk.SymExec.SymInstr
