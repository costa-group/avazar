import Llzk.Language.Core.Syntax.AST
import Llzk.Language.Core.Syntax.Printer
import Llzk.FFConstraints.Basic
import Llzk.SymExec.Basic
import Llzk.SymExec.Common
import Llzk.SymExec.Bitify

namespace Llzk.SymExec.SymInstr

open Llzk.Language.Core.Syntax.AST
open Llzk.FFConstraints.Basic
open Llzk.Language.Core.Semantics.Basic
open Llzk.SymExec.Basic

def sEvalEq {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  return {
          inSymEnv := senv,
          f := FFFormula.ite
                 (FFFormula.eq v1 v2)
                 (FFFormula.eq (FFTerm.var outFFVar) (.val 1))
                 (FFFormula.eq (FFTerm.var outFFVar) (.val 0)),
          resVar := outFFVar,
          nextId := cfg.nextId
  }

def sEvalNeq {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  return {
          inSymEnv := senv,
          f := FFFormula.ite
                 (FFFormula.not (FFFormula.eq v1 v2))
                 (FFFormula.eq (FFTerm.var outFFVar) (.val 0))
                 (FFFormula.eq (FFTerm.var outFFVar) (.val 1)),
          resVar := outFFVar,
          nextId := cfg.nextId
  }

def sEvalBor {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  return {
          inSymEnv := senv,
          f : FFFormula c :=
               .ite (.and (.eq v1 (.val 0)) (.eq v2 (.val 0)))
                    (.eq (.var outFFVar) (.val 0))
                    (.eq (.var outFFVar) (.val 1)),
          resVar := outFFVar,
          nextId := cfg.nextId
  }

def sEvalBAnd {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  return {
          inSymEnv := senv,
          f : FFFormula c :=
               .ite (.or (.eq v1 (.val 0)) (.eq v2 (.val 0)))
                    (.eq (.var outFFVar) (.val 0))
                    (.eq (.var outFFVar) (.val 1)),
          resVar := outFFVar,
          nextId := cfg.nextId
  }

def sEvalBNeg {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (s : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v ← simpleExprToTerm senv s
  return {
          inSymEnv := senv,
          f : FFFormula c :=
               .ite (.eq v (.val 0))
                    (.eq (FFTerm.var outFFVar) (.val 1))
                    (.eq (FFTerm.var outFFVar) (.val 0)),
          resVar := outFFVar,
          nextId := cfg.nextId
  }


/-
  x<0 ->

   x < v is encoded as range(x, 0, v-1)
-/
def sEvalLtConstLeft {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToFF senv s2
  let f := if v2.val == 0 then
             FFFormula.false -- x<0 is always false when we are working with unsigned integers
           else
             FFFormula.eq (FFTerm.var outFFVar) (.ite (.range v1 0 (v2-1)) (.val 1) (.val 0))
  return {
          inSymEnv := senv,
          f := f,
          nextId := cfg.nextId,
          resVar := outFFVar
        }


/-
   v < x is encoded as range(x, v, p-1)
-/
def sEvalLtConstRight {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToFF senv s1
  let v2 ← simpleExprToTerm senv s2
  let f := if (v1.val == (c.p-1)) then
             FFFormula.false -- p-1 < x is always false when we are working with unsigned integers
           else
             FFFormula.eq (FFTerm.var outFFVar) (.ite (.range v2 (v1+1) (c.p-1)) (.val 1) (.val 0))
  return {
          inSymEnv := senv,
          f := f,
          nextId := cfg.nextId,
          resVar := outFFVar
        }

/- Trivial implementation for less than comparison, that simple
   FFFormula.lt
-/
def sEvalLtTrivial {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  return {
          inSymEnv := senv,
          f := FFFormula.eq (FFTerm.var outFFVar)
                 (FFTerm.ite (FFFormula.lt v1 v2) (.val 1) (.val 0)),
          resVar := outFFVar,
          nextId := cfg.nextId
  }


def sEvalLtBitCmp {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  -- we will compare the bits of v1 and v2 from the most significant bit to
  let (ffVars1,bits1,bits1F) := bitify cfg md v1
  let cfg' := { cfg with nextId := cfg.nextId + c.k }
  let (ffVars2,bits2,bits2F) := bitify cfg' md v2
  -- we generate the formula for the less than comparison using the bits
  -- (bits1[0] < bits2[0]) \/ (bits1[0] = bits2[0] /\ bits1[1] < bits2[1])
  let ite := List.foldl (fun acc (b1, b2) => FFTerm.ite
                                               (.and (.eq b1 (.val 0)) (.eq b2 (.val 1)))
                                               (.val 1)
                                               (.ite (.and (.eq b1 (.val 1)) (.eq b2 (.val 0))) (.val 0) acc))
                                               (.val 0) (List.zip bits1 bits2)
  let bits1Set : FFVarSet := ffVars1.foldl (fun s v => s.insert v) emptyFFVarSet
  let bits2Set : FFVarSet := ffVars2.foldl (fun s v => s.insert v) emptyFFVarSet
  let newFFVars := bits1Set ∪ bits2Set
  return {
          inSymEnv := senv,
          f := .and bits1F (.and bits2F (.eq (FFTerm.var outFFVar) ite)),
          resVar := outFFVar,
          nextId := cfg'.nextId+ c.k,
          newFFVars := newFFVars,
          newBoolVars := ∅
  }

def sEvalLt {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  -- sEvalLtTrivial cfg md senv s1 s2 outFFVar
  sEvalLtBitCmp cfg md senv s1 s2 outFFVar

/- x<=y is be encoded as 1 minus the result variable of (y < x).
-/
def sEvalLe {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let outFFVarLt : FFVar := { id := cfg.nextId,
                              meta_data := { src_info := md.src_info, orig_name := "gt_aux" }
                            }
  -- increment the nextId in the config for the next variable
  let cfg' : SymExecConfig c := { cfg with nextId := cfg.nextId + 1 }
  let ltSpec ← sEvalLt cfg' md senv s2 s1 outFFVarLt
  return {
          inSymEnv := senv,
          -- ltSpec.f /\ outFFVar = 1-outFFVarLt
          f := (.and ltSpec.f (.eq (FFTerm.var outFFVar)
                                   (FFTerm.sub (.val 1) (FFTerm.var outFFVarLt)))),
          nextId := ltSpec.nextId
          resVar := outFFVar,
          newFFVars := ltSpec.newFFVars.insert outFFVarLt,
          newBoolVars := ltSpec.newBoolVars
  }


/- Greater than simply uses the encoding of less than after swapping
   the operands -/
def sEvalGt {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  sEvalLt cfg md senv s2 s1 outFFVar

/- Greater than equal simply uses the encoding of less than equal
   after swapping the operands -/
def sEvalGe {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  sEvalLe cfg md senv s2 s1 outFFVar


end Llzk.SymExec.SymInstr
