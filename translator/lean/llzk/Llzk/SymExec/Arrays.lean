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

/- Symbolic execution of array creation -/
def seNewArray {c : ZKConfig}
  (_cfg : SymExecConfig c) (_md : CmdMD) (symEnv : SymEnv c) (id : VarID) (size : SimpleExpr c)
  : Except String (CmdsSpec c) := do
  match simpleExprToFF symEnv size with
  | Except.error err => Except.error ("seNewArray: failed to evaluate size expression: " ++ err)
  | Except.ok sz =>
    let arr : SymFFArray c := (List.replicate sz.val (.const 0)).toArray
    let newSymEnv := setVar symEnv id (SymValue.ffArray arr)
    return { inSymEnv := symEnv,
             outSymEnv := newSymEnv,
             f := FFFormula.true,
             nextId := _cfg.nextId,
             newFFVars := emptyFFVarSet,
             newBoolVars := emptyBoolVarSet
    }


def seArrayReadConstIdx {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD) (symEnv : SymEnv c)
  (out : VarID) (a : VarID) (idx : SimpleExpr c)
  : Except String (CmdsSpec c) := do
  let idxVal ← simpleExprToFF symEnv idx
  match getVar symEnv a with
  | Except.error err => Except.error ("seArrayReadConstIdx: failed to get array variable: " ++ err)
  | Except.ok (SymValue.ffArray arr) =>
    if h : idxVal.val < arr.size then
      let elem := arr[idxVal.val]'h
      match elem with
      | SymFFVar.const v =>
        let newSymEnv := setVar symEnv out (SymValue.ffVar (SymFFVar.const v))
        return { inSymEnv := symEnv,
                 outSymEnv := newSymEnv,
                 f := FFFormula.true,
                 nextId := cfg.nextId,
                 newFFVars := emptyFFVarSet,
                 newBoolVars := emptyBoolVarSet
        }
      | SymFFVar.var v =>
        let newSymEnv := setVar symEnv out (SymValue.ffVar (SymFFVar.var v))
        return { inSymEnv := symEnv,
                 outSymEnv := newSymEnv,
                 f := FFFormula.true,
                 nextId := cfg.nextId,
                 newFFVars := emptyFFVarSet,
                 newBoolVars := emptyBoolVarSet
        }
    else
      Except.error
         s!"seArrayReadConstIdx: index {idxVal.val} out of bounds for array of size {arr.size}"
  | Except.ok _ => Except.error s!"seArrayReadConstIdx: variable '{a}' is not an array"

def seArrayReadNonConstIdx {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD) (symEnv : SymEnv c)
  (out : VarID) (a : VarID) (idx : SimpleExpr c)
  : Except String (CmdsSpec c) := do
  throw s!"seArrayRead operations with non-constant index not implemented yet"


/- Symbolic execution of array read -/
def seArrayRead {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD) (symEnv : SymEnv c)
  (out : VarID) (a : VarID) (idx : SimpleExpr c)
  : Except String (CmdsSpec c) := do
  match seArrayReadConstIdx cfg md symEnv out a idx with
  | Except.ok spec => return spec
  | Except.error _ => seArrayReadNonConstIdx cfg md symEnv out a idx



def seArrayWriteConstIdx {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD) (symEnv : SymEnv c)
  (a : VarID) (idx : SimpleExpr c) (value : SimpleExpr c)
  : Except String (CmdsSpec c) := do
  let idxVal ← simpleExprToFF symEnv idx
  let valueVal ← simpleExprToSymFFVar symEnv value
  match getVar symEnv a with
  | Except.error err => Except.error ("seArrayWriteConstIdx: failed to get array variable: " ++ err)
  | Except.ok (SymValue.ffArray arr) =>
    if h : idxVal.val < arr.size then
      let newArr := arr.set idxVal.val valueVal
      let newSymEnv := setVar symEnv a (SymValue.ffArray newArr)
      return { inSymEnv := symEnv,
               outSymEnv := newSymEnv,
               f := FFFormula.true,
               nextId := cfg.nextId,
               newFFVars := emptyFFVarSet,
               newBoolVars := emptyBoolVarSet
      }
    else
      Except.error
         s!"seArrayWriteConstIdx: index {idxVal.val} out of bounds for array of size {arr.size}"
  | Except.ok _ => Except.error s!"seArrayWriteConstIdx: variable '{a}' is not an array"

def seArrayWriteNonConstIdx {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD) (symEnv : SymEnv c)
  (a : VarID) (idx : SimpleExpr c) (value : SimpleExpr c)
  : Except String (CmdsSpec c) := do
  throw s!"seArrayWrite operations with non-constant index not implemented yet"

def seArrayWrite {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD) (symEnv : SymEnv c)
  (a : VarID) (idx : SimpleExpr c) (value : SimpleExpr c)
  : Except String (CmdsSpec c) := do
  match seArrayWriteConstIdx cfg md symEnv a idx value with
  | Except.ok spec => return spec
  | Except.error e =>
     seArrayWriteNonConstIdx cfg md symEnv a idx value

/- Symbolic execution of array copy -/
def seArrayCopy {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD) (symEnv : SymEnv c) (out : VarID) (a : VarID)
  : Except String (CmdsSpec c) := do
  match getVar symEnv a with
  | Except.error err => Except.error ("seArrayCopy: failed to get array variable: " ++ err)
  | Except.ok (SymValue.ffArray arr) =>
    let newSymEnv := setVar symEnv out (SymValue.ffArray arr)
    return { inSymEnv := symEnv,
             outSymEnv := newSymEnv,
             f := FFFormula.true,
             nextId := cfg.nextId,
             newFFVars := emptyFFVarSet,
             newBoolVars := emptyBoolVarSet
    }
  | Except.ok _ => Except.error s!"seArrayCopy: variable '{a}' is not an array"

end Llzk.SymExec.SymInstr
