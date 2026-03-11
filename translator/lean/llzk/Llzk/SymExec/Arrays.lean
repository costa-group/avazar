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
  match getVar symEnv a with
  | Except.error err => Except.error ("seArrayReadNonConstIdx: failed to get array variable: " ++ err)
  | Except.ok (SymValue.ffArray arr) =>
    let arrayElements := arr.toList
    let idxTerm ← simpleExprToTerm symEnv idx -- it is not a value
    let outFFVar := FFVar.mk (cfg.nextId) { src_info := md.src_info, orig_name := "a_nc_access" }
    let rec loop (l : List (SymFFVar c)) (i : Nat) : FFFormula c :=
      match l with
      | [] => FFFormula.false
      | elem :: rest =>
        let elemTerm := symVarToTerm elem
        let idxEq := FFFormula.eq idxTerm (.val i)
        let caseFormula := (FFFormula.eq (FFTerm.var outFFVar) elemTerm)
        let restFormula := loop rest (i + 1)
        .ite idxEq caseFormula restFormula
    let f := loop arrayElements 0
    let newSymEnv := setVar symEnv out (SymValue.ffVar (SymFFVar.var outFFVar))
    return { inSymEnv := symEnv,
             outSymEnv := newSymEnv,
             f := f,
             nextId := cfg.nextId + 1,
             newFFVars := { outFFVar },
             newBoolVars := emptyBoolVarSet
    }
  | Except.ok _ => Except.error s!"seArrayReadConstIdx: variable '{a}' is not an array"



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
  match getVar symEnv a with
  | Except.error err => Except.error ("seArrayWriteNonConstIdx: failed to get array variable: " ++ err)
  | Except.ok (SymValue.ffArray arr) =>
    let arrayElements := arr.toList
    let arrayelementsAsTerms := arrayElements.map symVarToTerm
    let idxTerm ← simpleExprToTerm symEnv idx -- it is not a value
    let valueTerm ← simpleExprToTerm symEnv value -- the value to store
    -- create a new symbolic variables for all element of the array
    let newFFVars := List.range arr.size
                      |> List.map
                            (fun i => FFVar.mk (cfg.nextId+i)
                                               { src_info := md.src_info,
                                                 orig_name := s!"{a}_nc_write_{i}"
                                              })
    let newArrayelements := newFFVars.map (fun v => SymFFVar.var v)
    let newArr : SymFFArray c := newArrayelements.toArray
    let newSymEnv := setVar symEnv a (SymValue.ffArray newArr)
    -- a list wit equalities for all elements
    -- create a list
    let rec loop (l: List (FFTerm c)) (i : Nat ) : List (FFTerm c) :=
      match l with
      | [] => []
      | elem :: rest =>
          if ( i == 0 ) then
            -- this is the element to update
            valueTerm :: rest
          else
            elem :: (loop rest (i - 1))
    let indices := List.range arr.size
    let eqPairs := indices.map
          (fun i =>
              let arrElemAux := loop arrayelementsAsTerms i
              let eqConstraints := List.zip newFFVars arrElemAux
                          |> List.map (fun (newV, oldV) =>
                                let newTerm := FFTerm.var newV
                                let oldTerm := oldV
                                FFFormula.eq newTerm oldTerm)
              let f := eqConstraints.foldl (.and) FFFormula.true
              (i, f))
     let f := eqPairs.foldl (fun acc (i, eqF) =>
                let idxEq := FFFormula.eq idxTerm (.val i)
                .ite idxEq eqF acc
              ) FFFormula.false
     return {
                inSymEnv := symEnv,
                outSymEnv := newSymEnv,
                f := f,
                nextId := cfg.nextId + arr.size,
                newFFVars := newFFVars.foldl (fun acc v => acc.insert v) emptyFFVarSet
                newBoolVars := emptyBoolVarSet
            }
  | Except.ok _ => Except.error s!"seArrayWriteNonConstIdx: variable '{a}' is not an array"



def seArrayWrite {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD) (symEnv : SymEnv c)
  (a : VarID) (idx : SimpleExpr c) (value : SimpleExpr c)
  : Except String (CmdsSpec c) := do
  match seArrayWriteConstIdx cfg md symEnv a idx value with
  | Except.ok spec => return spec
  | Except.error _ => seArrayWriteNonConstIdx cfg md symEnv a idx value

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
