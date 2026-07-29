import Corellzk2smt.Basic
import Corellzk2smt.Config
import Corellzk2smt.SymExec.Basic
import Corellzk2smt.SymExec.Common
import Corellzk2smt.FFConstraints.Basic
import Corellzk2smt.Language.Core.Syntax.AST


namespace Corellzk2smt.SymExec.BigStep


open Corellzk2smt.Config (GlobalConfig)
open Corellzk2smt.Language.Core.Syntax.AST
open Corellzk2smt.SymExec.Basic
open Corellzk2smt.FFConstraints.Basic


def seNewArray {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (id : VarID)
    (size : SimpleExpr c)
    : Except String (CmdsSpec c) :=
    match tryEvalSimpleExprToFFValue symEnv size with
    | Except.error msg => Except.error msg
    | Except.ok sizeValue =>
      let arr : SymArray c := (List.replicate sizeValue.val (.const 0)).toArray
      let newSymEnv := setVar symEnv id (SymValue.array arr)
      Except.ok {
        inSymEnv := symEnv,
        outSymEnv := newSymEnv,
        f := .true,
        nextVarId := sconf.nextVarId
      }


def seReadArrayConstantIdx {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (out : VarID)
    (a : VarID)
    (index : SimpleExpr c)
    : Except String (CmdsSpec c) :=
    match tryEvalSimpleExprToFFValue symEnv index with
    | Except.error msg => Except.error msg
    | Except.ok indexValue =>
      match getVar symEnv a with
      | Except.error msg => Except.error msg
      | Except.ok (SymValue.array arr) =>
        if h: indexValue.val < arr.size then
          let value := arr[indexValue.val]'h
          let newSymEnv := setVar symEnv out (.simple value)
          Except.ok {
            inSymEnv := symEnv,
            outSymEnv := newSymEnv,
            f := .true,
            nextVarId := sconf.nextVarId
          }
        else
          Except.error s!"Index {indexValue.val} is out of bounds for array {a} of size {arr.size}"
      | Except.ok _ => Except.error s!"Variable {a} is not an array"

def seReadArrayNonConstantIdx {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (out : VarID)
    (a : VarID)
    (index : SimpleExpr c)
    : Except String (CmdsSpec c) :=
  Except.error "seReadArray: TBD"


def seReadArray {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (out : VarID)
    (a : VarID)
    (index : SimpleExpr c)
    : Except String (CmdsSpec c) :=
  match seReadArrayConstantIdx md gconf sconf symEnv specs out a index with
  | Except.ok spec => Except.ok spec
  | Except.error _ =>
    seReadArrayNonConstantIdx md gconf sconf symEnv specs out a index



def seWriteArrayConstantIdx {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (a : VarID)
    (index : SimpleExpr c)
    (value : SimpleExpr c)
    : Except String (CmdsSpec c) :=
    match tryEvalSimpleExprToFFValue symEnv index with
    | Except.error msg => Except.error msg
    | Except.ok indexValue =>
      match getVar symEnv a with
      | Except.error msg => Except.error msg
      | Except.ok (SymValue.array arr) =>
        if h: indexValue.val < arr.size then
          match resolveSimpleExpr symEnv value with
          | Except.error msg => Except.error msg
          | Except.ok v =>
            let newArr := arr.set indexValue.val v
            let newSymEnv := setVar symEnv a (SymValue.array newArr)
            Except.ok {
              inSymEnv := symEnv,
              outSymEnv := newSymEnv,
              f := .true,
              nextVarId := sconf.nextVarId
            }
        else
          Except.error s!"Index {indexValue.val} is out of bounds for array {a} of size {arr.size}"
      | Except.ok _ => Except.error s!"Variable {a} is not an array"

def seWriteArrayNonConstantIdx {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (a : VarID)
    (index : SimpleExpr c)
    (value : SimpleExpr c)
    : Except String (CmdsSpec c) :=
  Except.error "seWriteArray: TBD"

def seWriteArray {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (a : VarID)
    (index : SimpleExpr c)
    (value : SimpleExpr c)
    : Except String (CmdsSpec c) :=
  match seWriteArrayConstantIdx md gconf sconf symEnv specs a index value with
  | Except.ok spec => Except.ok spec
  | Except.error _ =>
    seWriteArrayNonConstantIdx md gconf sconf symEnv specs a index value

def seCopyArray {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (out : VarID)
    (a : VarID)
    : Except String (CmdsSpec c) :=
    match getVar symEnv a with
    | Except.error msg => Except.error msg
    | Except.ok arr =>
      let newSymEnv := setVar symEnv out arr
      Except.ok {
        inSymEnv := symEnv,
        outSymEnv := newSymEnv,
        f := .true,
        nextVarId := sconf.nextVarId
      }

end Corellzk2smt.SymExec.BigStep
