import Corellzk2smt.Basic
import Corellzk2smt.Config
import Corellzk2smt.SymExec.Basic
import Corellzk2smt.SymExec.Common
import Corellzk2smt.FFConstraints.Basic
import Corellzk2smt.Language.Core.Syntax.AST
import Corellzk2smt.Language.Core.Semantics.Basic

/-!
Symbolic execution of the arithmetic operators (`+ - * / ^ %/ //` and unary `-`, plus the bare
`Expr.id` case), dispatched to from `seEvalExpr` (`SymExec/Assignment.lean`). Each `seExprXXX` is
currently a permanent `"Not implemented yet"` stub -- `seEvalAssignmentConst` (`Assignment.lean`)
already handles the case where both operands fully constant-fold; these are for the general,
not-necessarily-constant case, still to be built.
-/

namespace Corellzk2smt.SymExec.BigStep

open Corellzk2smt.Config (GlobalConfig)
open Corellzk2smt.Language.Core.Syntax.AST
open Corellzk2smt.Language.Core.Semantics.Basic
open Corellzk2smt.SymExec.Basic
open Corellzk2smt.FFConstraints.Basic

def seExprAdd {c : ZKConfig}
    (_md : CmdMD)
    (_gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (_specs : List (FuncSpec c))
    (s1 s2 : SimpleExpr c)
  : Except String (ExprSpec c) :=
    match resolveSimpleExpr symEnv s1 with
    | Except.error msg => Except.error msg
    | Except.ok v1 =>
        match resolveSimpleExpr symEnv s2 with
        | Except.error msg => Except.error msg
        | Except.ok v2 =>
            let v1Term := simpleSymValToTerm v1
            let v2Term := simpleSymValToTerm v2
            let outFFVar : FFVar := sconf.nextVarId
            let f := FFFormula.eq (FFTerm.var outFFVar) (FFTerm.add v1Term v2Term) -- outVar = v1 + v2
            Except.ok {
                outSymEnv := symEnv,
                f := f,
                nextVarId := sconf.nextVarId + 1,
                result := SimpleSymVal.ffvar ⟨outFFVar, none⟩
            }

def seExprSub {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (e1 e2 : SimpleExpr c)
  : Except String (ExprSpec c) :=
  Except.error "Not implemented yet"

def seExprMul {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (e1 e2 : SimpleExpr c)
  : Except String (ExprSpec c) :=
  Except.error "Not implemented yet"

def seExprDiv {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (e1 e2 : SimpleExpr c)
  : Except String (ExprSpec c) :=
  Except.error "Not implemented yet"

def seExprPow {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (e1 e2 : SimpleExpr c)
  : Except String (ExprSpec c) :=
  Except.error "Not implemented yet"

def seExprUIMod {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (e1 e2 : SimpleExpr c)
  : Except String (ExprSpec c) :=
  Except.error "Not implemented yet"

def seExprUIDiv {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (e1 e2 : SimpleExpr c)
  : Except String (ExprSpec c) :=
  Except.error "Not implemented yet"

def seExprNeg {c : ZKConfig}
    (_md : CmdMD)
    (_gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (_specs : List (FuncSpec c))
    (s : SimpleExpr c)
  : Except String (ExprSpec c) :=
    match resolveSimpleExpr symEnv s with
    | Except.error msg => Except.error msg
    | Except.ok v =>
      let vTerm := simpleSymValToTerm v
      let outFFVar : FFVar := sconf.nextVarId
      let f := FFFormula.eq (FFTerm.var outFFVar) (FFTerm.neg vTerm) -- outVar = -v
      Except.ok {
          outSymEnv := symEnv,
          f := f,
          nextVarId := sconf.nextVarId + 1,
          result := SimpleSymVal.ffvar ⟨outFFVar, none⟩
      }

def seExprId {c : ZKConfig}
    (_md : CmdMD)
    (_gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (_specs : List (FuncSpec c))
    (s : SimpleExpr c)
  : Except String (ExprSpec c) :=
  match resolveSimpleExpr symEnv s with
  | Except.error msg => Except.error msg
  | Except.ok v =>
      Except.ok {
          outSymEnv := symEnv,
          f := FFFormula.true,
          nextVarId := sconf.nextVarId,
          result := v
      }

end Corellzk2smt.SymExec.BigStep
