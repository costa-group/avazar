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
            let f := FFFormula.eq (FFTerm.var outFFVar) (FFTerm.sub v1Term v2Term) -- outVar = v1 - v2
            Except.ok {
                outSymEnv := symEnv,
                f := f,
                nextVarId := sconf.nextVarId + 1,
                result := SimpleSymVal.ffvar ⟨outFFVar, none⟩
            }

def seExprMul {c : ZKConfig}
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
            let f := FFFormula.eq (FFTerm.var outFFVar) (FFTerm.mul v1Term v2Term) -- outVar = v1 * v2
            Except.ok {
                outSymEnv := symEnv,
                f := f,
                nextVarId := sconf.nextVarId + 1,
                result := SimpleSymVal.ffvar ⟨outFFVar, none⟩
            }
--           f := FFFormula.eq (FFTerm.mul (FFTerm.var outFFVar) v2) v1,  -- (outVar = v1 / v2)

def seExprDiv {c : ZKConfig}
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
            let f := FFFormula.ite
                      (FFFormula.eq v2Term (FFTerm.val 0))
                      FFFormula.false
                      (FFFormula.eq (FFTerm.mul (FFTerm.var outFFVar) v2Term) v1Term)
            Except.ok {
                outSymEnv := symEnv,
                f := f,
                nextVarId := sconf.nextVarId + 1,
                result := SimpleSymVal.ffvar ⟨outFFVar, none⟩
            }


/-- Term-level repeated multiplication: `ffTermPow t n` denotes `t^n` -- the constraint-level
    counterpart of `evalPow`'s `v1 ^ v2.val`, built once as a top-level function (rather than a
    `seExprPowWithConstantExponent`-local `let rec`) so its evaluation can be proved correct by
    plain induction on `n` (`ffTermPow_correct`, `SymExec/Correctness/ArithExprCorrectness.lean`). -/
def ffTermPow {c : ZKConfig} (t : FFTerm c) : Nat → FFTerm c
  | 0 => FFTerm.val 1
  | n + 1 => FFTerm.mul t (ffTermPow t n)

def seExprPowWithConstantExponent {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (s1 s2 : SimpleExpr c)
  : Except String (ExprSpec c) :=
    match tryEvalSimpleExprToFFValue symEnv s2 with
    | Except.error msg => Except.error msg
    | Except.ok power =>
        match resolveSimpleExpr symEnv s1 with
        | Except.error msg => Except.error msg
        | Except.ok base =>
            let outFFVar : FFVar := sconf.nextVarId
            let baseTerm := simpleSymValToTerm base
            let f := FFFormula.eq (FFTerm.var outFFVar) (ffTermPow baseTerm power.val)
            Except.ok {
                outSymEnv := symEnv,
                f := f,
                nextVarId := sconf.nextVarId + 1,
                result := SimpleSymVal.ffvar ⟨outFFVar, none⟩
            }

def seExprPowWithNonConstantExponent {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (s1 s2 : SimpleExpr c)
  : Except String (ExprSpec c) :=
    Except.error "Power with non-constant exponent is not implemented yet"

def seExprPow {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (s1 s2 : SimpleExpr c)
  : Except String (ExprSpec c) :=
    match seExprPowWithConstantExponent md gconf sconf symEnv specs s1 s2 with
    | Except.ok result => Except.ok result
    | Except.error _ =>
        seExprPowWithNonConstantExponent md gconf sconf symEnv specs s1 s2

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
