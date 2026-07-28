import Corellzk2smt.Basic
import Corellzk2smt.Config
import Corellzk2smt.SymExec.Basic
import Corellzk2smt.SymExec.Common
import Corellzk2smt.FFConstraints.Basic
import Corellzk2smt.Language.Core.Syntax.AST
import Corellzk2smt.Language.Core.Semantics.Basic
import Corellzk2smt.SymExec.BinaryExpansion

/-!
Symbolic execution of the boolean-valued operators (`| & = != < <= > >=` and unary boolean
negation `!`), dispatched to from `seEvalExpr` (`SymExec/Assignment.lean`). Each `seExprXXX` is
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
open Corellzk2smt.SymExec.BinaryExpansion

def seExprBor {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
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
            match bool_ffterm gconf sconf (FFTerm.var outFFVar) with
            | Except.error msg => Except.error msg
            | Except.ok fbool =>
                let f := FFFormula.and
                            (FFFormula.eq
                              (FFTerm.var outFFVar)
                              (FFTerm.ite
                                 (.and (.eq v1Term (.val 0)) (.eq v2Term (.val 0)))
                                 (.val 0)
                                 (.val 1)))
                            fbool
                Except.ok {
                    outSymEnv := symEnv,
                    f := f,
                    nextVarId := sconf.nextVarId + 1,
                    result := SimpleSymVal.ffvar ⟨outFFVar, none⟩
                }

def seExprBAnd {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
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
            match bool_ffterm gconf sconf (FFTerm.var outFFVar) with
            | Except.error msg => Except.error msg
            | Except.ok fbool =>
                let f := FFFormula.and
                            (FFFormula.eq
                              (FFTerm.var outFFVar)
                              (FFTerm.ite
                                 (.or (.eq v1Term (.val 0)) (.eq v2Term (.val 0)))
                                 (.val 0)
                                 (.val 1)))
                            fbool
                Except.ok {
                    outSymEnv := symEnv,
                    f := f,
                    nextVarId := sconf.nextVarId + 1,
                    result := SimpleSymVal.ffvar ⟨outFFVar, none⟩
                }

def seExprBNeg {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (s : SimpleExpr c)
  : Except String (ExprSpec c) :=
    match resolveSimpleExpr symEnv s with
    | Except.error msg => Except.error msg
    | Except.ok v =>
        let vTerm := simpleSymValToTerm v
        let outFFVar : FFVar := sconf.nextVarId
        match bool_ffterm gconf sconf (FFTerm.var outFFVar) with
        | Except.error msg => Except.error msg
        | Except.ok fbool =>
            let f := FFFormula.and
                            (FFFormula.eq
                              (FFTerm.var outFFVar)
                              (FFTerm.ite
                                 (.eq vTerm (.val 0))
                                 (.val 1)
                                 (.val 0)))
                            fbool
            Except.ok {
              outSymEnv := symEnv,
              f := f,
              nextVarId := sconf.nextVarId + 1,
              result := SimpleSymVal.ffvar ⟨outFFVar, none⟩
            }

/-- `.eq`'s symbolic encoding: `evalEq` produces the *value* `1` or `0` (not a bare constraint that
    `v1 = v2` must hold), so the formula has to actually tie a fresh `outFFVar` to that value via a
    term-level `ite` on the equality test -- `outFFVar = 1` when `v1Term = v2Term` holds, `outFFVar
    = 0` otherwise. No range constraint is needed on `outFFVar`: the `ite` term itself can only
    ever evaluate to `1` or `0`, for any `v1`/`v2`. -/
def seExprEq {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
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
            match bool_ffterm gconf sconf (FFTerm.var outFFVar) with
            | Except.error msg => Except.error msg
            | Except.ok fbool =>
                let f := FFFormula.and
                            (FFFormula.eq
                                (FFTerm.var outFFVar)
                                (FFTerm.ite (FFFormula.eq v1Term v2Term)
                                  (FFTerm.val 1) (FFTerm.val 0)))
                            fbool
                Except.ok {
                    outSymEnv := symEnv,
                    f := f,
                    nextVarId := sconf.nextVarId + 1,
                    result := SimpleSymVal.ffvar ⟨outFFVar, none⟩
                }


/-- Mirror of `seExprEq`, for `evalNeq` (`outFFVar = 1` when `v1Term ≠ v2Term`, `0` otherwise) --
    same `ite`-on-equality shape (branches swapped) plus the same `bool_ffterm` boolean tag on
    `outFFVar`. -/
def seExprNeq {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
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
            match bool_ffterm gconf sconf (FFTerm.var outFFVar) with
            | Except.error msg => Except.error msg
            | Except.ok fbool =>
                let f := FFFormula.and
                            (FFFormula.eq (FFTerm.var outFFVar)
                                (FFTerm.ite (FFFormula.eq v1Term v2Term)
                                  (FFTerm.val 0) (FFTerm.val 1)))
                            fbool
                Except.ok {
                    outSymEnv := symEnv,
                    f := f,
                    nextVarId := sconf.nextVarId + 1,
                    result := SimpleSymVal.ffvar ⟨outFFVar, none⟩
                }


def seExprLtSigned {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (e1 e2 : SimpleExpr c)
  : Except String (ExprSpec c) :=
  Except.error "Not implemented yet"

def seExprLeSigned {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (e1 e2 : SimpleExpr c)
  : Except String (ExprSpec c) :=
  Except.error "Not implemented yet"

def seExprGtSigned {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (e1 e2 : SimpleExpr c)
  : Except String (ExprSpec c) :=
  Except.error "Not implemented yet"

def seExprGeSigned {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (e1 e2 : SimpleExpr c)
  : Except String (ExprSpec c) :=
  Except.error "Not implemented yet"

end Corellzk2smt.SymExec.BigStep
