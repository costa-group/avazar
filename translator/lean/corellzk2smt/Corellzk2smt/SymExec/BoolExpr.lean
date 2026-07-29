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

/- s1 < s2 where s2 is a constant -/
def seExprLtSignedConstantUpperBound {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (s1 s2 : SimpleExpr c)
  : Except String (ExprSpec c) :=
    match tryEvalSimpleExprToFFValue symEnv s2 with
    | Except.error msg => Except.error msg
    | Except.ok rhs =>
        match resolveSimpleExpr symEnv s1 with
        | Except.error msg => Except.error msg
        | Except.ok lhs =>
            let lhsTerm := simpleSymValToTerm lhs
            let outFFVar : FFVar := sconf.nextVarId
            match bool_ffterm gconf sconf (FFTerm.var outFFVar) with
            | Except.error msg => Except.error msg
            | Except.ok fbool =>
                -- `rhs - 1` wraps around (into the positive half) if `rhs` is itself already the
                -- field's minimum signed value -- nothing is less than the minimum, so that case
                -- is handled directly (the condition is simply `false`) instead of falling
                -- through to the (unsound) `rhs - 1` range check.
                let cond :=
                  if rhs = (c.midpoint : FF c) then
                    FFFormula.false
                  else
                    FFFormula.range lhsTerm (c.midpoint : FF c) (rhs-1)
                let f := FFFormula.and
                            (FFFormula.eq
                                (FFTerm.var outFFVar)
                                (FFTerm.ite cond (FFTerm.val 1) (FFTerm.val 0)))
                            fbool
                Except.ok {
                    outSymEnv := symEnv,
                    f := f,
                    nextVarId := sconf.nextVarId + 1,
                    result := SimpleSymVal.ffvar ⟨outFFVar, none⟩
                }

/- s1 < s2 where s1 is a constant -/
def seExprLtSignedConstantLowerBound {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (s1 s2 : SimpleExpr c)
  : Except String (ExprSpec c) :=
    match tryEvalSimpleExprToFFValue symEnv s1 with
    | Except.error msg => Except.error msg
    | Except.ok lhs =>
        match resolveSimpleExpr symEnv s2 with
        | Except.error msg => Except.error msg
        | Except.ok rhs =>
            let rhsTerm := simpleSymValToTerm rhs
            let outFFVar : FFVar := sconf.nextVarId
            match bool_ffterm gconf sconf (FFTerm.var outFFVar) with
            | Except.error msg => Except.error msg
            | Except.ok fbool =>
                -- `lhs + 1` wraps around (into the negative half) if `lhs` is itself already the
                -- field's maximum signed value -- nothing exceeds the maximum, so that case is
                -- handled directly (the condition is simply `false`) instead of falling through
                -- to the (unsound) `lhs + 1` range check.
                let cond :=
                  if lhs = (c.midpoint - 1 : FF c) then
                    FFFormula.false
                  else
                    FFFormula.range rhsTerm (lhs+1) (c.midpoint-1 : FF c)
                let f := FFFormula.and
                            (FFFormula.eq
                                (FFTerm.var outFFVar)
                                (FFTerm.ite cond (FFTerm.val 1) (FFTerm.val 0)))
                            fbool
                Except.ok {
                    outSymEnv := symEnv,
                    f := f,
                    nextVarId := sconf.nextVarId + 1,
                    result := SimpleSymVal.ffvar ⟨outFFVar, none⟩
                }

/-

s1<s2

s1 is negative, s2 is positive => s1<s2 is true
s1 is positive, s2 is negative => s1<s2 is false
other wise, we compute the difference s1-s2 and check if it is negative.

-/
def seExprLtSignedNonConstant {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (s1 s2 : SimpleExpr c)
  : Except String (ExprSpec c) :=
    match resolveSimpleExpr symEnv s1 with
    | Except.error msg => Except.error msg
    | Except.ok lhs =>
        match resolveSimpleExpr symEnv s2 with
        | Except.error msg => Except.error msg
        | Except.ok rhs =>
            let lhsTerm := simpleSymValToTerm lhs
            let rhsTerm := simpleSymValToTerm rhs
            let outFFVar : FFVar := sconf.nextVarId
            match bool_ffterm gconf sconf (FFTerm.var outFFVar) with
            | Except.error msg => Except.error msg
            | Except.ok fbool =>
                let s1IsPositive := FFFormula.range lhsTerm 0 (c.midpoint-1 : FF c)
                let s1IsNegative := FFFormula.range lhsTerm (c.midpoint : FF c) (c.p-1 : FF c)
                let s2IsPositive := FFFormula.range rhsTerm 0 (c.midpoint-1 : FF c)
                let s2IsNegative := FFFormula.range rhsTerm (c.midpoint : FF c) (c.p-1 : FF c)
                let diffTerm := FFTerm.sub lhsTerm rhsTerm
                let diffTermIsNeg := (FFFormula.range diffTerm (c.midpoint : FF c) (c.p-1 : FF c))
                let f := FFFormula.and
                          (FFFormula.eq
                          (FFTerm.var outFFVar)
                          (FFTerm.ite
                            (FFFormula.and s1IsNegative s2IsPositive)
                            (FFTerm.val 1)
                            (FFTerm.ite
                                (FFFormula.and s1IsPositive s2IsNegative)
                                (FFTerm.val 0)
                                (FFTerm.ite
                                    diffTermIsNeg
                                    (FFTerm.val 1)
                                    (FFTerm.val 0)))))
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
    (s1 s2 : SimpleExpr c)
  : Except String (ExprSpec c) :=
  match seExprLtSignedConstantUpperBound md gconf sconf symEnv specs s1 s2 with
  | Except.ok res => Except.ok res
  | Except.error _ =>
    match seExprLtSignedConstantLowerBound md gconf sconf symEnv specs s1 s2 with
    | Except.ok res => Except.ok res
    | Except.error _ =>
      seExprLtSignedNonConstant md gconf sconf symEnv specs s1 s2

def seExprGtSigned {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (s1 s2 : SimpleExpr c)
  : Except String (ExprSpec c) :=
    seExprLtSigned md gconf sconf symEnv specs s2 s1

def seExprLeSigned {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (s1 s2 : SimpleExpr c)
  : Except String (ExprSpec c) :=
  match seExprGtSigned md gconf sconf symEnv specs s1 s2 with
  | Except.error msg => Except.error msg
  | Except.ok gtSpec =>
    let outFFVar : FFVar := gtSpec.nextVarId
    match bool_ffterm gconf sconf (FFTerm.var outFFVar) with
    | Except.error msg => Except.error msg
    | Except.ok fbool =>
        let f := FFFormula.and
                      gtSpec.f
                      (FFFormula.and
                        (FFFormula.eq
                          (FFTerm.var outFFVar)
                          (FFTerm.sub (FFTerm.val 1) (simpleSymValToTerm gtSpec.result)))
                        fbool)
        Except.ok {
            outSymEnv := gtSpec.outSymEnv,
            f := f,
            nextVarId := gtSpec.nextVarId + 1,
            result := SimpleSymVal.ffvar ⟨outFFVar, none⟩
        }

def seExprGeSigned {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (s1 s2 : SimpleExpr c)
  : Except String (ExprSpec c) :=
    seExprLeSigned md gconf sconf symEnv specs s2 s1

end Corellzk2smt.SymExec.BigStep
