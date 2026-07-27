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

/-- The constraint gadget shared by `.uidiv`/`.uimod` with a constant, positive divisor `B`
    (`2 ≤ B.val < midpoint`): mints fresh `Q`/`R`, and asserts the division identity plus range
    bounds on `Q` that depend on which half of the field the dividend `A` falls in --
    `[0, (midpoint-1)/B]` when `A < midpoint`, `[midpoint/B, (p-1)/B]` otherwise. Splitting on `A`'s
    half (rather than using one bound covering the whole field) is what keeps the gadget both
    sound (every real quotient fits the bound for its half) and complete (no second, "wrapped"
    `(Q,R)` pair also satisfies the equation) -- see `SymExec/Correctness/ArithExprCorrectness.lean`
    for why a single-bound version can't have both. -/
def uiDivModGadget {c : ZKConfig} (sconf : SymExecConfig c) (A : SimpleSymVal c) (B : FF c) :
    FFFormula c × FFVar × FFVar :=
  let Q : FFVar := sconf.nextVarId
  let R : FFVar := sconf.nextVarId + 1
  let uLo : Nat := (c.midpoint - 1) / B.val
  let lo : Nat := c.midpoint / B.val
  let hi : Nat := (c.p - 1) / B.val
  let Aterm := simpleSymValToTerm A
  let eqn := FFFormula.eq Aterm (FFTerm.add (FFTerm.mul (FFTerm.var Q) (FFTerm.val B)) (FFTerm.var R))
  let rRange := FFFormula.range (FFTerm.var R) 0 (B.val - 1 : FF c)
  let lowBranch := FFFormula.and eqn (FFFormula.and rRange (FFFormula.range (FFTerm.var Q) 0 (uLo : FF c)))
  let highBranch :=
    FFFormula.and eqn (FFFormula.and rRange (FFFormula.range (FFTerm.var Q) (lo : FF c) (hi : FF c)))
  let isLow := FFFormula.range Aterm 0 (c.midpoint - 1 : FF c)
  (FFFormula.ite isLow lowBranch highBranch, Q, R)

def seExprUIDivWithFFPositiveConstantDivisor {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (s1 s2 : SimpleExpr c)
  : Except String (ExprSpec c) :=
  match tryEvalSimpleExprToFFValue symEnv s2 with
  | Except.error msg => Except.error msg
  | Except.ok B =>
      if B.val = 1 then
        match resolveSimpleExpr symEnv s1 with
        | Except.error msg => Except.error msg
        | Except.ok v =>
            Except.ok {
                outSymEnv := symEnv,
                f := FFFormula.true,
                nextVarId := sconf.nextVarId,
                result := v
            }
        -- B is in the range [1, midpoint-1], i.e. positive in the finite field
      else if B.val > 1 && B.val < c.midpoint then
        match resolveSimpleExpr symEnv s1 with
        | Except.error msg => Except.error msg
        | Except.ok A =>
            let (f, Q, _R) := uiDivModGadget sconf A B
            Except.ok {
                outSymEnv := symEnv,
                f := f,
                nextVarId := sconf.nextVarId + 2,
                result := SimpleSymVal.ffvar ⟨Q, none⟩
            }
      else
        Except.error
          s!"Error: divisor {B.val} is not in the range [1, midpoint-1] for .uidiv expression."

def seExprUIDivWithNonConstantDivisor {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (s1 s2 : SimpleExpr c)
    : Except String (ExprSpec c) :=
    Except.error "Integer division with non-constant divisor is not implemented yet"

def seExprUIDiv {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (e1 e2 : SimpleExpr c)
  : Except String (ExprSpec c) :=
    match seExprUIDivWithFFPositiveConstantDivisor md gconf sconf symEnv specs e1 e2 with
    | Except.ok result => Except.ok result
    | Except.error _ =>
        seExprUIDivWithNonConstantDivisor md gconf sconf symEnv specs e1 e2

/-- `.uimod`'s constant-positive-divisor path: shares `uiDivModGadget` with `.uidiv` (same fresh
    `Q`/`R`, same tie-back equation, same range bounds), but reports `R` as the result instead of
    `Q` -- and, unlike `.uidiv`, the `B.val = 1` identity case reports the constant `0` (`A mod 1 =
    0` for any `A`), not `A` itself. `s1` is still resolved in that case (not just discarded) so a
    malformed `e1` is caught symbolically the same way the concrete side would fail on it. -/
def seExprUIModWithFFPositiveConstantDivisor {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (s1 s2 : SimpleExpr c)
  : Except String (ExprSpec c) :=
  match tryEvalSimpleExprToFFValue symEnv s2 with
  | Except.error msg => Except.error msg
  | Except.ok B =>
      if B.val = 1 then
        match resolveSimpleExpr symEnv s1 with
        | Except.error msg => Except.error msg
        | Except.ok _v =>
            Except.ok {
                outSymEnv := symEnv,
                f := FFFormula.true,
                nextVarId := sconf.nextVarId,
                result := SimpleSymVal.const 0
            }
        -- B is in the range [1, midpoint-1], i.e. positive in the finite field
      else if B.val > 1 && B.val < c.midpoint then
        match resolveSimpleExpr symEnv s1 with
        | Except.error msg => Except.error msg
        | Except.ok A =>
            let (f, _Q, R) := uiDivModGadget sconf A B
            Except.ok {
                outSymEnv := symEnv,
                f := f,
                nextVarId := sconf.nextVarId + 2,
                result := SimpleSymVal.ffvar ⟨R, none⟩
            }
      else
        Except.error
          s!"Error: divisor {B.val} is not in the range [1, midpoint-1] for .uimod expression."

def seExprUIModWithNonConstantDivisor {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (s1 s2 : SimpleExpr c)
    : Except String (ExprSpec c) :=
    Except.error "Integer modulo with non-constant divisor is not implemented yet"

def seExprUIMod {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (e1 e2 : SimpleExpr c)
  : Except String (ExprSpec c) :=
    match seExprUIModWithFFPositiveConstantDivisor md gconf sconf symEnv specs e1 e2 with
    | Except.ok result => Except.ok result
    | Except.error _ =>
        seExprUIModWithNonConstantDivisor md gconf sconf symEnv specs e1 e2

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
