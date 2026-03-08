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

/- Recall that boolean values are 0 for false and any non-zero value for true.

   This means that A and B, for example, cannot be encoded as A*B, because no
   one guarantees that A and B are forced to be boolean in the constraints.

-/

/- Equality of boolean expressions.

   1 if the are equal, 0 otherwise.
-/

def sEvalEq {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  return {
          inSymEnv := senv,
          f := FFFormula.eq
                    (FFTerm.var outFFVar)
                    (FFTerm.ite (FFFormula.eq v1 v2) (.val 1) (.val 0))
          resVar := outFFVar,
          nextId := cfg.nextId
  }

/- Non-equality of boolean expressions.

   0 if they are equal, 1 otherwise.
-/

def sEvalNeq {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  return {
          inSymEnv := senv,
          f := FFFormula.eq
                 (FFTerm.var outFFVar)
                 (FFTerm.ite (FFFormula.eq v1 v2) (.val 0) (.val 1)),
          resVar := outFFVar,
          nextId := cfg.nextId
  }


/- Boolean OR operation.

   0 if both are 0, 1 otherwise.
-/
def sEvalBor {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  return {
          inSymEnv := senv,
          f := FFFormula.eq
                 (FFTerm.var outFFVar)
                 (FFTerm.ite
                    (.and (.eq v1 (.val 0)) (.eq v2 (.val 0)))
                    (.val 0)
                    (.val 1)),
          resVar := outFFVar,
          nextId := cfg.nextId
  }

/- Boolean AND operation.

   0 if either is 0, 1 otherwise.
-/
def sEvalBAnd {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  return {
          inSymEnv := senv,
          f := FFFormula.eq
                 (FFTerm.var outFFVar)
                 (FFTerm.ite
                    (.or (.eq v1 (.val 0)) (.eq v2 (.val 0)))
                    (.val 0)
                    (.val 1)),
          resVar := outFFVar,
          nextId := cfg.nextId
  }

/- Boolean negation operation.

   1 if the input is 0, and 0 otherwise.
-/
def sEvalBNeg {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (s : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v ← simpleExprToTerm senv s
  return {
          inSymEnv := senv,
          f := FFFormula.eq (FFTerm.var outFFVar)
                 (FFTerm.ite
                    (.eq v (.val 0))
                    (.val 1)
                    (.val 0)),
          resVar := outFFVar,
          nextId := cfg.nextId
  }



/- Unsigned comparison-/


/-
  Special case of unsigned x < y when the upper bound is a constant.

  x < v is encoded as:

  v = 0 -> false
  v > 0 -> range(x, 0, v-1)
-/
def sEvalLtUnSignedConstLeft {c : ZKConfig}
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
  Special case of unsigned x < y when the lower bound is a constant.

  v < x is encoded as:

  v = c.p-1 -> false
  v < c.p-1 -> range(x, v+1, c.p-1)
-/
def sEvalLtUnSignedConstRight {c : ZKConfig}
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

/- Compare x < y bitwise. We compare the bits of x and y from the
   most significant bit to the least significant bit.
-/
def sEvalLtUnSignedBitCmp {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  let bits1Spec := bitify cfg md v1 -- bitify v1
  let cfg' := { cfg with nextId := bits1Spec.nextId }
  let bits2Spec := bitify cfg' md v2 -- bitify v2
  let ite := List.foldl -- construct the ite expression for bitwise comparison
              (fun acc (b1, b2) =>
                  FFTerm.ite
                    (.and (.eq b1 (.val 0)) (.eq b2 (.val 1)))
                    (.val 1)
                    (.ite (.and (.eq b1 (.val 1)) (.eq b2 (.val 0))) (.val 0) acc))
              (.val 0)
              (List.zip bits1Spec.bits bits2Spec.bits)
  let newFFVars := bits1Spec.newFFVars ∪ bits2Spec.newFFVars
  let f := .and bits1Spec.f (.and bits2Spec.f (.eq (FFTerm.var outFFVar) ite))
  return {
          inSymEnv := senv,
          f := f
          resVar := outFFVar,
          nextId := bits2Spec.nextId,
          newFFVars := newFFVars,
          newBoolVars := ∅
  }

/- General case of unsigned x < y. We first check if we can apply the special cases
   for constants, and if not, we fall back to bitwise comparison.
-/
def sEvalLtUnSigned {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  match sEvalLtUnSignedConstLeft cfg md senv s1 s2 outFFVar with
  | Except.ok spec => return spec
  | Except.error _ =>
    match sEvalLtUnSignedConstRight cfg md senv s1 s2 outFFVar with
    | Except.ok spec => return spec
    | Except.error _ => sEvalLtUnSignedBitCmp cfg md senv s1 s2 outFFVar

/- x <= y is be encoded as ~(y < x), which is 1 minus the result
   variable of (y < x).
-/
def sEvalLeUnSigned {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let outFFVarLt : FFVar := { id := cfg.nextId,
                              meta_data := { src_info := md.src_info, orig_name := "gt_aux" }
                            }
  -- increment the nextId in the config for the next variable
  let cfg' : SymExecConfig c := { cfg with nextId := cfg.nextId + 1 }
  let ltSpec ← sEvalLtUnSigned cfg' md senv s2 s1 outFFVarLt
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
def sEvalGtUnSigned {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  sEvalLtUnSigned cfg md senv s2 s1 outFFVar

/- Greater than equal simply uses the encoding of less than equal
   after swapping the operands -/
def sEvalGeUnSigned {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  sEvalLeUnSigned cfg md senv s2 s1 outFFVar

/- Signed comparison-/

/- Special case of signed x < y when the upper bound is a constant.

   x < v is encoded as:

     v = c.midpoint -> false
     v > c.midpoint -> range(x, midpoint, v-1)
     v = 0 -> range(x, midpoint, p-1)
     0 < v < c.midpoint -> range(x, 0, v-1) or range(x, c.midpoint, p-1)
-/
def sEvalLtSignedConstLeft {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToFF senv s2
  let f :=  if v2.val == c.midpoint then
              FFFormula.false -- s1 < midpoint is false, midpoint is the smallest negative number
            else if v2.val > c.midpoint then
              (FFFormula.eq (FFTerm.var outFFVar)
                            (.ite (.range v1 c.midpoint (v2.val-1)) (.val 1) (.val 0))) -- negative
            else if v2.val == 0 then
              (FFFormula.eq (FFTerm.var outFFVar)
                            (.ite (.range v1 c.midpoint (c.p-1)) (.val 1) (.val 0))) -- any negative
           else
             FFFormula.eq (FFTerm.var outFFVar) -- [0,v-1] or [midpoint, p-1]
                          (.ite (.or (.range v1 0 (v2-1)) (.range v1 c.midpoint (c.p-1))) (.val 1) (.val 0))
  return {
          inSymEnv := senv,
          f := f,
          nextId := cfg.nextId,
          resVar := outFFVar
        }

/- Special case of signed x < y when the lower bound is a constant.

   v < x is encoded as:

     v = midpoint-1 -> false
     v < c.midpoint-1 -> range(x, v+1,midpoint-1)
     v = c.p-1 -> range(x, 0, midpoint-1)
     v >= c.midpoint -> range(x, v+1, p-1) or range(x, 0, midpoint-1)
-/
def sEvalLtSignedConstRight {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToFF senv s1
  let v2 ← simpleExprToTerm senv s2
  let f := if (v1.val == c.midpoint-1) then
             FFFormula.false -- c.midpoint-1 is the largest positive
           else if (v1.val < c.midpoint-1) then
             FFFormula.eq (FFTerm.var outFFVar)
                          (.ite (.range v2 (v1+1) (c.midpoint-1)) (.val 1) (.val 0))
           else if (v1.val == c.p-1) then
             FFFormula.eq (FFTerm.var outFFVar)
                          (.ite (.range v2 0 (c.midpoint-1)) (.val 1) (.val 0))
           else
             FFFormula.eq (FFTerm.var outFFVar)
                          (.ite (.or (.range v2 (v1+1) (c.p-1)) (.range v2 0 (c.midpoint-1)))
                                (.val 1)
                                (.val 0))
  return {
          inSymEnv := senv,
          f := f,
          nextId := cfg.nextId,
          resVar := outFFVar
        }

/- Encoding signed x < y using the unsigned version.

   A=1 if x is non-negative, 0 otherwise
   B=1 if y is non-negative, 0 otherwise
   C  is the result of unsigned x < y

   the final result is encoded as:

    if A=B then C else 1-A
-/
def sEvalLtSignedBitCmp {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  -- A
  let ffVarIsS1Pos : FFVar := { id := cfg.nextId,
                                meta_data := { src_info := md.src_info, orig_name := "isS1Pos" }
                              }
  -- B
  let ffVarIsS2Pos : FFVar := { id := cfg.nextId + 1,
                                meta_data := { src_info := md.src_info, orig_name := "isS2Pos" }
                              }
  -- C
  let ffVarLt : FFVar := { id := cfg.nextId + 2,
                              meta_data := { src_info := md.src_info, orig_name := "ltAux" }
                            }
  let cfg' := { cfg with nextId := cfg.nextId + 3 }
  let isS1Pos ← sEvalLtUnSigned cfg' md senv s1 (SimpleExpr.val c.midpoint) ffVarIsS1Pos
  let cfg'' := { cfg' with nextId := isS1Pos.nextId }
  let isS2Pos ← sEvalLtUnSigned cfg'' md senv s2 (SimpleExpr.val c.midpoint) ffVarIsS2Pos
  let cfg''' := { cfg'' with nextId := isS2Pos.nextId }
  let ltSpec ← sEvalLtUnSignedBitCmp cfg''' md senv s1 s2 ffVarLt
  -- if A=B then C else 1-A
  let f := FFFormula.eq (FFTerm.var outFFVar)
           (FFTerm.ite
             (.eq (FFTerm.var ffVarIsS1Pos) (FFTerm.var ffVarIsS2Pos))
             (FFTerm.var ffVarLt)
             (FFTerm.sub (.val 1) (FFTerm.var ffVarIsS1Pos)))
  return {
          inSymEnv := senv,
          f := .and isS1Pos.f (.and isS2Pos.f (.and ltSpec.f f)),
          resVar := outFFVar
          nextId := ltSpec.nextId,
          newFFVars := isS1Pos.newFFVars ∪ isS2Pos.newFFVars ∪ ltSpec.newFFVars ∪
                       {ffVarIsS1Pos, ffVarIsS2Pos, ffVarLt},
          newBoolVars := isS1Pos.newBoolVars ∪ isS2Pos.newBoolVars ∪ ltSpec.newBoolVars
        }

/- General case of x < y. We first try the special cases with constants, and if
   those don't apply, we use the bitwise comparison. -/
def sEvalLtSigned {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  match sEvalLtSignedConstLeft cfg md senv s1 s2 outFFVar with
  | Except.ok spec => return spec
  | Except.error _ =>
    match sEvalLtSignedConstRight cfg md senv s1 s2 outFFVar with
    | Except.ok spec => return spec
    | Except.error _ => sEvalLtSignedBitCmp cfg md senv s1 s2 outFFVar

/- x<=y is be encoded as 1 minus the result variable of (y < x).
-/
def sEvalLeSigned {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let outFFVarLt : FFVar := { id := cfg.nextId,
                              meta_data := { src_info := md.src_info, orig_name := "gt_aux" }
                            }
  -- increment the nextId in the config for the next variable
  let cfg' : SymExecConfig c := { cfg with nextId := cfg.nextId + 1 }
  let ltSpec ← sEvalLtSigned cfg' md senv s2 s1 outFFVarLt
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
def sEvalGtSigned {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  sEvalLtSigned cfg md senv s2 s1 outFFVar

/- Greater than equal simply uses the encoding of less than equal
   after swapping the operands -/
def sEvalGeSigned {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  sEvalLeSigned cfg md senv s2 s1 outFFVar

end Llzk.SymExec.SymInstr
