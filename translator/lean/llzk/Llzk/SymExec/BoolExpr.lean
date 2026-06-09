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
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  let outFFVar : FFVar := { id := cfg.nextId,
                            meta_data := { src_info := md.src_info, orig_name := id}
                          }
  return {
          inSymEnv := senv,
          outSymEnv := senv,
          f := (.and (FFFormula.eq
                        (FFTerm.var outFFVar)
                        (FFTerm.ite (FFFormula.eq v1 v2) (.val 1) (.val 0)))
                      (FFFormula.range (FFTerm.var outFFVar) 0 1)), -- force bool
          resTerm := (FFTerm.var outFFVar),
          res := ⟨outFFVar, none⟩,
          newFFVars := { outFFVar },
          nextId := cfg.nextId+1
  }

/- Non-equality of boolean expressions.

   0 if they are equal, 1 otherwise.
-/

def sEvalNeq {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  let outFFVar : FFVar := { id := cfg.nextId,
                            meta_data := { src_info := md.src_info, orig_name := id}
                          }
  return {
          inSymEnv := senv,
          outSymEnv := senv,
          f := (.and (FFFormula.eq
                        (FFTerm.var outFFVar)
                        (FFTerm.ite (FFFormula.eq v1 v2) (.val 0) (.val 1)))
                     (FFFormula.range (FFTerm.var outFFVar) 0 1)), -- force bool
          resTerm := (FFTerm.var outFFVar),
          res := ⟨outFFVar, none⟩,
          newFFVars := { outFFVar },
          nextId := cfg.nextId+1
  }


/- Boolean OR operation.

   0 if both are 0, 1 otherwise.
-/
def sEvalBor {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  let outFFVar : FFVar := { id := cfg.nextId,
                            meta_data := { src_info := md.src_info, orig_name := id}
                          }
  return {
          inSymEnv := senv,
          outSymEnv := senv,
          f := .and
                (FFFormula.eq
                  (FFTerm.var outFFVar)
                  (FFTerm.ite
                    (.and (.eq v1 (.val 0)) (.eq v2 (.val 0)))
                    (.val 0)
                    (.val 1)))
                (FFFormula.range (FFTerm.var outFFVar) 0 1), -- force bool
          resTerm := (FFTerm.var outFFVar),
          res := ⟨outFFVar, none⟩,
          newFFVars := { outFFVar },
          nextId := cfg.nextId+1
  }

/- Boolean AND operation.

   0 if either is 0, 1 otherwise.
-/
def sEvalBAnd {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  let outFFVar : FFVar := { id := cfg.nextId,
                            meta_data := { src_info := md.src_info, orig_name := id}
                          }
  return {
          inSymEnv := senv,
          outSymEnv := senv,
          f := .and
                (FFFormula.eq
                  (FFTerm.var outFFVar)
                  (FFTerm.ite
                    (.or (.eq v1 (.val 0)) (.eq v2 (.val 0)))
                    (.val 0)
                    (.val 1)))
                (FFFormula.range (FFTerm.var outFFVar) 0 1), -- force bool
          resTerm := (FFTerm.var outFFVar),
          res := ⟨outFFVar, none⟩,
          newFFVars := { outFFVar },
          nextId := cfg.nextId+1
  }

/- Boolean negation operation.

   1 if the input is 0, and 0 otherwise.
-/
def sEvalBNeg {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  let v ← simpleExprToTerm senv s
  let outFFVar : FFVar := { id := cfg.nextId,
                            meta_data := { src_info := md.src_info, orig_name := id}
                          }
  return {
          inSymEnv := senv,
          outSymEnv := senv,
          f := .and
                (FFFormula.eq (FFTerm.var outFFVar)
                 (FFTerm.ite
                    (.eq v (.val 0))
                    (.val 1)
                    (.val 0)))
                (FFFormula.range (FFTerm.var outFFVar) 0 1), -- force bool
          resTerm := (FFTerm.var outFFVar),
          res := ⟨outFFVar, none⟩,
          newFFVars := { outFFVar },
          nextId := cfg.nextId+1
  }



/- Unsigned comparison-/


/-
  Special case of unsigned x < y when the upper bound is a constant.

  x < v is encoded as:

  v = 0 -> false
  v > 0 -> range(x, 0, v-1)
-/
def sEvalLtUnSignedConstLeft {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToFF senv s2
  let outFFVar : FFVar := { id := cfg.nextId,
                            meta_data := { src_info := md.src_info, orig_name := id}
                          }
  let f := if v2.val == 0 then
             FFFormula.false -- x<0 is always false when we are working with unsigned integers
           else
             FFFormula.eq (FFTerm.var outFFVar) (.ite (.range v1 0 (v2-1)) (.val 1) (.val 0))
  return {
          inSymEnv := senv,
          outSymEnv := senv,
          f := (.and f (FFFormula.range (FFTerm.var outFFVar) 0 1)), -- force bool
          resTerm := (FFTerm.var outFFVar),
          res := ⟨outFFVar, none⟩,
          newFFVars := { outFFVar },
          nextId := cfg.nextId+1
        }

/-
  Special case of unsigned x < y when the lower bound is a constant.

  v < x is encoded as:

  v = c.p-1 -> false
  v < c.p-1 -> range(x, v+1, c.p-1)
-/
def sEvalLtUnSignedConstRight {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToFF senv s1
  let v2 ← simpleExprToTerm senv s2
  let outFFVar : FFVar := { id := cfg.nextId,
                            meta_data := { src_info := md.src_info, orig_name := id}
                          }
  let f := if (v1.val == (c.p-1)) then
             FFFormula.false -- p-1 < x is always false when we are working with unsigned integers
           else
             FFFormula.eq (FFTerm.var outFFVar) (.ite (.range v2 (v1+1) (c.p-1)) (.val 1) (.val 0))
  return {
          inSymEnv := senv,
          outSymEnv := senv,
          f := (.and f (FFFormula.range (FFTerm.var outFFVar) 0 1)), -- force bool
          resTerm := (FFTerm.var outFFVar),
          res := ⟨outFFVar, none⟩,
          newFFVars := { outFFVar },
          nextId := cfg.nextId+1
        }

/- Compare x < y bitwise. We compare the bits of x and y from the
   most significant bit to the least significant bit.
-/
def sEvalLtUnSignedBitCmp {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  let outFFVar : FFVar := { id := cfg.nextId,
                            meta_data := { src_info := md.src_info, orig_name := id}
                          }
  let cfg' := { cfg with nextId := cfg.nextId+1 }
  let bits1Spec := bitify cfg' md v1 -- bitify v1
  let cfg'' := { cfg with nextId := bits1Spec.nextId }
  let bits2Spec := bitify cfg'' md v2 -- bitify v2
  let ite := List.foldl -- construct the ite expression for bitwise comparison
              (fun acc (b1, b2) =>
                  FFTerm.ite
                    (.and (.eq b1 (.val 0)) (.eq b2 (.val 1)))
                    (.val 1)
                    (.ite (.and (.eq b1 (.val 1)) (.eq b2 (.val 0))) (.val 0) acc))
              (.val 0)
              (List.zip bits1Spec.bits bits2Spec.bits)
  let newFFVars := bits1Spec.newFFVars ∪ bits2Spec.newFFVars ∪ { outFFVar }
  let f := .and bits1Spec.f (.and bits2Spec.f (.eq (FFTerm.var outFFVar) ite))
  return {
          inSymEnv := senv,
          outSymEnv := senv,
          f := (.and f (FFFormula.range (FFTerm.var outFFVar) 0 1)), -- force bool
          resTerm := (FFTerm.var outFFVar),
          res := ⟨outFFVar, none⟩,
          nextId := bits2Spec.nextId,
          newFFVars := newFFVars,
          newBoolVars := ∅
  }

/- General case of unsigned x < y. We first check if we can apply the special cases
   for constants, and if not, we fall back to bitwise comparison.
-/
def sEvalLtUnSigned {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  match sEvalLtUnSignedConstLeft cfg md senv s1 s2 id with
  | Except.ok spec => return spec
  | Except.error _ =>
    match sEvalLtUnSignedConstRight cfg md senv s1 s2 id with
    | Except.ok spec => return spec
    | Except.error _ =>
      match sEvalLtUnSignedBitCmp cfg md senv s1 s2 id with
      | Except.ok spec => return spec
      | Except.error err => throw err

/- x <= y is be encoded as ~(y < x), which is 1 minus the result
   variable of (y < x).
-/
def sEvalLeUnSigned {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  let outFFVar : FFVar := { id := cfg.nextId,
                            meta_data := { src_info := md.src_info, orig_name := id}
                          }
  -- increment the nextId in the config for the next variable
  let cfg' : SymExecConfig c := { cfg with nextId := cfg.nextId + 1 }
  let ltSpec ← sEvalLtUnSigned cfg' md senv s2 s1 s!"{id}_le_aux"
  return {
          inSymEnv := senv,
          outSymEnv := ltSpec.outSymEnv,
          -- ltSpec.f /\ outFFVar = 1-outFFVarLt
          f := (.and (.and ltSpec.f (.eq (FFTerm.var outFFVar)
                                   (FFTerm.sub (.val 1) (FFTerm.var ltSpec.res.var))))
                    (FFFormula.range (FFTerm.var outFFVar) 0 1)), -- force bool
          nextId := ltSpec.nextId,
          resTerm := (FFTerm.var outFFVar),
          res := ⟨outFFVar, none⟩,
          newFFVars := ltSpec.newFFVars.insert outFFVar,
          newBoolVars := ltSpec.newBoolVars
  }

/- Greater than simply uses the encoding of less than after swapping
   the operands -/
def sEvalGtUnSigned {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  sEvalLtUnSigned cfg md senv s2 s1 id

/- Greater than equal simply uses the encoding of less than equal
   after swapping the operands -/
def sEvalGeUnSigned {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  sEvalLeUnSigned cfg md senv s2 s1 id

/- Signed comparison-/

/- Special case of signed x < y when the upper bound is a constant.

   x < v is encoded as:

     v = c.midpoint -> false
     v > c.midpoint -> range(x, midpoint, v-1)
     v = 0 -> range(x, midpoint, p-1)
     0 < v < c.midpoint -> range(x, 0, v-1) or range(x, c.midpoint, p-1)
-/
def sEvalLtSignedConstLeft {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToFF senv s2
  let outFFVar : FFVar := { id := cfg.nextId,
                            meta_data := { src_info := md.src_info, orig_name := id}
                          }
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
                          (.ite (.or (.range v1 0 (v2-1)) (.range v1 c.midpoint (c.p-1)))
                                (.val 1)
                                (.val 0))
  return {
          inSymEnv := senv,
          outSymEnv := senv,
          f := (.and f (FFFormula.range (FFTerm.var outFFVar) 0 1)), -- force boolean
          resTerm := (FFTerm.var outFFVar),
          res := ⟨outFFVar, none⟩,
          nextId := cfg.nextId+1,
          newFFVars := { outFFVar }
        }

/- Special case of signed x < y when the lower bound is a constant.

   v < x is encoded as:

     v = midpoint-1 -> false
     v < c.midpoint-1 -> range(x, v+1,midpoint-1)
     v = c.p-1 -> range(x, 0, midpoint-1)
     v >= c.midpoint -> range(x, v+1, p-1) or range(x, 0, midpoint-1)
-/
def sEvalLtSignedConstRight {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToFF senv s1
  let v2 ← simpleExprToTerm senv s2
  let outFFVar : FFVar := { id := cfg.nextId,
                            meta_data := { src_info := md.src_info, orig_name := id}
                          }
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
          outSymEnv := senv,
          f := (.and f (FFFormula.range (FFTerm.var outFFVar) 0 1)), -- force boolean
          resTerm := (FFTerm.var outFFVar),
          res := ⟨outFFVar, none⟩,
          nextId := cfg.nextId+1,
          newFFVars := { outFFVar }
        }

/- Encoding signed x < y using the unsigned version.

   A=1 if x is non-negative, 0 otherwise
   B=1 if y is non-negative, 0 otherwise
   C is the result of unsigned x < y

   the final result is encoded as:

    if A=B then C else 1-A
-/
def sEvalLtSignedBitCmp {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  let outFFVar : FFVar := { id := cfg.nextId,
                            meta_data := { src_info := md.src_info, orig_name := id}
                          }
  let cfg' := { cfg with nextId := cfg.nextId + 4 }
  let isS1Pos ← sEvalLtUnSigned cfg' md senv s1 (SimpleExpr.val c.midpoint) s!"{id}isS1Pos"
  let cfg'' := { cfg' with nextId := isS1Pos.nextId }
  let isS2Pos ← sEvalLtUnSigned cfg'' md
                     isS1Pos.outSymEnv s2 (SimpleExpr.val c.midpoint) s!"{id}_isS2Pos"
  let cfg''' := { cfg'' with nextId := isS2Pos.nextId }
  let ltSpec ← sEvalLtUnSignedBitCmp cfg''' md isS1Pos.outSymEnv s1 s2 s!"{id}ltAux"
  -- if A=B then C else 1-A
  let f := (.and
              (FFFormula.eq
                (FFTerm.var outFFVar)
                (FFTerm.ite
                  (.eq (FFTerm.var isS1Pos.res.var) (FFTerm.var isS2Pos.res.var))
                  (FFTerm.var ltSpec.res.var)
                  (FFTerm.sub (.val 1) (FFTerm.var isS1Pos.res.var))))
              (FFFormula.range (FFTerm.var outFFVar) 0 1)) -- force boolean
  return {
          inSymEnv := senv,
          outSymEnv := ltSpec.outSymEnv,
          f := .and isS1Pos.f (.and isS2Pos.f (.and ltSpec.f f)),
          resTerm := (FFTerm.var outFFVar),
          res := ⟨outFFVar, none⟩,
          nextId := ltSpec.nextId+1,
          newFFVars := isS1Pos.newFFVars ∪ isS2Pos.newFFVars ∪ ltSpec.newFFVars ∪
                       {outFFVar},
          newBoolVars := isS1Pos.newBoolVars ∪ isS2Pos.newBoolVars ∪ ltSpec.newBoolVars
        }



/-
s1 < s2, where s1 is a constant value v1

if v1 is positive (v1.val < c.midpoint)

  x' = v1-s2
  out = ite (s2 in [midpoint, p-1]), -- s2 is negative
            0, -- s2 is negative, so v1 cannot be less than s2
            ite (x' in [midpoint, p-1]), -- x' is negative, so s1 is less than s2
                1,
                0)

if v1 is negative (v1.val >= c.midpoint)

  x' = v1-s2
  out = ite (s2 in [0, c.midpoint-1]), -- s2 is positive
            1, -- s2 is positive, so v1 is less than s2
            ite (x' in [midpoint, p-1]), -- x' is negative, so s1 is less than s2
                1,
                0)

-/
def sEvalLtSigned_range_sub_left_const {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToFF senv s1
  let v2 ← simpleExprToTerm senv s2
  let outFFVar : FFVar := { id := cfg.nextId,
                              meta_data := { src_info := md.src_info, orig_name := id}
                          }
  let diffFFVar : FFVar := { id := cfg.nextId+1,
                               meta_data := { src_info := md.src_info, orig_name := id}
                         }
  let diffFormula := FFFormula.eq (FFTerm.var diffFFVar) (FFTerm.sub (FFTerm.val v1) v2)
  let diffVarIsNeg := (FFFormula.range (FFTerm.var diffFFVar) (c.midpoint : FF c) ((c.p-1) : FF c))
  let fDiff := (FFTerm.ite diffVarIsNeg (FFTerm.val 1) (FFTerm.val 0))
  let f :=
    if ( v1.val < c.midpoint) then -- is positive
      .and diffFormula
        (.eq (FFTerm.var outFFVar)
             (FFTerm.ite
               (FFFormula.range v2 (c.midpoint : FF c) ((c.p-1) : FF c)) -- v2 is negative
               (FFTerm.val 0)
               fDiff))
        else -- v1 is negative
      .and diffFormula
        (.eq (FFTerm.var outFFVar)
             (FFTerm.ite
               (FFFormula.range v2 (0 : FF c) ( c.midpoint-1 : FF c)) -- v2 is positive
               (FFTerm.val 1)
               fDiff))
    return {
            inSymEnv := senv,
            outSymEnv := senv,
            f := (.and f (FFFormula.range (FFTerm.var outFFVar) 0 1)), -- force boolean
            resTerm := (FFTerm.var outFFVar),
            res := ⟨outFFVar, none⟩,
            nextId := cfg.nextId+2,
            newFFVars := { outFFVar }
          }

/-
-/
def sEvalLtSigned_range_sub_right_const {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToFF senv s2
  let outFFVar : FFVar := { id := cfg.nextId,
                              meta_data := { src_info := md.src_info, orig_name := id}
                          }
  let diffFFVar : FFVar := { id := cfg.nextId+1,
                               meta_data := { src_info := md.src_info, orig_name := id}
                         }
  let diffFormula := FFFormula.eq (FFTerm.var diffFFVar) (FFTerm.sub v1 (FFTerm.val v2))
  let diffVarIsNeg := (FFFormula.range (FFTerm.var diffFFVar) (c.midpoint : FF c) ((c.p-1) : FF c))
  let fDiff := (FFTerm.ite diffVarIsNeg (FFTerm.val 1) (FFTerm.val 0))
  let f :=
    if ( v2.val < c.midpoint) then -- v2 is positive
      .and diffFormula
        (.eq (FFTerm.var outFFVar)
             (FFTerm.ite
               (FFFormula.range v1 (c.midpoint : FF c) ((c.p-1) : FF c)) -- v1 is negative
               (FFTerm.val 1)
               fDiff))
        else -- v2 is negative
      .and diffFormula
        (.eq (FFTerm.var outFFVar)
             (FFTerm.ite
               (FFFormula.range v1 (0 : FF c) ( c.midpoint-1 : FF c)) -- v1 is positive
               (FFTerm.val 0)
               fDiff))
    return {
            inSymEnv := senv,
            outSymEnv := senv,
            f := (.and f (FFFormula.range (FFTerm.var outFFVar) 0 1)), -- force boolean
            resTerm := (FFTerm.var outFFVar),
            res := ⟨outFFVar, none⟩,
            nextId := cfg.nextId+2,
            newFFVars := { outFFVar }
          }


/-
-/
def sEvalLtSigned_range_sub_gen {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  let outFFVar : FFVar := { id := cfg.nextId,
                              meta_data := { src_info := md.src_info, orig_name := id}
                          }
  let diffFFVar : FFVar := { id := cfg.nextId+1,
                               meta_data := { src_info := md.src_info, orig_name := id}
                         }
  let diffFormula := FFFormula.eq (FFTerm.var diffFFVar) (FFTerm.sub v1 v2)
  let s1IsPos := FFFormula.range v1 (0 : FF c) (c.midpoint-1 : FF c)
  let s1IsNeg := FFFormula.range v1 (c.midpoint : FF c) ((c.p-1) : FF c)
  let s2IsPos := FFFormula.range v2 (0 : FF c) (c.midpoint-1 : FF c)
  let s2IsNeg := FFFormula.range v2 (c.midpoint : FF c) ((c.p-1) : FF c)
  let diffVarIsNeg := (FFFormula.range (FFTerm.var diffFFVar) (c.midpoint : FF c) ((c.p-1) : FF c))
  let fDiff := (FFTerm.ite diffVarIsNeg (FFTerm.val 1) (FFTerm.val 0))
  let f :=
    .and diffFormula
        (.eq (FFTerm.var outFFVar)
             (FFTerm.ite
               (.and s1IsPos s2IsNeg) -- s1 is positive and s2 is negative
               (FFTerm.val 0)
               (FFTerm.ite
                 (.and s1IsNeg s2IsPos) -- s1 is negative and s2 is positive
                 (FFTerm.val 1)
                 fDiff)))
    return {
            inSymEnv := senv,
            outSymEnv := senv,
            f := (.and f (FFFormula.range (FFTerm.var outFFVar) 0 1)), -- force boolean
            resTerm := (FFTerm.var outFFVar),
            res := ⟨outFFVar, none⟩,
            nextId := cfg.nextId+2,
            newFFVars := { outFFVar }
          }

def sEvalLtSigned_range_sub {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
    match sEvalLtSigned_range_sub_left_const cfg md senv s1 s2 id with
    | Except.ok spec => return spec
    | Except.error _ =>
      match sEvalLtSigned_range_sub_right_const cfg md senv s1 s2 id with
      | Except.ok spec => return spec
      | Except.error _ => sEvalLtSigned_range_sub_gen cfg md senv s1 s2 id


/- General case of x < y. We first try the special cases with constants, and if
   those don't apply, we use the bitwise comparison. -/
def sEvalLtSigned_normal {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  match sEvalLtSignedConstLeft cfg md senv s1 s2 id with
  | Except.ok spec => return spec
  | Except.error _ =>
    match sEvalLtSignedConstRight cfg md senv s1 s2 id with
    | Except.ok spec => return spec
    | Except.error _ => sEvalLtSignedBitCmp cfg md senv s1 s2 id

/- General case of x < y. We first try the special cases with constants, and if
   those don't apply, we use the bitwise comparison. -/
def sEvalLtSigned {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  match cfg.cmpScm with
  | CmpScm.range_of_diff => sEvalLtSigned_range_sub cfg md senv s1 s2 id
  | CmpScm.normal => sEvalLtSigned_normal cfg md senv s1 s2 id



/- x<=y is be encoded as 1 minus the result variable of (y < x).
-/
def sEvalLeSigned {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  let outFFVar : FFVar := { id := cfg.nextId,
                              meta_data := { src_info := md.src_info, orig_name := "gt_aux" }
                            }
  -- increment the nextId in the config for the next variable
  let cfg' : SymExecConfig c := { cfg with nextId := cfg.nextId + 1 }
  let ltSpec ← sEvalLtSigned cfg' md senv s2 s1 s!"{id}_gt_aux"
  return {
          inSymEnv := senv,
          outSymEnv := ltSpec.outSymEnv,
          -- ltSpec.f /\ outFFVar = 1-outFFVarLt
          f := (.and ltSpec.f
                     (.and (.eq (FFTerm.var outFFVar)
                                   (FFTerm.sub (.val 1) (FFTerm.var ltSpec.res.var)))
                           (FFFormula.range (FFTerm.var outFFVar) 0 1))), -- force bool
          nextId := ltSpec.nextId,
          resTerm := (FFTerm.var outFFVar),
          res := ⟨outFFVar, none⟩,
          newFFVars := ltSpec.newFFVars.insert outFFVar,
          newBoolVars := ltSpec.newBoolVars
  }

/- Greater than simply uses the encoding of less than after swapping
   the operands -/
def sEvalGtSigned {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  sEvalLtSigned cfg md senv s2 s1 id

/- Greater than equal simply uses the encoding of less than equal
   after swapping the operands -/
def sEvalGeSigned {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  sEvalLeSigned cfg md senv s2 s1 id

end Llzk.SymExec.SymInstr
