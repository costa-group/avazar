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


/- Symbolic expression of .neg expression -/
def sEvalExprId {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (s : SimpleExpr c) (_id : VarID)
  : Except String (ExprSpec c) := do
  let v ← simpleExprToSymFFVar senv s
  return {
          inSymEnv := senv,
          outSymEnv := senv,
          f := FFFormula.true, -- outVar = -v
          resTerm := default, -- will not be used
          res := v,
          newFFVars := {},
          nextId := cfg.nextId+1
  }


/- Symbolic expression of .neg expression -/
def sEvalExprNeg {c : ZKConfig}
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
          f := FFFormula.eq (FFTerm.var outFFVar) (FFTerm.neg v), -- outVar = -v
          resTerm := (FFTerm.var outFFVar),
          res := SymFFVar.var ⟨outFFVar, none⟩,
          newFFVars := { outFFVar },
          nextId := cfg.nextId+1
  }

/- Symbolic expression of .add expression -/
def sEvalExprAdd {c : ZKConfig}
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
          f := FFFormula.eq (FFTerm.var outFFVar) (FFTerm.add v1 v2), -- outVar = v1 + v2
          resTerm := (FFTerm.var outFFVar),
          res := SymFFVar.var ⟨outFFVar, none⟩,
          newFFVars := { outFFVar },
          nextId := cfg.nextId+1
  }

/- Symbolic expression of .sub expression -/
def sEvalExprSub {c : ZKConfig}
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
          f := FFFormula.eq (FFTerm.var outFFVar) (FFTerm.sub v1 v2), -- outVar = v1 - v2
          resTerm := (FFTerm.var outFFVar),
          res := SymFFVar.var ⟨outFFVar, none⟩,
          newFFVars := { outFFVar },
          nextId := cfg.nextId+1
  }

/- Symbolic expression of .mul expression -/
def sEvalExprMul {c : ZKConfig}
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
          f := FFFormula.eq (FFTerm.var outFFVar) (FFTerm.mul v1 v2), -- outVar = v1 * v2
          resTerm := (FFTerm.var outFFVar),
          res := SymFFVar.var ⟨outFFVar, none⟩,
          newFFVars := { outFFVar },
          nextId := cfg.nextId+1
  }

/- Symbolic expression of .div expression -/
def sEvalExprDiv {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  let outFFVar : FFVar := { id := cfg.nextId,
                            meta_data := { src_info := md.src_info, orig_name := id}
                          }
  let f := FFFormula.ite
                      (FFFormula.eq v2 (FFTerm.val 0))
                      FFFormula.false
                      (FFFormula.eq (FFTerm.mul (FFTerm.var outFFVar) v2) v1)
  return {
          inSymEnv := senv,
          outSymEnv := senv,
          -- outVar*v2 = v1
          f := f
          resTerm := (FFTerm.var outFFVar),
          res := SymFFVar.var ⟨outFFVar, none⟩,
          newFFVars := { outFFVar },
          nextId := cfg.nextId+1
  }

/- Symbolic expression of .pow expression -/
def sEvalExprPow {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  let base ← simpleExprToTerm senv s1
  let power ← simpleExprToFF senv s2 -- power must be a constant
  let outFFVar : FFVar := { id := cfg.nextId,
                            meta_data := { src_info := md.src_info, orig_name := id}
                          }
  let rec loop (n : Nat ) : FFTerm c :=
    match n with
    | 0 => FFTerm.val 1
    | 1 => base
    | n'+1 => FFTerm.mul base (loop n')
  let f := .eq (FFTerm.var outFFVar) (loop power.val)
  return {
          inSymEnv := senv,
          outSymEnv := senv,
          f := f,
          resTerm := (FFTerm.var outFFVar),
          res := SymFFVar.var ⟨outFFVar, none⟩,
          newFFVars := { outFFVar },
          nextId := cfg.nextId+1
  }


/-
For the encodings of Q = A / B and R = A mod B, should I generate the
finite field constraints

  A = Q * B + R

should I something else to avoid non-determinism? like R<B?

-/

def uiDivModGadget {c : ZKConfig}
   (md : CmdMD)
   (sconf : SymExecConfig c)
   (A : SymFFVar c)
   (B : FF c)
   : FFFormula c × FFVar × FFVar :=
    let Q : FFVar := { id := sconf.nextId,
                       meta_data := { src_info := md.src_info, orig_name := default } }
    let R : FFVar := { id := sconf.nextId + 1,
                       meta_data := { src_info := md.src_info, orig_name := default } }
  let uLo : Nat := (c.midpoint - 1) / B.val
  let lo : Nat := c.midpoint / B.val
  let hi : Nat := (c.p - 1) / B.val
  let Aterm := symVarToTerm A
  let eqn := FFFormula.eq Aterm (FFTerm.add (FFTerm.mul (FFTerm.var Q) (FFTerm.val B)) (FFTerm.var R))
  let rRange := FFFormula.range (FFTerm.var R) 0 (B.val - 1 : FF c)
  let lowBranch := FFFormula.and eqn (FFFormula.and rRange (FFFormula.range (FFTerm.var Q) 0 (uLo : FF c)))
  let highBranch :=
    FFFormula.and eqn (FFFormula.and rRange (FFFormula.range (FFTerm.var Q) (lo : FF c) (hi : FF c)))
  let isLow := FFFormula.range Aterm 0 (c.midpoint - 1 : FF c)
  (FFFormula.ite isLow lowBranch highBranch, Q, R)

def uiDivModGadgetLargeDivisor {c : ZKConfig}
  (md : CmdMD)
  (sconf : SymExecConfig c)
  (A : SymFFVar c)
  (B : FF c)
  : FFFormula c × FFVar × FFVar :=
    let Q : FFVar := { id := sconf.nextId,
                       meta_data := { src_info := md.src_info, orig_name := default } }
    let R : FFVar := { id := sconf.nextId + 1,
                       meta_data := { src_info := md.src_info, orig_name := default } }
  let Aterm := symVarToTerm A
  let isHighA := FFFormula.range Aterm B (-1 : FF c)
  let lowBranch := FFFormula.and (FFFormula.eq (FFTerm.var Q) (FFTerm.val 0))
    (FFFormula.eq (FFTerm.var R) Aterm)
  let highBranch := FFFormula.and (FFFormula.eq (FFTerm.var Q) (FFTerm.val 1))
    (FFFormula.eq (FFTerm.var R) (FFTerm.sub Aterm (FFTerm.val B)))
  (FFFormula.ite isHighA highBranch lowBranch, Q, R)


/- Symbolic expression of .uidiv expression -/
def sEvalExprUidiv {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  let B ← simpleExprToFF senv s2
  if B.val = 1 then
    let v ← simpleExprToSymFFVar senv s1
    return {
          inSymEnv := senv,
          outSymEnv := senv,
          f := .true,
          resTerm := default,
          res := v,
          newFFVars := {},
          nextId := cfg.nextId
    }
  else if B.val > 1 && B.val < c.midpoint then
    let A ← simpleExprToSymFFVar senv s1
    let (f, Q, R) := uiDivModGadget md cfg A B
    return {
            inSymEnv := senv,
            outSymEnv := senv,
            f := f,
            resTerm := (FFTerm.var Q),
            res := SymFFVar.var ⟨Q, none⟩,
            newFFVars := { Q, R },
            nextId := cfg.nextId+2
    }
    else if B.val ≥ c.midpoint then
    let A ← simpleExprToSymFFVar senv s1
    let (f, Q, R) := uiDivModGadgetLargeDivisor md cfg A B
    return {
            inSymEnv := senv,
            outSymEnv := senv,
            f := f,
            resTerm := (FFTerm.var Q),
            res := SymFFVar.var ⟨Q, none⟩,
            newFFVars := { Q, R },
            nextId := cfg.nextId+2
    }
  else
    Except.error s!"Error: division by zero for .uidiv expression."

/- Symbolic expression of .uimod expression -/
def sEvalExprUimod {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  let B ← simpleExprToFF senv s2
  if B.val = 1 then
    let v ← simpleExprToSymFFVar senv s1
    return {
          inSymEnv := senv,
          outSymEnv := senv,
          f := .true,
          resTerm := default,
          res := v,
          newFFVars := {},
          nextId := cfg.nextId
    }
  else if B.val > 1 && B.val < c.midpoint then
    let A ← simpleExprToSymFFVar senv s1
    let (f, Q, R) := uiDivModGadget md cfg A B
    return {
            inSymEnv := senv,
            outSymEnv := senv,
            f := f,
            resTerm := (FFTerm.var R),
            res := SymFFVar.var ⟨R, none⟩,
            newFFVars := { Q, R },
            nextId := cfg.nextId+2
    }
    else if B.val ≥ c.midpoint then
    let A ← simpleExprToSymFFVar senv s1
    let (f, Q, R) := uiDivModGadgetLargeDivisor md cfg A B
    return {
            inSymEnv := senv,
            outSymEnv := senv,
            f := f,
            resTerm := (FFTerm.var R),
            res := SymFFVar.var ⟨R, none⟩,
            newFFVars := { Q, R },
            nextId := cfg.nextId+2
    }
  else
    Except.error s!"Error: division by zero for .uimod expression."
end Llzk.SymExec.SymInstr
