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
  return {
          inSymEnv := senv,
          outSymEnv := senv,
          -- outVar*v2 = v1
          f := FFFormula.eq (FFTerm.mul (FFTerm.var outFFVar) v2) v1,  -- (outVar = v1 / v2)
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

should I something else to aovid non-determinsim? like R<B?

-/

/- Symbolic expression of .uidiv expression -/
def sEvalExprUidiv {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  let A ← simpleExprToTerm senv s1
  let B ← simpleExprToTerm senv s2
  let Q : FFVar := { id := cfg.nextId,
                            meta_data := { src_info := md.src_info, orig_name := id}
                          }
  let R : FFVar := { id := cfg.nextId+1,
                            meta_data := { src_info := md.src_info, orig_name := id}
                          }
  let f := FFFormula.and (FFFormula.eq A (FFTerm.add (FFTerm.mul (FFTerm.var Q) B) (FFTerm.var R)))
                      (FFFormula.lt (FFTerm.var R) B)
  return {
          inSymEnv := senv,
          outSymEnv := senv,
          f := f,
          resTerm := (FFTerm.var Q),
          res := SymFFVar.var ⟨Q, none⟩,
          newFFVars := { Q, R },
          nextId := cfg.nextId+2
  }

/- Symbolic expression of .uimod expression -/
def sEvalExprUimod {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  let A ← simpleExprToTerm senv s1
  let B ← simpleExprToTerm senv s2
  let Q : FFVar := { id := cfg.nextId,
                            meta_data := { src_info := md.src_info, orig_name := id}
                          }
  let R : FFVar := { id := cfg.nextId+1,
                            meta_data := { src_info := md.src_info, orig_name := id}
                          }
  let f := FFFormula.and (FFFormula.eq A (FFTerm.add (FFTerm.mul (FFTerm.var Q) B) (FFTerm.var R)))
                      (FFFormula.lt (FFTerm.var R) B)
  return {
          inSymEnv := senv,
          outSymEnv := senv,
          f := f,
          resTerm := (FFTerm.var R),
          res := SymFFVar.var ⟨R, none⟩,
          newFFVars := { Q, R },
          nextId := cfg.nextId+2
  }

end Llzk.SymExec.SymInstr
