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


def sEvalBitWiseAND {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  let bits1Spec := bitify cfg md v1 -- bitify v1
  let cfg' := { cfg with nextId := bits1Spec.nextId }
  let bits2Spec := bitify cfg' md v2 -- bitify v2
  let cfg'' := { cfg' with nextId := bits2Spec.nextId }
  let bits3Spec := bitify cfg'' md (FFTerm.var outFFVar) -- bitify outVar
  -- generate $r_i = a_i * b_i$ for each bit
  let f : FFFormula c :=
    List.foldl
      (fun acc (b1, b2, out) =>
        (.and acc
              (FFFormula.eq
                  out
                  (FFTerm.mul b1 b2))))
    (.and bits1Spec.f (.and bits2Spec.f bits3Spec.f))
    (List.zipWith3 (fun b1 b2 out => (b1, b2, out)) bits1Spec.bits bits2Spec.bits bits3Spec.bits)
  let newFFVars := bits1Spec.newFFVars ∪ bits2Spec.newFFVars ∪ bits3Spec.newFFVars
  return {
    inSymEnv := senv,
    f := f,
    resVar := outFFVar,
    nextId := bits3Spec.nextId,
    newFFVars := newFFVars
  }

def sEvalBitWiseOR {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  let bits1Spec := bitify cfg md v1 -- bitify v1
  let cfg' := { cfg with nextId := bits1Spec.nextId }
  let bits2Spec := bitify cfg' md v2 -- bitify v2
  let cfg'' := { cfg' with nextId := bits2Spec.nextId }
  let bits3Spec := bitify cfg'' md (FFTerm.var outFFVar) -- bitify outVar
  -- generate $r_i = a_i + b_i - a_i * b_i$ for each bit
  let f : FFFormula c :=
    List.foldl
      (fun acc (b1, b2, out) =>
        (.and acc
              (FFFormula.eq
                  out
                  (FFTerm.sub (FFTerm.add b1 b2) (FFTerm.mul b1 b2)))))
    (.and bits1Spec.f (.and bits2Spec.f bits3Spec.f))
    (List.zipWith3 (fun b1 b2 out => (b1, b2, out)) bits1Spec.bits bits2Spec.bits bits3Spec.bits)
  let newFFVars := bits1Spec.newFFVars ∪ bits2Spec.newFFVars ∪ bits3Spec.newFFVars
  return {
    inSymEnv := senv,
    f := f,
    resVar := outFFVar,
    nextId := bits3Spec.nextId,
    newFFVars := newFFVars
  }

def sEvalBitWiseXOR {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  let bits1Spec := bitify cfg md v1 -- bitify v1
  let cfg' := { cfg with nextId := bits1Spec.nextId }
  let bits2Spec := bitify cfg' md v2 -- bitify v2
  let cfg'' := { cfg' with nextId := bits2Spec.nextId }
  let bits3Spec := bitify cfg'' md (FFTerm.var outFFVar) -- bitify outVar
  -- generate $r_i = a_i + b_i - 2 * a_i * b_i$ for each bit
  let f : FFFormula c :=
    List.foldl
      (fun acc (b1, b2, out) =>
        (.and acc
              (FFFormula.eq
                out
                (FFTerm.sub (FFTerm.add b1 b2) (FFTerm.mul (FFTerm.mul (FFTerm.val 2) b1) b2)))))
    (.and bits1Spec.f (.and bits2Spec.f bits3Spec.f))
    (List.zipWith3 (fun b1 b2 out => (b1, b2, out)) bits1Spec.bits bits2Spec.bits bits3Spec.bits)
  let newFFVars := bits1Spec.newFFVars ∪ bits2Spec.newFFVars ∪ bits3Spec.newFFVars
  return {
    inSymEnv := senv,
    f := f,
    resVar := outFFVar,
    nextId := bits3Spec.nextId,
    newFFVars := newFFVars
  }

def sEvalBitWiseNOT {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v ← simpleExprToTerm senv s
  let bits1Spec := bitify cfg md v -- bitify v1
  let cfg' := { cfg with nextId := bits1Spec.nextId }
  let bits2Spec := bitify cfg' md (FFTerm.var outFFVar) -- bitify outVar
  -- generate $r_i = 1 - a_i$ for each bit
  let f : FFFormula c :=
    List.foldl
      (fun acc (b, out) =>
        (.and acc
              (FFFormula.eq
                out
                (FFTerm.sub (FFTerm.val 1) b))))
    (.and bits1Spec.f bits2Spec.f)
    (List.zip bits1Spec.bits bits2Spec.bits)
  let newFFVars := bits1Spec.newFFVars ∪ bits2Spec.newFFVars
  return {
    inSymEnv := senv,
    f := f,
    resVar := outFFVar,
    nextId := bits2Spec.nextId,
    newFFVars := newFFVars
  }

def sEvalBitWiseSHLAux {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (v1 : FFTerm c) (v2 : Nat) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  if v2 >= c.k then
    -- if shift amount is greater than or equal to bit width, the result is always 0
    return {
      inSymEnv := senv,
      f := FFFormula.eq (FFTerm.var outFFVar) (FFTerm.val 0),
      resVar := outFFVar,
      nextId := cfg.nextId
    }
  else
    let bits1Spec := bitify cfg md v1 -- bitify v1
    let newBits := (bits1Spec.bits.reverse.drop v2).reverse
    let idxs := List.range c.k
    let pows := idxs.map (fun i => FFTerm.val (2 ^ (i+v2)))
    let shiftedBits := List.zipWith (fun bit pow => FFTerm.mul bit pow) newBits pows
    let sum := match shiftedBits, pows with
               | b::bs, p::ps => List.foldl (fun acc (bit, pow) => FFTerm.add acc (FFTerm.mul bit pow))
                        (FFTerm.mul b p)
                        (List.zip bs ps)
               | _, _ => FFTerm.val 0 -- they are the same length, we reach this with empty lists
    let f : FFFormula c := (.and bits1Spec.f (FFFormula.eq (FFTerm.var outFFVar) sum))
    let newFFVars := bits1Spec.newFFVars
    return {
      inSymEnv := senv,
      f := f,
      resVar := outFFVar,
      nextId := bits1Spec.nextId,
      newFFVars := newFFVars
    }

def sEvalBitWiseSHLConstShift {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToFF senv s2 -- the number of bits
  sEvalBitWiseSHLAux cfg md senv v1 v2.val outFFVar

/-
   outVars1 = shl outVar0 1
   outVars2 = shl outVar1 2
   outVars3 = shl outVar2 4
   outVars4 = shl outVar2 4



-/


def sEvalBitWiseSHL {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  match sEvalBitWiseSHLConstShift cfg md senv s1 s2 outFFVar with
  | Except.ok spec => return spec
  | Except.error _ =>
      Except.error "Bitwise shift left with non-constant not implemented yet"



def sEvalBitWiseSHRAux {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (v1 : FFTerm c) (v2 : Nat) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  if v2 >= c.k then
    -- if shift amount is greater than or equal to bit width, the result is always 0
    return {
      inSymEnv := senv,
      f := FFFormula.eq (FFTerm.var outFFVar) (FFTerm.val 0),
      resVar := outFFVar,
      nextId := cfg.nextId
    }
  else
    let bits1Spec := bitify cfg md v1 -- bitify v1
    let newBits := bits1Spec.bits.drop v2
    let idxs := List.range c.k
    let pows := idxs.map (fun i => FFTerm.val (2 ^ i))
    let shiftedBits := List.zipWith (fun bit pow => FFTerm.mul bit pow) newBits pows
    let sum := match shiftedBits, pows with
               | b::bs, p::ps => List.foldl (fun acc (bit, pow) => FFTerm.add acc (FFTerm.mul bit pow))
                        (FFTerm.mul b p)
                        (List.zip bs ps)
               | _, _ => FFTerm.val 0 -- they are the same length, we reach this with empty lists
    let f : FFFormula c := (.and bits1Spec.f (FFFormula.eq (FFTerm.var outFFVar) sum))
    let newFFVars := bits1Spec.newFFVars
    return {
       inSymEnv := senv,
       f := f,
       resVar := outFFVar,
       nextId := bits1Spec.nextId,
       newFFVars := newFFVars
    }


def sEvalBitWiseSHRConstShift {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToFF senv s2 -- the number of bits
  sEvalBitWiseSHRAux cfg md senv v1 v2.val outFFVar

def sEvalBitWiseSHR {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  match sEvalBitWiseSHRConstShift cfg md senv s1 s2 outFFVar with
  | Except.ok spec => return spec
  | Except.error _ =>
      Except.error "Bitwise shift right with non-constant not implemented yet"

end Llzk.SymExec.SymInstr
