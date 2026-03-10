import Llzk.Language.Core.Syntax.AST
import Llzk.Language.Core.Syntax.Printer
import Llzk.FFConstraints.Basic
import Llzk.SymExec.Basic
import Llzk.SymExec.Common
import Llzk.SymExec.Bitify
import Llzk.SymExec.BoolExpr



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
    resTerm := (FFTerm.var outFFVar),
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
    resTerm := (FFTerm.var outFFVar),
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
    resTerm := (FFTerm.var outFFVar),
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
    resTerm := (FFTerm.var outFFVar),
    nextId := bits2Spec.nextId,
    newFFVars := newFFVars
  }


/- SHIFT LEFT
-/

def sEvalBitWiseSHLAux {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (v1 : FFTerm c) (v2 : Nat) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  if v2 >= c.k then
    -- if shift amount is greater than or equal to bit width, the result is always 0
    return {
      inSymEnv := senv,
      f := FFFormula.eq (FFTerm.var outFFVar) (FFTerm.val 0),
      resTerm := (FFTerm.var outFFVar),
      nextId := cfg.nextId
    }
  else
    let bits1Spec := bitify cfg md v1 -- bitify v1
    let newBits := (bits1Spec.bits.reverse.drop v2).reverse
    let idxs := List.range c.k
    let pows := idxs.map (fun i => FFTerm.val (2 ^ (i+v2)))
    let shiftedBits := List.zipWith (fun bit pow => FFTerm.mul bit pow) newBits pows
    let sum := match shiftedBits, pows with
               | b::bs, p::ps => List.foldl
                                   (fun acc (bit, pow) => FFTerm.add acc (FFTerm.mul bit pow))
                                   (FFTerm.mul b p)
                                   (List.zip bs ps)
               | _, _ => FFTerm.val 0 -- they are the same length, we reach this with empty lists
    let f : FFFormula c := (.and bits1Spec.f (FFFormula.eq (FFTerm.var outFFVar) sum))
    let newFFVars := bits1Spec.newFFVars
    return {
      inSymEnv := senv,
      f := f,
      resTerm := (FFTerm.var outFFVar),
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

s2 must fit in floor(log2(k))+1 bits, otherwise the result is 0

   ite (< s2 k) (eq outVar 0) F

where F is as follows. Let b1,...,bi be the log2(k)+1 lsb bits of s2

   outVars0 = s1
   ite (eq b1 1) (shr outVar_0 1 outVar_1) (eq outVar_1 outVars0)
   ite (eq b2 1) (shr outVar_1 2 outVar_2) (eq outVar_2 outVars1)
   ite (eq b3 1) (shr outVar_2 4 outVar_3) (eq outVar_3 outVars2)
   ite (eq b4 1) (shr outVar_3 8 outVar_4) (eq outVar_4 outVars_3)
   ...
   ite (eq bi 1) (shr outVar_i 2^{i-1} outVar_{i+1}) (eq outVar_{i+1} outVars_{i})
   outVar = outVar_{i+1}

-/

def sEvalBitWiseSHLNonConstShift_Loop {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c)
  (bits : List (FFTerm c))
  (ffVars : List (FFVar))
  (shiftAmount : Nat)
  (accm : ExprSpec c)
  : Except String (ExprSpec c) := do
  match bits, ffVars with
  | [], [] => return accm -- no more bits to process, return true
  | b::bs, ffV::ffVs =>
      let shiftSpec ← sEvalBitWiseSHLAux cfg md senv accm.resTerm shiftAmount ffV
      let cfg' : SymExecConfig c := { cfg with nextId := shiftSpec.nextId }
      let ffVTerm := FFTerm.var ffV
      let newF : FFFormula c := .and accm.f
                                        (.ite (FFFormula.eq b (FFTerm.val 1))
                                              shiftSpec.f
                                              (FFFormula.eq ffVTerm accm.resTerm))
      let newAccm : ExprSpec c := {
                                    inSymEnv := senv,
                                    f := newF,
                                    nextId := cfg'.nextId,
                                    resTerm := ffVTerm,
                                    newFFVars := accm.newFFVars ∪ shiftSpec.newFFVars,
                                    newBoolVars := accm.newBoolVars ∪ shiftSpec.newBoolVars
                                  }
      sEvalBitWiseSHLNonConstShift_Loop cfg md senv bs ffVs (shiftAmount * 2) newAccm
  | _, _ => throw "Mismatched bits and ffVars lists, should not happen!"


def sEvalBitWiseSHLNonConstShift {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  let numOfBits := c.k.log2 +1 -- number of bits needed to represent shift amount
  let ltVar := FFVar.mk cfg.nextId { orig_name := "shift_amount_lt_k", src_info := md.src_info }
  let cfg' : SymExecConfig c := { cfg with nextId := cfg.nextId + 1 }
  -- the +1 because we are using the encoding of lt
  let ltSpec ← sEvalLtUnSignedConstLeft cfg' md senv s2 (SimpleExpr.val (numOfBits+1)) ltVar
  -- we only care about the lower bits that represent the shift amount
  let cfg'' : SymExecConfig c := { cfg' with nextId := ltSpec.nextId }
  let shiftSpec := bitify cfg'' md v2 -- bitify the ltVar to get the bits for the shift amount
  let shiftBits := (shiftSpec.bits.reverse.drop (c.k-numOfBits)).reverse
  let nextId := shiftSpec.nextId
  let ffVars := List.range numOfBits
                 |>.map (fun i => FFVar.mk (nextId + i)
                                           { orig_name := s!"shift_bit_{i}",
                                             src_info := md.src_info
                                          })
  let nextId' := nextId + numOfBits
  let cfg''' : SymExecConfig c := { cfg'' with nextId := nextId' }
  let newFFVars := ffVars.foldl (fun acc v => acc.insert v) (ltSpec.newFFVars ∪ shiftSpec.newFFVars)
  let newBoolVars := ltSpec.newBoolVars ∪ shiftSpec.newBoolVars
  let initExpSpec : ExprSpec c := {
    inSymEnv := senv,
    f := shiftSpec.f,
    resTerm := v1, -- we will update this in the loop, but it needs to be initialized to something
    nextId := nextId',
    newFFVars := newFFVars,
    newBoolVars := newBoolVars
  }
  let finalExpSpec ← sEvalBitWiseSHLNonConstShift_Loop cfg''' md senv shiftBits ffVars 1 initExpSpec
  let f := .and ltSpec.f
                (.ite (.eq ltSpec.resTerm (FFTerm.val 1))
                      (.and finalExpSpec.f
                            (FFFormula.eq (FFTerm.var outFFVar) finalExpSpec.resTerm))
                      (FFFormula.eq (FFTerm.var outFFVar) (FFTerm.val 0)))
  return {
    inSymEnv := senv,
    f := f,
    resTerm := (FFTerm.var outFFVar),
    nextId := finalExpSpec.nextId,
    newFFVars := finalExpSpec.newFFVars,
    newBoolVars := finalExpSpec.newBoolVars
  }


def sEvalBitWiseSHL {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  match sEvalBitWiseSHLConstShift cfg md senv s1 s2 outFFVar with
  | Except.ok spec => return spec
  | Except.error _ => sEvalBitWiseSHLNonConstShift cfg md senv s1 s2 outFFVar



/- SHIFT RIGHT
-/


def sEvalBitWiseSHRAux {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (v1 : FFTerm c) (v2 : Nat) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  if v2 >= c.k then
    -- if shift amount is greater than or equal to bit width, the result is always 0
    return {
      inSymEnv := senv,
      f := FFFormula.eq (FFTerm.var outFFVar) (FFTerm.val 0),
      resTerm := (FFTerm.var outFFVar),
      nextId := cfg.nextId
    }
  else
    let bits1Spec := bitify cfg md v1 -- bitify v1
    let newBits := bits1Spec.bits.drop v2
    let idxs := List.range c.k
    let pows := idxs.map (fun i => FFTerm.val (2 ^ i))
    let shiftedBits := List.zipWith (fun bit pow => FFTerm.mul bit pow) newBits pows
    let sum := match shiftedBits, pows with
               | b::bs, p::ps => List.foldl
                                    (fun acc (bit, pow) => FFTerm.add acc (FFTerm.mul bit pow))
                                    (FFTerm.mul b p)
                                    (List.zip bs ps)
               | _, _ => FFTerm.val 0 -- they are the same length, we reach this with empty lists
    let f : FFFormula c := (.and bits1Spec.f (FFFormula.eq (FFTerm.var outFFVar) sum))
    let newFFVars := bits1Spec.newFFVars
    return {
       inSymEnv := senv,
       f := f,
       resTerm := (FFTerm.var outFFVar),
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


/-

s2 must fit in floor(log2(k))+1 bits, otherwise the result is 0

   ite (< s2 k) (eq outVar 0) F

where F is as follows. Let b1,...,bi be the log2(k)+1 lsb bits of s2

   outVars0 = s1
   ite (eq b1 1) (shr outVar_0 1 outVar_1) (eq outVar_1 outVars0)
   ite (eq b2 1) (shr outVar_1 2 outVar_2) (eq outVar_2 outVars1)
   ite (eq b3 1) (shr outVar_2 4 outVar_3) (eq outVar_3 outVars2)
   ite (eq b4 1) (shr outVar_3 8 outVar_4) (eq outVar_4 outVars_3)
   ...
   ite (eq bi 1) (shr outVar_i 2^{i-1} outVar_{i+1}) (eq outVar_{i+1} outVars_{i})
   outVar = outVar_{i+1}

-/

def sEvalBitWiseSHRNonConstShift_Loop {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c)
  (bits : List (FFTerm c))
  (ffVars : List (FFVar))
  (shiftAmount : Nat)
  (accm : ExprSpec c)
  : Except String (ExprSpec c) := do
  match bits, ffVars with
  | [], [] => return accm -- no more bits to process, return true
  | b::bs, ffV::ffVs =>
      let shiftSpec ← sEvalBitWiseSHRAux cfg md senv accm.resTerm shiftAmount ffV
      let cfg' : SymExecConfig c := { cfg with nextId := shiftSpec.nextId }
      let ffVTerm := FFTerm.var ffV
      let newF : FFFormula c := .and accm.f
                                        (.ite (FFFormula.eq b (FFTerm.val 1))
                                              shiftSpec.f
                                              (FFFormula.eq ffVTerm accm.resTerm))
      let newAccm : ExprSpec c := {
                                    inSymEnv := senv,
                                    f := newF,
                                    nextId := cfg'.nextId,
                                    resTerm := ffVTerm,
                                    newFFVars := accm.newFFVars ∪ shiftSpec.newFFVars,
                                    newBoolVars := accm.newBoolVars ∪ shiftSpec.newBoolVars
                                  }
      sEvalBitWiseSHRNonConstShift_Loop cfg md senv bs ffVs (shiftAmount * 2) newAccm
  | _, _ => throw "Mismatched bits and ffVars lists, should not happen!"


def sEvalBitWiseSHRNonConstShift {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  let numOfBits := c.k.log2 +1 -- number of bits needed to represent shift amount
  let ltVar := FFVar.mk cfg.nextId { orig_name := "shift_amount_lt_k", src_info := md.src_info }
  let cfg' : SymExecConfig c := { cfg with nextId := cfg.nextId + 1 }
  -- the +1 because we are using the encoding of lt
  let ltSpec ← sEvalLtUnSignedConstLeft cfg' md senv s2 (SimpleExpr.val (numOfBits+1)) ltVar
  -- we only care about the lower bits that represent the shift amount
  let cfg'' : SymExecConfig c := { cfg' with nextId := ltSpec.nextId }
  let shiftSpec := bitify cfg'' md v2 -- bitify the ltVar to get the bits for the shift amount
  let shiftBits := (shiftSpec.bits.reverse.drop (c.k-numOfBits)).reverse
  let nextId := shiftSpec.nextId
  let ffVars := List.range numOfBits
                |>.map (fun i => FFVar.mk (nextId + i)
                                          { orig_name := s!"shift_bit_{i}",
                                            src_info := md.src_info
                                          })
  let nextId' := nextId + numOfBits
  let cfg''' : SymExecConfig c := { cfg'' with nextId := nextId' }
  let newFFVars := ffVars.foldl (fun acc v => acc.insert v) (ltSpec.newFFVars ∪ shiftSpec.newFFVars)
  let newBoolVars := ltSpec.newBoolVars ∪ shiftSpec.newBoolVars
  let initExpSpec : ExprSpec c := {
    inSymEnv := senv,
    f := shiftSpec.f,
    resTerm := v1, -- we will update this in the loop, but it needs to be initialized to something
    nextId := nextId',
    newFFVars := newFFVars,
    newBoolVars := newBoolVars
  }
  let finalExpSpec ← sEvalBitWiseSHRNonConstShift_Loop cfg''' md senv shiftBits ffVars 1 initExpSpec
  let f := .and ltSpec.f
                (.ite (.eq ltSpec.resTerm (FFTerm.val 1))
                      (.and finalExpSpec.f
                            (FFFormula.eq (FFTerm.var outFFVar) finalExpSpec.resTerm))
                      (FFFormula.eq (FFTerm.var outFFVar) (FFTerm.val 0)))
  return {
    inSymEnv := senv,
    f := f,
    resTerm := (FFTerm.var outFFVar),
    nextId := finalExpSpec.nextId,
    newFFVars := finalExpSpec.newFFVars,
    newBoolVars := finalExpSpec.newBoolVars
  }

def sEvalBitWiseSHR {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  match sEvalBitWiseSHRConstShift cfg md senv s1 s2 outFFVar with
  | Except.ok spec => return spec
  | Except.error _ => sEvalBitWiseSHRNonConstShift cfg md senv s1 s2 outFFVar

end Llzk.SymExec.SymInstr
