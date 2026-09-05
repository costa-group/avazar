import Llzk.Language.Core.Syntax.AST
import Llzk.Language.Core.Syntax.Printer
import Llzk.FFConstraints.Basic
import Llzk.SymExec.Basic
import Llzk.SymExec.Common
import Llzk.SymExec.BinaryExpansion
import Llzk.SymExec.BoolExpr



namespace Llzk.SymExec.SymInstr

open Llzk.Language.Core.Syntax.AST
open Llzk.FFConstraints.Basic
open Llzk.Language.Core.Semantics.Basic
open Llzk.SymExec.Basic

/-
The bitwise operations are:

  and, or, xor, not, shift left, and shift right
-/

abbrev f_bin_calc_t (c : ZKConfig) :=
  SymExecConfig c → CmdMD → FFTerm c → FFTerm c → (FFTerm c × List FFVar × Nat × FFFormula c)

abbrev f_mono_calc_t (c : ZKConfig) :=
  SymExecConfig c → CmdMD → FFTerm c → (FFTerm c × List FFVar × Nat × FFFormula c)

-- $r_i = a_i * b_i$
def calc_and {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD) (b1 b2 : (FFTerm c))
  : (FFTerm c) × List FFVar × Nat × FFFormula c :=
  match b1, b2 with
  | FFTerm.val n1, FFTerm.val n2 =>
    (FFTerm.val (n1.val * n2.val), [], cfg.nextId, FFFormula.true)
  | FFTerm.val n, _ =>
    if n.val = 0 then
      (FFTerm.val 0, [], cfg.nextId, FFFormula.true)
    else
      (b2, [], cfg.nextId, FFFormula.true)
  | _, FFTerm.val n =>
    if n.val = 0 then
      (FFTerm.val 0, [], cfg.nextId, FFFormula.true)
    else
     (b1, [], cfg.nextId, FFFormula.true)
  | _, _ =>
      let bitVar : FFVar := FFVar.mk cfg.nextId { src_info := md.src_info,
                                                  orig_name := s!"bit{cfg.nextId}"
                                                }
      let f := FFFormula.eq (FFTerm.var bitVar) (FFTerm.mul b1 b2)
      let cfg' := { cfg with nextId := cfg.nextId + 1 }
      let f' := add_bool_ffterm cfg' (FFTerm.var bitVar) f
      (FFTerm.var bitVar,[bitVar],cfg'.nextId,f')

-- $r_i = a_i + b_i - a_i * b_i$
def calc_or {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD) (b1 b2 : (FFTerm c))
  : (FFTerm c) × List FFVar × Nat × FFFormula c :=
  match b1, b2 with
  | FFTerm.val n1, FFTerm.val n2 =>
    (FFTerm.val (n1.val + n2.val - n1.val * n2.val), [], cfg.nextId, FFFormula.true)
  | FFTerm.val n, _ =>
    if n.val = 0 then
      (b2, [], cfg.nextId, FFFormula.true)
    else
      (FFTerm.val 1, [], cfg.nextId, FFFormula.true)
  | _, FFTerm.val n =>
    if n.val = 0 then
      (b1, [], cfg.nextId, FFFormula.true)
    else
      (FFTerm.val 1, [], cfg.nextId, FFFormula.true)
  | _, _ =>
      let bitVar : FFVar := FFVar.mk cfg.nextId { src_info := md.src_info,
                                                  orig_name := s!"bit{cfg.nextId}"
                                                }
      let f := FFFormula.eq (FFTerm.var bitVar) (FFTerm.sub (FFTerm.add b1 b2) (FFTerm.mul b1 b2))
      let cfg' := { cfg with nextId := cfg.nextId + 1 }
      let f' := add_bool_ffterm cfg' (FFTerm.var bitVar) f
      (FFTerm.var bitVar,[bitVar],cfg'.nextId,f')

--  $r_i = a_i + b_i - 2 * a_i * b_i$ for each bit
def calc_xor {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD) (b1 b2 : (FFTerm c))
  : (FFTerm c) × List FFVar × Nat × FFFormula c :=
  match b1, b2 with
  | FFTerm.val n1, FFTerm.val n2 =>
    (FFTerm.val (n1.val + n2.val - 2 * n1.val * n2.val), [], cfg.nextId, FFFormula.true)
  | FFTerm.val n, _ =>
    if n.val = 0 then
      (b2, [], cfg.nextId, FFFormula.true)
    else
      let bitVar : FFVar := FFVar.mk cfg.nextId { src_info := md.src_info,
                                                  orig_name := s!"bit{cfg.nextId}"
                                                }
       let f := FFFormula.eq (FFTerm.var bitVar) (FFTerm.sub (FFTerm.val 1) b2)
       let cfg' := { cfg with nextId := cfg.nextId + 1 }
       let f' := add_bool_ffterm cfg' (FFTerm.var bitVar) f
       (FFTerm.var bitVar,[bitVar],cfg'.nextId,f')
  | _, FFTerm.val n =>
    if n.val = 0 then
      (b1, [], cfg.nextId, FFFormula.true)
    else
      let bitVar : FFVar := FFVar.mk cfg.nextId { src_info := md.src_info,
                                                  orig_name := s!"bit{cfg.nextId}"
                                                }
       let f := FFFormula.eq (FFTerm.var bitVar) (FFTerm.sub (FFTerm.val 1) b1)
       let cfg' := { cfg with nextId := cfg.nextId + 1 }
       let f' := add_bool_ffterm cfg' (FFTerm.var bitVar) f
       (FFTerm.var bitVar,[bitVar],cfg'.nextId,f')
  | _, _ =>
      let bitVar : FFVar := FFVar.mk cfg.nextId { src_info := md.src_info,
                                                  orig_name := s!"bit{cfg.nextId}"
                                                }
      let f := FFFormula.eq (FFTerm.var bitVar)
                            (FFTerm.sub (FFTerm.add b1 b2)
                                        (FFTerm.mul (FFTerm.mul (FFTerm.val 2) b1) b2))
      let cfg' := { cfg with nextId := cfg.nextId + 1 }
      let f' := add_bool_ffterm cfg' (FFTerm.var bitVar) f
      (FFTerm.var bitVar,[bitVar],cfg'.nextId,f' )

-- $r_i = a_i * b_i$
def calc_not {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD) (b : (FFTerm c))
  : (FFTerm c) × List FFVar × Nat × FFFormula c :=
  match b with
  | FFTerm.val n =>
    (FFTerm.val (1-n.val), [], cfg.nextId, FFFormula.true)
  | _ =>
      let bitVar : FFVar := FFVar.mk cfg.nextId { src_info := md.src_info,
                                                  orig_name := s!"bit{cfg.nextId}"
                                                }
      let f := FFFormula.eq (FFTerm.var bitVar) (FFTerm.sub (FFTerm.val 1) b)
      let cfg' := { cfg with nextId := cfg.nextId + 1 }
      let f' := add_bool_ffterm cfg' (FFTerm.var bitVar) f
      (FFTerm.var bitVar,[bitVar],cfg'.nextId,f')

def sEvalBinBitWiseOp_aux {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (bits1 bits2 : List (FFTerm c))
  (f_calc : f_bin_calc_t c)
  : List (FFTerm c) × List FFVar × Nat × FFFormula c :=
  match bits1, bits2 with
  | [], [] => ([], [], cfg.nextId, FFFormula.true)
  | b1 :: bs1, b2 :: bs2 =>
    let (outBit, newFFVars, nextId, maybeFormula) := f_calc cfg md b1 b2
    let cfg' := { cfg with nextId := nextId }
    let (outBits', outVars', nextId', outFormula') := sEvalBinBitWiseOp_aux cfg' md bs1 bs2 f_calc
    let f := match maybeFormula with
             | FFFormula.true => outFormula'
             | _ => FFFormula.and maybeFormula outFormula'
    (outBit :: outBits', newFFVars ++ outVars', nextId', f)
  | b1 :: bs1, [] =>
    let b2 := FFTerm.val 0
    let bs2 := []
    let (outBit, newFFVars, nextId, maybeFormula) := f_calc cfg md b1 b2
    let cfg' := { cfg with nextId := nextId }
    let (outBits', outVars', nextId', outFormula') := sEvalBinBitWiseOp_aux cfg' md bs1 bs2 f_calc
    let f := match maybeFormula with
             | FFFormula.true => outFormula'
             | _ => FFFormula.and maybeFormula outFormula'
    (outBit :: outBits', newFFVars ++ outVars', nextId', f)
  | [], b2 :: bs2 =>
    let b1 := FFTerm.val 0
    let bs1 := []
    let (outBit, newFFVars, nextId, maybeFormula) := f_calc cfg md b1 b2
    let cfg' := { cfg with nextId := nextId }
    let (outBits', outVars', nextId', outFormula') := sEvalBinBitWiseOp_aux cfg' md bs1 bs2 f_calc
    let f := match maybeFormula with
             | FFFormula.true => outFormula'
             | _ => FFFormula.and maybeFormula outFormula'
    (outBit :: outBits', newFFVars ++ outVars', nextId', f)

def sEvalBinBitWiseOp {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  (f_calc : f_bin_calc_t c)
  : Except String (ExprSpec c) := do
  let outFFVar : FFVar := { id := cfg.nextId,
                            meta_data := { src_info := md.src_info, orig_name := id}
                          }
  let outFFVarTerm := FFTerm.var outFFVar
  let cfg' := { cfg with nextId := cfg.nextId+1 }
  let binExpanSpec1 ← binexpn cfg' md senv s1
  let cfg'' := { cfg with nextId := binExpanSpec1.nextId }
  let binExpanSpec2 ← binexpn cfg'' md binExpanSpec1.outSymEnv s2
  let cfg''' := { cfg' with nextId := binExpanSpec2.nextId }
  let (outBits, outVars, nextId, outFormula) :=
    sEvalBinBitWiseOp_aux cfg''' md binExpanSpec1.bits binExpanSpec2.bits f_calc
  let cfg'''' := { cfg''' with nextId := nextId }
  let sum := to_sum cfg'''' outBits outFFVarTerm
  let f := FFFormula.and binExpanSpec1.f (.and binExpanSpec2.f (.and outFormula sum))
  let senv' := binExpanSpec2.outSymEnv
  return {
    inSymEnv := senv,
    outSymEnv := senv',
    nextId := cfg''''.nextId,
    resTerm := outFFVarTerm,
    res := SymFFVar.var ⟨outFFVar, outBits⟩,
    f := f,
    newFFVars := binExpanSpec1.newFFVars ∪ binExpanSpec2.newFFVars ∪
                 (Std.TreeSet.ofList outVars) ∪ {outFFVar},
    newBoolVars := emptyBoolVarSet
  }


def sEvalMonoBitWiseOp_aux {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (bits : List (FFTerm c))
  (f_calc : f_mono_calc_t c)
  : List (FFTerm c) × List FFVar × Nat × FFFormula c :=
  match bits with
  | [] => ([], [], cfg.nextId, FFFormula.true)
  | b :: bs =>
    let (outBit, newFFVars, nextId, maybeFormula) := f_calc cfg md b
    let cfg' := { cfg with nextId := nextId }
    let (outBits', outVars', nextId', outFormula') := sEvalMonoBitWiseOp_aux cfg' md bs f_calc
    let f := match maybeFormula with
             | FFFormula.true => outFormula'
             | _ => FFFormula.and maybeFormula outFormula'
    (outBit :: outBits', newFFVars ++ outVars', nextId', f)

def sEvalMonoBitWiseOp {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s : SimpleExpr c) (id : VarID)
  (f_calc : f_mono_calc_t c)
  : Except String (ExprSpec c) := do
  let outFFVar : FFVar := { id := cfg.nextId,
                            meta_data := { src_info := md.src_info, orig_name := id}
                          }
  let outFFVarTerm := FFTerm.var outFFVar
  let binExpanSpec ← binexpn cfg md senv s
  let cfg' := { cfg with nextId := binExpanSpec.nextId }
  let (outBits, outVars, nextId, outFormula) :=
    sEvalMonoBitWiseOp_aux cfg' md binExpanSpec.bits f_calc
  let cfg'' := { cfg' with nextId := nextId }
  let sum  := to_sum cfg'' outBits outFFVarTerm
  let f := FFFormula.and binExpanSpec.f (.and outFormula sum)
  let senv' := binExpanSpec.outSymEnv
  return {
    inSymEnv := senv,
    outSymEnv := senv',
    nextId := cfg''.nextId,
    resTerm := outFFVarTerm,
    res := SymFFVar.var ⟨outFFVar, outBits⟩,
    f := f,
    newFFVars := binExpanSpec.newFFVars ∪ (Std.TreeSet.ofList outVars) ∪ {outFFVar},
    newBoolVars := emptyBoolVarSet
  }


def sEvalBitwiseAND {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  sEvalBinBitWiseOp cfg md senv s1 s2 id calc_and

def sEvalBitwiseOR {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  sEvalBinBitWiseOp cfg md senv s1 s2 id calc_or

def sEvalBitwiseXOR {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  sEvalBinBitWiseOp cfg md senv s1 s2 id calc_xor

def sEvalBitwiseNOT {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  sEvalMonoBitWiseOp cfg md senv s id calc_not


/- SHIFT LEFT
-/

def sEvalBitWiseSHLAux {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 : SimpleExpr c) (v2 : Nat) (id : VarID)
  : Except String (ExprSpec c) := do
  if v2 >= c.k then
    -- if shift amount is greater than or equal to bit width, the result is always 0
    return {
      inSymEnv := senv,
      outSymEnv := senv,
      f := FFFormula.true,
      resTerm := (FFTerm.val 0),
      res := SymFFVar.const 0,
      nextId := cfg.nextId,
      newFFVars := emptyFFVarSet,
      newBoolVars := emptyBoolVarSet
    }
  else
    let outFFVar : FFVar := { id := cfg.nextId,
                              meta_data := { src_info := md.src_info, orig_name := id}
                            }
    let outFFVarTerm := FFTerm.var outFFVar
    let cfg' := { cfg with nextId := cfg.nextId+1 }
    let binExpanSpec ← binexpn cfg' md senv s1
    let newBits := (binExpanSpec.bits.reverse.drop v2).reverse
    let cfg'' := { cfg' with nextId := binExpanSpec.nextId }
    let sum := to_sum cfg'' newBits outFFVarTerm
    let f : FFFormula c := (.and binExpanSpec.f  sum)
    let newFFVars := binExpanSpec.newFFVars ∪ { outFFVar }
    return {
      inSymEnv := senv,
      outSymEnv := binExpanSpec.outSymEnv,
      f := f,
      resTerm := (FFTerm.var outFFVar),
      res := SymFFVar.var ⟨outFFVar, newBits⟩,
      nextId := cfg''.nextId,
      newFFVars := newFFVars
      newBoolVars := emptyBoolVarSet
    }

def sEvalBitWiseSHLConstShift {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  let v2 ← simpleExprToFF senv s2 -- the number of bits
  sEvalBitWiseSHLAux cfg md senv s1 v2.val id



/-

* bit.shl s1 s2  (right shift s1 by s2 bits)
* k is the number of bit of the prime
* Let [b_0,...,b_{log2(k)+1}] be the log2(k)+1 lsb bits of s2, and [bit_1,...,bit_k] be
  the bits of s1


f  := the formulas produced when bitifying s1 and s2
Bs := [bit_1,...,bit_k]
for i in [0,...,log2(k)+1] {
  Bs' := a list of new fresh bits of length k
  Bs'' := shl Bs by (2^i), add (2^i) zero bits at the end to get length k
  F1 := A formula stating that the variables of Bs' and Bs are equal
  F2 := A formula stating that the variables of Bs' and Bs'' are equal
  FB := a formula stating that all new variables in Bs' are boolean
  f := f ∧ FB ∧ ite(b_{i}=1, F2,  F1)
  Bs := Bs'
}

f'  := A formula stating that all Bs are 0 (here Bs are the last bits used for the result)
f'' := A formula stating that all Bs are boolean (maybe not needed because they are forced to be 0)
f''' := ite( (range s2 0 k), f, (f' ∧ f'') ) /\ res = sum_i 2^i * Bi

return (f''' , <res, Bs>)

-/


def sEvalBitWiseSHLNonConstShift_Loop {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD) (id : VarID)
  (shiftAmountBits : List (FFTerm c))
  (bitNum : Nat)
  (currValueBits : List (FFTerm c))
  (accmF : FFFormula c)
  (ffVarsAccm : FFVarSet)
  (boolVarsAccm : BoolVarSet)
  -- result bits, formula, nextId, newFFVars, newBoolVars
  : Except String (List (FFTerm c) × (FFFormula c) × Nat × FFVarSet × BoolVarSet) := do
  match shiftAmountBits with
  | [] => return (currValueBits, accmF, bitNum, ffVarsAccm, boolVarsAccm)
  | b::bs =>
      let n := 2^bitNum -- the number of bits to shift
      let startId := cfg.nextId -- the starting ID for the new FFVars
      -- generate a list of new FFVars for the new bits (and a corresponding list of terms)
      let idxs := List.range c.k
      let ffVars := idxs.map (fun i => FFVar.mk (startId + i)
                                            { src_info := md.src_info,
                                              orig_name := s!"bit{i}"
                                            })
      let ffVarsBits := ffVars.map (fun v => FFTerm.var v)
      -- state that all new variables are boolean. We add these constraints to the accumulated formula
      let accmF' := ffVarsBits.foldl (fun acc bit => add_bool_ffterm cfg bit acc) accmF
      -- shift currValueBits : List (FFTerm c) by n
      -- we remove the last n bits of currValueBits and then add n zero at the beginning
      let shiftedBits := List.replicate n (FFTerm.val 0) ++ (currValueBits.reverse.drop n).reverse
      -- a formula stating that the bits of ffVarsBits and currValueBits are equal
      let F1 := (List.zip ffVarsBits currValueBits |>.foldl (fun acc (a, b) => FFFormula.and acc (FFFormula.eq a b)) .true)
      -- a formula stating that the bits of ffVarsBits and shiftedBits are equal
      let F2 := (List.zip ffVarsBits shiftedBits |>.foldl (fun acc (a, b) => FFFormula.and acc (FFFormula.eq a b)) .true)
      -- combine the two formulas using an if-then-else based on the value of the current bit of the shift amount
      let accmF'' := FFFormula.and accmF' (.ite (.eq b (FFTerm.val 1)) F2 F1)
      -- instead the new variables are added to the accumulated sets
      let ffVarsAccm := ffVarsAccm.insertMany ffVars
      let cfg'' := { cfg with nextId := startId + c.k }
      sEvalBitWiseSHLNonConstShift_Loop cfg'' md id bs (bitNum+1) ffVarsBits accmF'' ffVarsAccm boolVarsAccm

def sEvalBitWiseSHLNonConstShift {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  let v2 ← simpleExprToTerm senv s2
  let numOfBits := c.k.log2 + 1 -- number of bits needed to represent the shift amount
  let binExpanSpec_for_s2 ← binexpn cfg md senv s2 -- convert the shift amount to bits
  -- it must fit in numOfBits, so we drop the bits beyond numOfBits
  let shiftBits := (binExpanSpec_for_s2.bits.reverse.drop (c.k-numOfBits)).reverse
  let cfg' := { cfg with nextId := binExpanSpec_for_s2.nextId }
  let binExpanSpec_for_s1 ← binexpn cfg' md binExpanSpec_for_s2.outSymEnv s1 -- convert the value to bits
  let cfg'' := { cfg with nextId := binExpanSpec_for_s1.nextId }
  -- generate the actual shifted bits and the corresponding formula, as described above
  let (lastBits, f, nextId, newFFVars, newBoolVars) ←
      sEvalBitWiseSHLNonConstShift_Loop
         cfg'' md id
         shiftBits 0 binExpanSpec_for_s1.bits (.and binExpanSpec_for_s2.f binExpanSpec_for_s1.f)
         emptyFFVarSet
         emptyBoolVarSet
  let outFFVar : FFVar := { id := nextId,
                            meta_data := { src_info := md.src_info, orig_name := id}
                          }
  let outFFVarTerm := FFTerm.var outFFVar
  let cfg''' := { cfg with nextId := nextId+1 }
  -- generate the sum formula for the shifted bits
  let sum_f := to_sum cfg''' lastBits outFFVarTerm
  let lastBits_are_0 := lastBits.foldl (fun acc b => .and acc (.eq b (FFTerm.val 0))) FFFormula.true
  -- to ensure that s2 is less than k, otherwise the result will be  0
  let s2_lt_k := FFFormula.range v2 0 c.k
  let f' := lastBits.foldl (fun acc bit => add_bool_ffterm cfg bit acc) (.and lastBits_are_0 (.eq outFFVarTerm (FFTerm.val 0)))
  let f'' := (.and (.ite s2_lt_k f f') sum_f)
  return {
    inSymEnv := senv,
    outSymEnv := binExpanSpec_for_s1.outSymEnv,
    f := f'',
    resTerm := outFFVarTerm
    res := SymFFVar.var ⟨outFFVar, lastBits⟩,
    nextId := cfg'''.nextId,
    newFFVars := binExpanSpec_for_s2.newFFVars ∪ binExpanSpec_for_s1.newFFVars ∪ newFFVars ∪ { outFFVar },
    newBoolVars := binExpanSpec_for_s2.newBoolVars ∪ binExpanSpec_for_s1.newBoolVars ∪ newBoolVars
  }

def sEvalBitwiseSHL {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  match sEvalBitWiseSHLConstShift cfg md senv s1 s2 id with
  | Except.ok spec => return spec
  | Except.error _ => sEvalBitWiseSHLNonConstShift cfg md senv s1 s2 id


def sEvalBitWiseSHRAux {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 : SimpleExpr c) (v2 : Nat) (id : VarID)
  : Except String (ExprSpec c) := do
  if v2 >= c.k then
    -- if shift amount is greater than or equal to bit width, the result is always 0
    return {
      inSymEnv := senv,
      outSymEnv := senv,
      f := FFFormula.true,
      resTerm := (FFTerm.val 0),
      res := SymFFVar.const 0,
      nextId := cfg.nextId,
      newFFVars := emptyFFVarSet,
      newBoolVars := emptyBoolVarSet
    }
  else
    let outFFVar : FFVar := { id := cfg.nextId,
                              meta_data := { src_info := md.src_info, orig_name := id}
                            }
    let outFFVarTerm := FFTerm.var outFFVar
    let cfg' := { cfg with nextId := cfg.nextId+1 }
    let binExpanSpec ← binexpn cfg' md senv s1
    let newBits := binExpanSpec.bits.drop v2
    let cfg'' := { cfg' with nextId := binExpanSpec.nextId }
    let sum := to_sum cfg'' newBits outFFVarTerm
    let f : FFFormula c := (.and binExpanSpec.f  sum)
    let newFFVars := binExpanSpec.newFFVars ∪ { outFFVar }
    return {
      inSymEnv := senv,
      outSymEnv := binExpanSpec.outSymEnv,
      f := f,
      resTerm := (FFTerm.var outFFVar),
      res := SymFFVar.var ⟨outFFVar, newBits⟩,
      nextId := cfg''.nextId,
      newFFVars := newFFVars
      newBoolVars := emptyBoolVarSet
    }


def sEvalBitWiseSHRConstShift {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  let v2 ← simpleExprToFF senv s2 -- the number of bits
  sEvalBitWiseSHRAux cfg md senv s1 v2.val id



/-

* bit.shr s1 s2  (right shift s1 by s2 bits)
* k is the number of bit of the prime
* Let [b_0,...,b_{log2(k)+1}] be the log2(k)+1 lsb bits of s2, and [bit_1,...,bit_k] be
  the bits of s1


f  := the formulas produced when bitifying s1 and s2
Bs := [bit_1,...,bit_k]
for i in [0,...,log2(k)+1] {
  Bs' := a list of new fresh bits of length k
  Bs'' := shr Bs by (2^i), add (2^i) zero bits at the beginning to get length k
  F1 := A formula stating that the variables of Bs' and Bs are equal
  F2 := A formula stating that the variables of Bs' and Bs'' are equal
  FB := a formula stating that all new variables in Bs' are boolean
  f := f ∧ FB ∧ ite(b_{i}=1, F2,  F1)
  Bs := Bs'
}

f'  := A formula stating that all Bs are 0 (here Bs are the last bits used for the result)
f'' := A formula stating that all Bs are boolean (maybe not needed because they are forced to be 0)
f''' := ite( (range s2 0 k), f, (f' ∧ f'') ) /\ res = sum_i 2^i * Bi

return (f''' , <res, Bs>)

-/


def sEvalBitWiseSHRNonConstShift_Loop {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD) (id : VarID)
  (shiftAmountBits : List (FFTerm c))
  (bitNum : Nat)
  (currValueBits : List (FFTerm c))
  (accmF : FFFormula c)
  (ffVarsAccm : FFVarSet)
  (boolVarsAccm : BoolVarSet)
  -- result bits, formula, nextId, newFFVars, newBoolVars
  : Except String (List (FFTerm c) × (FFFormula c) × Nat × FFVarSet × BoolVarSet) := do
  match shiftAmountBits with
  | [] => return (currValueBits, accmF, bitNum, ffVarsAccm, boolVarsAccm)
  | b::bs =>
      let n := 2^bitNum -- the number of bits to shift
      let startId := cfg.nextId -- the starting ID for the new FFVars
      -- generate a list of new FFVars for the new bits (and a corresponding list of terms)
      let idxs := List.range c.k
      let ffVars := idxs.map (fun i => FFVar.mk (startId + i)
                                            { src_info := md.src_info,
                                              orig_name := s!"bit{i}"
                                            })
      let ffVarsBits := ffVars.map (fun v => FFTerm.var v)
      -- state that all new variables are boolean. We add these constraints to the accumulated formula
      let accmF' := ffVarsBits.foldl (fun acc bit => add_bool_ffterm cfg bit acc) accmF
      -- shift currValueBits : List (FFTerm c) by n
      -- we remove the first n bits of currValueBits and then add n zero at the end
      let shiftedBits := currValueBits.drop n ++ List.replicate n (FFTerm.val 0)
      -- a formula stating that the bits of ffVarsBits and currValueBits are equal
      let F1 := (List.zip ffVarsBits currValueBits |>.foldl (fun acc (a, b) => FFFormula.and acc (FFFormula.eq a b)) .true)
      -- a formula stating that the bits of ffVarsBits and shiftedBits are equal
      let F2 := (List.zip ffVarsBits shiftedBits |>.foldl (fun acc (a, b) => FFFormula.and acc (FFFormula.eq a b)) .true)
      -- combine the two formulas using an if-then-else based on the value of the current bit of the shift amount
      let accmF'' := FFFormula.and accmF' (.ite (.eq b (FFTerm.val 1)) F2 F1)
      -- instead the new variables are added to the accumulated sets
      let ffVarsAccm := ffVarsAccm.insertMany ffVars
      let cfg'' := { cfg with nextId := startId + c.k }
      sEvalBitWiseSHRNonConstShift_Loop cfg'' md id bs (bitNum+1) ffVarsBits accmF'' ffVarsAccm boolVarsAccm

def sEvalBitWiseSHRNonConstShift {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  let v2 ← simpleExprToTerm senv s2
  let numOfBits := c.k.log2 + 1 -- number of bits needed to represent the shift amount
  let binExpanSpec_for_s2 ← binexpn cfg md senv s2 -- convert the shift amount to bits
  -- it must fit in numOfBits, so we drop the bits beyond numOfBits
  let shiftBits := (binExpanSpec_for_s2.bits.reverse.drop (c.k-numOfBits)).reverse
  let cfg' := { cfg with nextId := binExpanSpec_for_s2.nextId }
  let binExpanSpec_for_s1 ← binexpn cfg' md binExpanSpec_for_s2.outSymEnv s1 -- convert the value to bits
  let cfg'' := { cfg with nextId := binExpanSpec_for_s1.nextId }
  -- generate the actual shifted bits and the corresponding formula, as described above
  let (lastBits, f, nextId, newFFVars, newBoolVars) ←
      sEvalBitWiseSHRNonConstShift_Loop
         cfg'' md id
         shiftBits 0 binExpanSpec_for_s1.bits (.and binExpanSpec_for_s2.f binExpanSpec_for_s1.f)
         emptyFFVarSet
         emptyBoolVarSet
  let outFFVar : FFVar := { id := nextId,
                            meta_data := { src_info := md.src_info, orig_name := id}
                          }
  let outFFVarTerm := FFTerm.var outFFVar
  let cfg''' := { cfg with nextId := nextId+1 }
  -- generate the sum formula for the shifted bits
  let sum_f := to_sum cfg''' lastBits outFFVarTerm
  let lastBits_are_0 := lastBits.foldl (fun acc b => .and acc (.eq b (FFTerm.val 0))) FFFormula.true
  -- to ensure that s2 is less than k, otherwise the result will be  0
  let s2_lt_k := FFFormula.range v2 0 c.k
  let f' := lastBits.foldl (fun acc bit => add_bool_ffterm cfg bit acc) (.and lastBits_are_0 (.eq outFFVarTerm (FFTerm.val 0)))
  let f'' := (.and (.ite s2_lt_k f f') sum_f)
  return {
    inSymEnv := senv,
    outSymEnv := binExpanSpec_for_s1.outSymEnv,
    f := f'',
    resTerm := outFFVarTerm
    res := SymFFVar.var ⟨outFFVar, lastBits⟩,
    nextId := cfg'''.nextId,
    newFFVars := binExpanSpec_for_s2.newFFVars ∪ binExpanSpec_for_s1.newFFVars ∪ newFFVars ∪ { outFFVar },
    newBoolVars := binExpanSpec_for_s2.newBoolVars ∪ binExpanSpec_for_s1.newBoolVars ∪ newBoolVars
  }

def sEvalBitwiseSHR {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  match sEvalBitWiseSHRConstShift cfg md senv s1 s2 id with
  | Except.ok spec => return spec
  | Except.error _ => sEvalBitWiseSHRNonConstShift cfg md senv s1 s2 id

end Llzk.SymExec.SymInstr
