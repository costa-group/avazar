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

def sEvalBitwiseSHL {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  match sEvalBitWiseSHLConstShift cfg md senv s1 s2 id with
  | Except.ok spec => return spec
  | Except.error _ =>  Except.error "Non-constant shl is not supported yet"


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


def sEvalBitwiseSHR {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (id : VarID)
  : Except String (ExprSpec c) := do
  match sEvalBitWiseSHRConstShift cfg md senv s1 s2 id with
  | Except.ok spec => return spec
  | Except.error _ =>  Except.error "Non-constant shr is not supported yet"

end Llzk.SymExec.SymInstr
