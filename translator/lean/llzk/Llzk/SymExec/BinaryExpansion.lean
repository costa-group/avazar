import Llzk.Language.Core.Syntax.AST
import Llzk.Language.Core.Syntax.Printer
import Llzk.FFConstraints.Basic
import Llzk.SymExec.Basic

namespace Llzk.SymExec.SymInstr

open Llzk.Language.Core.Syntax.AST
open Llzk.FFConstraints.Basic
open Llzk.Language.Core.Semantics.Basic
open Llzk.SymExec.Basic


def bool_ffterm {c : ZKConfig}
  (cfg : SymExecConfig c) (v : FFTerm c) : FFFormula c :=
  match v with
  | FFTerm.val _ =>
    -- we assume it is 0 or 1, later we should elaborate
    FFFormula.true
  | _ =>
    match cfg.ffbool with
    | BoolFFScm.range =>
      FFFormula.range v 0 1
    | BoolFFScm.mul =>
      FFFormula.eq (FFTerm.mul v (FFTerm.sub (FFTerm.val 1) v))
                   (FFTerm.val 0)

def add_bool_ffterm {c : ZKConfig}
  (cfg : SymExecConfig c) (v : FFTerm c) (f : FFFormula c)
  :  FFFormula c :=
  match bool_ffterm cfg v with
  | FFFormula.true => f -- we assume it is 0 or 1
  | bool_v => FFFormula.and f bool_v

/- Binary expansion of a constant is based on BitVec. As an optimization, the number of bits
   is determined by the value of the constant, so we can have fewer bits than c.k.
-/
def binexpn_const {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD) (senv : SymEnv c) (v : FF c)
  : Except String (BinExpanSpec c) :=
  let k := v.val.log2 + 1 -- k is at most c.k
  let w : BitVec k := BitVec.ofNat k v.val -- get the value in as a bit vector
  let idxs := List.range k
  let bits := idxs.map (fun i => if (w.getLsbD i) then FFTerm.val 1 else FFTerm.val 0)
  return {
    inSymEnv := senv,
    outSymEnv := senv,
    nextId := cfg.nextId,
    f := FFFormula.true,
    bits := bits,
    newFFVars := emptyFFVarSet,
    newBoolVars := emptyBoolVarSet
  }


def to_sum {c : ZKConfig}
  (_cfg : SymExecConfig c) (bits : List (FFTerm c)) (v : FFTerm c)
  : FFFormula c :=
    -- sum of bits[i] * 2^i
    let pows := List.range bits.length
    let sum :=
        List.foldl (fun acc (bit, pow) =>
                      match bit, acc with
                      | FFTerm.val m, FFTerm.val n =>
                        FFTerm.val (n + m * (2 ^ pow))
                      | _, FFTerm.val n =>
                        if n = 0 then
                          (FFTerm.mul bit (FFTerm.val (2 ^ pow)))
                        else
                          FFTerm.add acc (FFTerm.mul bit (FFTerm.val (2 ^ pow)))
                      | FFTerm.val m, _ =>
                        if m = 0 then
                          acc
                        else
                          FFTerm.add acc (FFTerm.mul bit (FFTerm.val (2 ^ pow)))
                      | _, _ =>
                          FFTerm.add acc (FFTerm.mul bit (FFTerm.val (2 ^ pow))))
                   (FFTerm.val 0)
                   (List.zip bits pows)
    let sumF := FFFormula.eq v sum
    sumF

def to_sum_with_bit_constraints {c : ZKConfig}
  (cfg : SymExecConfig c) (bits : List (FFTerm c)) (v : FFTerm c)
  : FFFormula c :=
  let sumF := to_sum cfg bits v
  -- add constraints to ensure bits are boolean
  let f := bits.foldl (fun acc bit => add_bool_ffterm cfg bit acc) sumF
  f

def add_deterministic_constraints {c : ZKConfig}
  (_cfg : SymExecConfig c) (var : FFVar) (bits : List (FFTerm c)) (f : FFFormula c)
  : FFFormula c :=
  match bits.getLast? with
  | none => f
  | some msb =>
    let vTerm := FFTerm.var var
    let detF := (.imply (FFFormula.range vTerm 0 (c.midpoint-1))
                      (FFFormula.eq msb (FFTerm.val 0)))
    FFFormula.and f detF

def binexpn_var {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD) (senv : SymEnv c) (id : VarID) (v : FFVarWithBinRep c)
  : Except String (BinExpanSpec c) :=
  match v.bits with
  | none =>
    let startId := cfg.nextId
    let idxs := List.range c.k
    let ffVars := idxs.map (fun i => FFVar.mk (startId + i)
                                            { src_info := md.src_info,
                                              orig_name := s!"bit{i}"
                                            })
    let bits := ffVars.map (fun v => FFTerm.var v)
    let f' := to_sum_with_bit_constraints cfg bits (FFTerm.var v.var)
    let f := add_deterministic_constraints cfg v.var bits f'
    let senv' := setVar senv id (SymValue.ffVar (SymFFVar.var { var := v.var, bits := some bits }))
    return {
      inSymEnv := senv,
      outSymEnv := senv',
      nextId := cfg.nextId + c.k,
      bits := bits,
      f := f,
      newFFVars := Std.TreeSet.ofList ffVars,
      newBoolVars := emptyBoolVarSet
    }
  | some bits =>
    return {
      inSymEnv := senv,
      outSymEnv := senv,
      nextId := cfg.nextId,
      -- no need to relate the bits to the original variable, since it is already done
      f := FFFormula.true,
      bits := bits,
      newFFVars := emptyFFVarSet,
      newBoolVars := emptyBoolVarSet
    }

def binexpn {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD) (senv : SymEnv c) (s : SimpleExpr c)
  : Except String (BinExpanSpec c) :=
  match s with
  | .var id => match getVar senv id with
    | Except.ok (SymValue.ffVar (SymFFVar.const v)) =>
        binexpn_const cfg md senv v
    | Except.ok (SymValue.ffVar (SymFFVar.var v)) =>
        binexpn_var cfg md senv id v
    | Except.ok (SymValue.ffArray _) => Except.error s!"Variable '{id}' is an array"
    | Except.error err => Except.error err
  | .val v => binexpn_const cfg md senv v




end Llzk.SymExec.SymInstr
