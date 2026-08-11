import Corellzk2smt.Config
import Corellzk2smt.SymExec.Basic
import Corellzk2smt.FFConstraints.Basic
import Corellzk2smt.Language.Core.Syntax.AST

namespace Corellzk2smt.SymExec.BinaryExpansion

open Corellzk2smt.Config
open Corellzk2smt.SymExec.Basic
open Corellzk2smt.FFConstraints.Basic
open Corellzk2smt.Language.Core.Syntax.AST

/-- Encodes "`v`'s value is `0` or `1`," under whichever of the two schemes
    `gconf.sym_exec.boolFFVarScm` selects. For a literal `.val x`, there is nothing to encode as a
    formula -- instead `x` itself is checked directly, right here, and rejected with
    `Except.error` if it isn't actually `0` or `1` (a constant that isn't boolean can never be made
    boolean by any formula, so failing fast here is the only sound option). -/
def bool_ffterm {c : ZKConfig}
    (gconf : GlobalConfig c)
    (_sconf : SymExecConfig c)
  (v : FFTerm c) : Except String (FFFormula c) :=
  match v with
  | FFTerm.val x =>
    if x = 0 ∨ x = 1 then
      Except.ok FFFormula.true
    else
      Except.error "bool_ffterm: constant value is not 0 or 1"
  | _ =>
    match gconf.sym_exec.boolFFVarScm with
    | .range =>
      Except.ok (FFFormula.range v 0 1)
    | .mul =>
      Except.ok (FFFormula.eq (FFTerm.mul v (FFTerm.sub (FFTerm.val 1) v))
                   (FFTerm.val 0))


/-- Encodes "`x` is the weighted sum of `bits`, least-significant bit first," i.e.
    `x = bits[0]*2^0 + bits[1]*2^1 + ...`. -/
def gen_bin_rep {c : ZKConfig}
    (_gconf : GlobalConfig c)
    (_scfg : SymExecConfig c)
    (bits : List (FFTerm c))
    (x : FFTerm c)
  : FFFormula c :=
    let sum := (bits.zip (List.range bits.length)).foldl
      (fun acc (bit, pow) => FFTerm.add acc (FFTerm.mul bit (FFTerm.val (2 ^ pow))))
      (FFTerm.val 0)
    FFFormula.eq x sum

def fetch_bin_rep_const {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (senv : SymEnv c)
    (v : FF c)
  : Except String (SymEnv c × List (FFTerm c) × Nat × FFFormula c) :=
  let k := v.val.log2 + 1 -- k is at most c.k
  let w : BitVec k := BitVec.ofNat k v.val -- get the value in as a bit vector
  let idxs := List.range k
  let bits := idxs.map (fun i => if (w.getLsbD i) then FFTerm.val 1 else FFTerm.val 0)
  Except.ok (senv, bits, sconf.nextVarId, FFFormula.true)

def fetch_bin_rep_var {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (senv : SymEnv c)
    (id : VarID)
    (v : FFVarWithBinRep c)
  : Except String (SymEnv c × List (FFTerm c) × Nat × FFFormula c) :=
  match v.bits with
  | none =>
      let startId := sconf.nextVarId
      let idxs := List.range c.k
      let bits := idxs.map (fun i => FFTerm.var (startId + i))
      let f := gen_bin_rep gconf sconf bits (FFTerm.var v.var)
      let senv' := setVar senv id (SymValue.simple (SimpleSymVal.ffvar { var := v.var, bits := some bits }))
      Except.ok (senv', bits, sconf.nextVarId, f)
  | some bits =>
      Except.ok (senv, bits, sconf.nextVarId, FFFormula.true)

def fetch_bin_rep {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (senv : SymEnv c)
    (s : SimpleExpr c)
  : Except String (SymEnv c × List (FFTerm c) × Nat × FFFormula c) :=
  match s with
  | .var id =>
      match getVar senv id with
        | Except.error msg =>
            Except.error msg
        | Except.ok (SymValue.array _) =>
            Except.error s!"Variable '{id}' is an array"
        | Except.ok (SymValue.simple (SimpleSymVal.ffvar v)) =>
            fetch_bin_rep_var md gconf sconf senv id v
        | Except.ok (SymValue.simple (SimpleSymVal.const v)) =>
            fetch_bin_rep_const md gconf sconf senv v
  | .val v =>
        fetch_bin_rep_const md gconf sconf senv v

end Corellzk2smt.SymExec.BinaryExpansion
