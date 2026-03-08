import Llzk.Language.Core.Syntax.AST
import Llzk.Language.Core.Syntax.Printer
import Llzk.FFConstraints.Basic
import Llzk.SymExec.Basic

namespace Llzk.SymExec.SymInstr

open Llzk.Language.Core.Syntax.AST
open Llzk.FFConstraints.Basic
open Llzk.Language.Core.Semantics.Basic
open Llzk.SymExec.Basic


/- Bitify a constant FFTerm. It returns the list of bit terms (constants) and the
   corresponding formula (does not include variables, we return it just for uniformity) -/
def bitifyConst {c : ZKConfig}
  (_cfg : SymExecConfig c) (_md : CmdMD) (v : FF c)
  : List FFVar × List (FFTerm c) × FFFormula c :=
  let w : BitVec c.k := BitVec.ofNat c.k v.val
  let idxs := List.range c.k
  let bits := idxs.map (fun i => if (w.getLsbD i) then FFTerm.val 1 else FFTerm.val 0)
  let pows := idxs.map (fun i => FFTerm.val (2 ^ i))
  -- sum of bits[i] * 2^i
  let sum := List.foldl (fun acc (bit, pow) => FFTerm.add acc (FFTerm.mul bit pow))
                      (FFTerm.val 0)
                      (List.zip bits pows)
  let f := FFFormula.eq (FFTerm.val v) sum
  ([],bits, f)

/- Bitify a non-constant FFTerm. It returns the list of bit terms and the corresponding formula -/
def bitifyNonConst {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD) (e : FFTerm c)
  : List FFVar × List (FFTerm c) × FFFormula c :=
  let startId := cfg.nextId
  let idxs := List.range c.k
  let ffVars := idxs.map (fun i => FFVar.mk (startId + i) { src_info := md.src_info, orig_name := s!"bit{i}"})
  let bits := ffVars.map (fun v => FFTerm.var v)
  let pows := idxs.map (fun i => FFTerm.val (2 ^ i))
  -- sum of bits[i] * 2^i
  let sum := List.foldl (fun acc (bit, pow) => FFTerm.add acc (FFTerm.mul bit pow))
                      (FFTerm.val 0)
                      (List.zip bits pows)
  let sumF := FFFormula.eq e sum
  -- generate x*(1-x) = 0 for each bit to ensure it's boolean
  let f : FFFormula c:= bits.foldl
    (fun acc bit => FFFormula.and acc (FFFormula.eq (FFTerm.mul bit (FFTerm.sub (FFTerm.val 1) bit)) (FFTerm.val 0)))
    sumF
  (ffVars, bits, f)

def
 bitify {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD) (e : FFTerm c)
  : List FFVar × List (FFTerm c) × FFFormula c :=
  match e with
  | .val val => bitifyConst cfg md val
  | _ => bitifyNonConst cfg md e



end Llzk.SymExec.SymInstr
