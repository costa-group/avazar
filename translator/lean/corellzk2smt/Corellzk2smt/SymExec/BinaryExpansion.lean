import Corellzk2smt.Config
import Corellzk2smt.SymExec.Basic
import Corellzk2smt.FFConstraints.Basic

namespace Corellzk2smt.SymExec.BinaryExpansion

open Corellzk2smt.Config
open Corellzk2smt.SymExec.Basic
open Corellzk2smt.FFConstraints.Basic

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


end Corellzk2smt.SymExec.BinaryExpansion
