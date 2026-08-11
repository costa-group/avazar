import Corellzk2smt.Basic
import Corellzk2smt.Config
import Corellzk2smt.SymExec.Basic
import Corellzk2smt.SymExec.Common
import Corellzk2smt.FFConstraints.Basic
import Corellzk2smt.Language.Core.Syntax.AST
import Corellzk2smt.Language.Core.Semantics.Basic
import Corellzk2smt.SymExec.BinaryExpansion

/-!
Symbolic execution of the bitwise operators (`& | ^ << >>` and unary bitwise negation `~`),
dispatched to from `seEvalExpr` (`SymExec/Assignment.lean`). Each `seExprXXX` is currently a
permanent `"Not implemented yet"` stub -- `seEvalAssignmentConst` (`Assignment.lean`) already
handles the case where both operands fully constant-fold; these are for the general,
not-necessarily-constant case, still to be built (likely via the binary-expansion machinery in
`SymExec/Correctness/BinaryExpansionCorrectness.lean`, once that's implemented for real).
-/

namespace Corellzk2smt.SymExec.BigStep

open Corellzk2smt.Config (GlobalConfig)
open Corellzk2smt.Language.Core.Syntax.AST
open Corellzk2smt.Language.Core.Semantics.Basic
open Corellzk2smt.SymExec.Basic
open Corellzk2smt.FFConstraints.Basic
open Corellzk2smt.SymExec.BinaryExpansion

def seExprBitwiseAND {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (e1 e2 : SimpleExpr c)
  : Except String (ExprSpec c) :=
  Except.error "Not implemented yet"
  -- match fetch_bin_rep md gconf sconf symEnv e1 with
  -- | Except.error msg => Except.error msg
  -- | Except.ok (senv1, bits1, nextId1, f1) =>
  --   let sconf' := { sconf with nextVarId := nextId1 }
  --   match fetch_bin_rep md gconf sconf' senv1 e2 with
  --   | Except.error msg => Except.error msg
  --   | Except.ok (senv2, bits2, nextId2, f2) =>
  --     let k := Nat.min bits1.length bits2.length
  --     let bits := List.range k |>.map (fun i => FFTerm.and (bits1.get! i) (bits2.get! i))
  --     let f := FFFormula.and f1 f2
  --     Except.ok { symEnv := senv2, nextVarId := nextId2, bits := bits, formula := f }


def seExprBitwiseOR {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (e1 e2 : SimpleExpr c)
  : Except String (ExprSpec c) :=
  Except.error "Not implemented yet"

def seExprBitwiseXOR {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (e1 e2 : SimpleExpr c)
  : Except String (ExprSpec c) :=
  Except.error "Not implemented yet"

def seExprBitwiseNOT {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (e1 : SimpleExpr c)
  : Except String (ExprSpec c) :=
  Except.error "Not implemented yet"

def seExprBitwiseSHL {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (e1 e2 : SimpleExpr c)
  : Except String (ExprSpec c) :=
  Except.error "Not implemented yet"

def seExprBitwiseSHR {c : ZKConfig}
    (md : CmdMD)
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (e1 e2 : SimpleExpr c)
  : Except String (ExprSpec c) :=
  Except.error "Not implemented yet"

end Corellzk2smt.SymExec.BigStep
