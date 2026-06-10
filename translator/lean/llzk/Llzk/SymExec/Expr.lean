import Llzk.Language.Core.Syntax.AST
import Llzk.Language.Core.Syntax.Printer
import Llzk.FFConstraints.Basic
import Llzk.SymExec.Basic
import Llzk.SymExec.Common
import Llzk.SymExec.ArithExpr
import Llzk.SymExec.BoolExpr
import Llzk.SymExec.BitwiseExpr

namespace Llzk.SymExec.SymInstr

open Llzk.Language.Core.Syntax.AST
open Llzk.FFConstraints.Basic
open Llzk.Language.Core.Semantics.Basic
open Llzk.SymExec.Basic
  -- increment the nextId in the config for the next variable

def sEvalExpr {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD) (symEnv : SymEnv c) (e : Expr c) (id : VarID)
  : Except String (ExprSpec c) := do
 match e with
  | .bop op s1 s2 =>
    match op with
    | .add => sEvalExprAdd cfg md symEnv s1 s2 id -- arith
    | .sub => sEvalExprSub cfg md symEnv s1 s2 id -- arith
    | .mul => sEvalExprMul cfg md symEnv s1 s2 id -- arith
    | .div => sEvalExprDiv cfg md symEnv s1 s2 id -- arith
    | .bor => sEvalBor cfg md symEnv s1 s2 id -- bool
    | .band => sEvalBAnd cfg md symEnv s1 s2 id -- bool
    | .eq => sEvalEq cfg md symEnv s1 s2 id -- bool
    | .neq => sEvalNeq cfg md symEnv s1 s2 id -- bool
    -- Unsigned Comparison
    -- | .lt => sEvalLtUnSigned cfg md symEnv s1 s2 id -- bool
    -- | .le => sEvalLeUnSigned cfg md symEnv s1 s2 id -- bool
    -- | .gt => sEvalGtUnSigned cfg md symEnv s1 s2 id -- bool
    -- | .ge => sEvalGeUnSigned cfg md symEnv s1 s2 id -- bool
    -- Signed Comparison
    | .lt => sEvalLtSigned cfg md symEnv s1 s2 id -- bool
    | .le => sEvalLeSigned cfg md symEnv s1 s2 id -- bool
    | .gt => sEvalGtSigned cfg md symEnv s1 s2 id -- bool
    | .ge => sEvalGeSigned cfg md symEnv s1 s2 id -- bool
    -- bitwise
    | .and => sEvalBitwiseAND cfg md symEnv s1 s2 id -- bitwise
    | .or => sEvalBitwiseOR cfg md symEnv s1 s2 id -- bitwise
    | .xor => sEvalBitwiseXOR cfg md symEnv s1 s2 id -- bitwise
    | .shl => sEvalBitwiseSHL cfg md symEnv s1 s2 id -- bitwise
    | .shr => sEvalBitwiseSHR cfg md symEnv s1 s2 id -- bitwise
  | .uop op s =>
    match op with
     | .neg => sEvalExprNeg cfg md symEnv s id -- arith
     | .bneg => sEvalBNeg cfg md symEnv s id -- bool
     | .not => sEvalBitwiseNOT cfg md symEnv s id -- bitwise
  | .id _ =>
      Except.error s!"Evaluation of identifier is handled somewhere else, should not reach here"


end Llzk.SymExec.SymInstr
