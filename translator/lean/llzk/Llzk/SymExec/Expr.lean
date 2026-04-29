
import Llzk.Language.Core.Syntax.AST
import Llzk.Language.Core.Syntax.Printer
import Llzk.FFConstraints.Basic
import Llzk.SymExec.Basic
import Llzk.SymExec.Common
import Llzk.SymExec.ArithExpr
import Llzk.SymExec.BoolExpr
import Llzk.SymExec.BitWiseExpr

namespace Llzk.SymExec.SymInstr

open Llzk.Language.Core.Syntax.AST
open Llzk.FFConstraints.Basic
open Llzk.Language.Core.Semantics.Basic
open Llzk.SymExec.Basic

def sEvalExpr {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD) (symEnv : SymEnv c) (e : Expr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  match e with
  | .bop op s1 s2 =>
    match op with
    | .add => sEvalExprAdd cfg md symEnv s1 s2 outFFVar -- arith
    | .sub => sEvalExprSub cfg md symEnv s1 s2 outFFVar -- arith
    | .mul => sEvalExprMul cfg md symEnv s1 s2 outFFVar -- arith
    | .div => sEvalExprDiv cfg md symEnv s1 s2 outFFVar -- arith
    | .bor => sEvalBor cfg md symEnv s1 s2 outFFVar -- bool
    | .band => sEvalBAnd cfg md symEnv s1 s2 outFFVar -- bool
    | .eq => sEvalEq cfg md symEnv s1 s2 outFFVar -- bool
    | .neq => sEvalNeq cfg md symEnv s1 s2 outFFVar -- bool
    -- Unsigned
    -- | .lt => sEvalLtUnSigned cfg md symEnv s1 s2 outFFVar -- bool
    -- | .le => sEvalLeUnSigned cfg md symEnv s1 s2 outFFVar -- bool
    -- | .gt => sEvalGtUnSigned cfg md symEnv s1 s2 outFFVar -- bool
    -- | .ge => sEvalGeUnSigned cfg md symEnv s1 s2 outFFVar -- bool
    -- Signed
    | .lt => sEvalLtSigned cfg md symEnv s1 s2 outFFVar -- bool
    | .le => sEvalLeSigned cfg md symEnv s1 s2 outFFVar -- bool
    | .gt => sEvalGtSigned cfg md symEnv s1 s2 outFFVar -- bool
    | .ge => sEvalGeSigned cfg md symEnv s1 s2 outFFVar -- bool
    | .and => sEvalBitWiseAND cfg md symEnv s1 s2 outFFVar -- bitwise
    | .or => sEvalBitWiseOR cfg md symEnv s1 s2 outFFVar -- bitwise
    | .xor => sEvalBitWiseXOR cfg md symEnv s1 s2 outFFVar -- bitwise
    | .shl => sEvalBitWiseSHL cfg md symEnv s1 s2 outFFVar -- bitwise
    | .shr => sEvalBitWiseSHR cfg md symEnv s1 s2 outFFVar -- bitwise
  | .uop op s =>
    match op with
     | .neg => sEvalExprNeg cfg md symEnv s outFFVar
     | .bneg => sEvalBNeg cfg md symEnv s outFFVar
     | .not => sEvalBitWiseNOT cfg md symEnv s outFFVar
  | .id _ =>
      Except.error s!"Evaluation of identifier is handled somewhere else, should not reach here"


end Llzk.SymExec.SymInstr
