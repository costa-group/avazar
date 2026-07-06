import Corellzk2smt.Language.Core.Syntax.AST
import Corellzk2smt.SymExec.Basic

namespace Corellzk2smt.SymExec

open Corellzk2smt.Language.Core.Syntax.AST
open Corellzk2smt.SymExec.Basic

/- Try to evaluate a simple expressions to a field value. This is used for constant propagation
   when possible.
-/
def tryEvalSimpleExprToFFValue {c : ZKConfig}
  (senv : SymEnv c)
  (s : SimpleExpr c)
  : Except String (FF c) :=
  match s with
  | .var id => match getVar senv id with
    | Except.ok rest =>
      match rest with
      | .simple (SimpleSymVal.const v) => Except.ok v
      | _ => Except.error s!"Variable '{id}' is not a constant"
    | Except.error err => Except.error err
  | .val v => Except.ok v


end Corellzk2smt.SymExec
