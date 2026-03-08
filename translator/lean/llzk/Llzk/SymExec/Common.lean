import Llzk.Language.Core.Syntax.AST
import Llzk.Language.Core.Syntax.Printer
import Llzk.FFConstraints.Basic
import Llzk.SymExec.Basic

namespace Llzk.SymExec.SymInstr

open Llzk.Language.Core.Syntax.AST
open Llzk.FFConstraints.Basic
open Llzk.Language.Core.Semantics.Basic
open Llzk.SymExec.Basic

/- Try to evaluate a a simple expressions to a field value. This is used for constant propagation
   when possible.
-/
def simpleExprToFF {c : ZKConfig}
  (senv : SymEnv c) (s : SimpleExpr c)
  : Except String (FF c) :=
  match s with
  | .var id => match getVar senv id with
    | Except.ok (SymValue.ffVar (SymFFVar.const v)) => Except.ok v
    | Except.ok (SymValue.ffVar (SymFFVar.var _)) => Except.error s!"Variable '{id}' is a symbolic"
    | Except.ok (SymValue.ffArray _) => Except.error s!"Variable '{id}' is an array"
    | Except.error err => Except.error err
  | .val v => Except.ok v

def simpleExprToSymFFVar {c : ZKConfig}
  (senv : SymEnv c) (s : SimpleExpr c)
  : Except String (SymFFVar c) :=
  match s with
  | .var id => match getVar senv id with
    | Except.ok (SymValue.ffVar v) => Except.ok v
    | Except.ok (SymValue.ffArray _) => Except.error s!"Variable '{id}' is an array"
    | Except.error err => Except.error err
  | .val v => Except.ok (SymFFVar.const v)

def simpleExprToTerm {c : ZKConfig}
  (senv : SymEnv c) (s : SimpleExpr c)
  : Except String (FFTerm c) :=
  match s with
  | .var id => match getVar senv id with
    | Except.ok (SymValue.ffVar (SymFFVar.const v)) => Except.ok (.val v)
    | Except.ok (SymValue.ffVar (SymFFVar.var v)) => Except.ok (FFTerm.var v)
    | Except.ok (SymValue.ffArray _) => Except.error s!"Variable '{id}' is an array"
    | Except.error err => Except.error err
  | .val v => Except.ok (.val v)

def symVarToTerm {c : ZKConfig} (v : SymFFVar c) : FFTerm c :=
  match v with
  | SymFFVar.const val => .val val
  | SymFFVar.var v => FFTerm.var v


end Llzk.SymExec.SymInstr
