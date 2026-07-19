import Corellzk2smt.Language.Core.Syntax.AST
import Corellzk2smt.SymExec.Basic
import Corellzk2smt.FFConstraints.Basic

namespace Corellzk2smt.SymExec

open Corellzk2smt.Language.Core.Syntax.AST
open Corellzk2smt.Language.Core.Semantics.Basic
open Corellzk2smt.SymExec.Basic
open Corellzk2smt.FFConstraints.Basic

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

/- The FF-constraint term a simple symbolic value denotes: a constant becomes a literal term,
   a symbolic variable becomes a reference to its constraint variable. Ignores any cached
   binary expansion -- that's a separate concern from what value the term computes to. -/
def simpleSymValToTerm {c : ZKConfig} (sv : SimpleSymVal c) : FFTerm c :=
  match sv with
  | .const v   => FFTerm.val v
  | .ffvar vbr => FFTerm.var vbr.var

/- Resolve a simple expression against a symbolic environment, giving back its full symbolic
   representation (constant or constraint variable) -- unlike `tryEvalSimpleExprToFFValue`,
   this never fails just because the value isn't a compile-time constant. -/
def resolveSimpleExpr {c : ZKConfig}
    (senv : SymEnv c)
    (s : SimpleExpr c)
    : Except String (SimpleSymVal c) :=
  match s with
  | .var id => match getVar senv id with
    | Except.ok (.simple sv) => Except.ok sv
    | Except.ok (.array _) => Except.error s!"Variable '{id}' is an array, expected scalar"
    | Except.error err => Except.error err
  | .val v => Except.ok (.const v)

/-- Resolve a simple expression against a symbolic environment, giving back its full symbolic
    value -- unlike `resolveSimpleExpr`, this also accepts (and passes through) a whole array,
    for function-call arguments (`seFuncCall`) where a parameter can be array-typed. Mirrors
    `Semantics.Basic.evalSimpleExprToValue` exactly. -/
def resolveSimpleExprToSymValue {c : ZKConfig}
    (senv : SymEnv c)
    (s : SimpleExpr c)
    : Except String (SymValue c) :=
  match s with
  | .var id => getVar senv id
  | .val v => Except.ok (.simple (.const v))

/-- `resolveSimpleExprToSymValue`, for a whole argument list. -/
def resolveSimpleExprsToSymValue {c : ZKConfig}
    (senv : SymEnv c)
    (l : List (SimpleExpr c))
    : Except String (List (SymValue c)) :=
  l.mapM (resolveSimpleExprToSymValue senv)

/-- The macro-call argument a simple symbolic value denotes: a constant becomes a literal
    `Const`, a symbolic variable becomes a reference to its constraint variable -- the
    `MacroCallParam` mirror of `simpleSymValToTerm`. -/
def simpleSymValToMacroCallParam {c : ZKConfig} (sv : SimpleSymVal c) : MacroCallParam c :=
  match sv with
  | .const v   => MacroCallParam.const (Const.ffc v)
  | .ffvar vbr => MacroCallParam.var (Var.ffv vbr.var)

/-- Flatten a single (possibly array-shaped) symbolic value into its per-element macro-call
    arguments, in order -- purely a function of the value's own runtime shape (never fails,
    unlike `flattenArgVal`, which additionally checks the value's shape against a *declared*
    parameter type). `flattenArgVal`'s success case always agrees with this (see
    `flattenArgVal_eq_flattenSymValueParams` in `SymExec/FuncCallCorrectness.lean`). -/
def flattenSymValueParams {c : ZKConfig} (v : SymValue c) : List (MacroCallParam c) :=
  match v with
  | .simple sv => [simpleSymValToMacroCallParam sv]
  | .array arr => arr.toList.map simpleSymValToMacroCallParam

/-- `flattenSymValueParams`, for a whole value list -- each value's own flattened block,
    concatenated in order. -/
def flattenSymValuesParams {c : ZKConfig} (vs : List (SymValue c)) : List (MacroCallParam c) :=
  (vs.map flattenSymValueParams).flatten

/-- Concrete mirror of `flattenSymValueParams`: flatten a single (possibly array-shaped)
    concrete value into its per-element `.const` macro-call arguments, in order -- the
    constant-argument encoding `H_specCorrect`-style hypotheses use to phrase a callee's macro
    call over concrete `argVals`/`retVals`/aux witnesses. -/
def flattenValueParams {c : ZKConfig} (v : Value c) : List (MacroCallParam c) :=
  match v with
  | .scalar x => [MacroCallParam.const (Const.ffc x)]
  | .array arr => arr.toList.map (fun x => MacroCallParam.const (Const.ffc x))

/-- `flattenValueParams`, for a whole value list. -/
def flattenValuesParams {c : ZKConfig} (vs : List (Value c)) : List (MacroCallParam c) :=
  (vs.map flattenValueParams).flatten

/-- Flatten a single (possibly array-shaped) concrete value down to its raw `FF c` elements
    (no `MacroCallParam`/`Const` wrapping) -- the assignment-construction-side counterpart of
    `flattenValueParams`, used to read a `retVals : List (Value c)` back as one flat `FF c` list
    indexed by fresh constraint-variable offset. -/
def flattenValueToFF {c : ZKConfig} (v : Value c) : List (FF c) :=
  match v with
  | .scalar x => [x]
  | .array arr => arr.toList

/-- `flattenValueToFF`, for a whole value list. -/
def flattenValuesToFF {c : ZKConfig} (vs : List (Value c)) : List (FF c) :=
  (vs.map flattenValueToFF).flatten

end Corellzk2smt.SymExec
