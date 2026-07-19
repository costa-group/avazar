import Corellzk2smt.Basic
import Corellzk2smt.Language.Core.Syntax.AST

/- Collects every variable name that is ever an assignment target within a function's body.

   This is used to build a fully-defined initial environment for a function call: every
   variable is defaulted to 0 before execution starts, so a variable assigned along one branch
   of a conditional but not the other is still always defined afterwards (rather than being
   "maybe defined", which would force environments to have different domains along different
   branches of the same function). See `evalFunCall` in `Semantics/BigStep.lean`.

   The language isn't strongly typed, so no attempt is made here to track whether a variable
   is eventually used as an array or a finite-field value -- everything defaults to a scalar
   0, and `new_array`/`copy_array` overwrite that default the first time the variable is
   actually used as an array.
-/

namespace Corellzk2smt.Language.Core.Analysis.DefinedVars

open Corellzk2smt.Language.Core.Syntax.AST

mutual

def definedVarsCom {c : ZKConfig} (vars : VarIDSet) (cmd : Com c) : VarIDSet :=
  match cmd with
  | .assign id _        => vars.insert id
  | .if_stmt _ tb eb     => definedVarsCmds (definedVarsCmds vars tb) eb
  | .loop_exp _ body     => definedVarsCmds vars body
  | .loop _ body         => definedVarsCmds vars body
  | .new_array id _      => vars.insert id
  | .read_array id _ _   => vars.insert id
  | .write_array _ _ _   => vars -- mutates an existing array, doesn't define a new variable
  | .copy_array dst _    => vars.insert dst
  | .func_call outs _ _  => outs.foldl (fun acc id => acc.insert id) vars

def definedVarsCmds {c : ZKConfig} (vars : VarIDSet) (cmds : List (ComWithMD c)) : VarIDSet :=
  match cmds with
  | [] => vars
  | i :: rest =>
    match i with
    | .mk _ cmd => definedVarsCmds (definedVarsCom vars cmd) rest

end

/-- Every variable a function ever assigns, including its parameters. -/
def definedVarsOfFunc {c : ZKConfig} (f : Func c) : VarIDSet :=
  match f with
  | .mk _name params _rets body =>
    let initVars := params.foldl (fun acc p => acc.insert p.name) emptyVarIDSet
    definedVarsCmds initVars body

end Corellzk2smt.Language.Core.Analysis.DefinedVars
