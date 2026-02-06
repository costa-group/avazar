import Llzk.Basic
import Llzk.Language.Core.Syntax
import Std.Data.TreeMap.Basic

import Mathlib.Tactic.NormNum.LegendreSymbol -- needed for div in FF to compile

namespace Llzk.Language.Core.Semantics

open Llzk.Language.Core

/- Environment: A mapping from program variables to FF values -/
abbrev Env (c : ZKConfig) := Std.TreeMap ProgVarID (FF c)

/- The next few functions provide an abstraction of the different operations
   of an environment, so we can change the implementation later if needed
-/

/- Create an empty environment -/
def emptyEnv (c : ZKConfig) : Env c := Std.TreeMap.empty

/- Retrive a value from an environemnt. It fails if the variable
   is not in the environemt -/
def get_var {c : ZKConfig} (env : Env c) (id : ProgVarID) : Except String (FF c) :=
  match env.get? id with
  | some v => Except.ok v
  | none   => Except.error s!"Variable '{id}' not found"

/- Set the value of a variable in an environemnt. It updates
   the value if it exists already. It never fails -/
def set_var {c : ZKConfig} (env : Env c) (id : ProgVarID) (v : FF c) : Env c :=
  env.insert id v

/- Update the value of a variable in an environemnt. It fails if the variable
   is not in the environemt -/
def update_var {c : ZKConfig} (env : Env c) (id : ProgVarID) (v : FF c) : Except String (Env c) :=
  if env.contains id then
    Except.ok (env.insert id v)
  else
    Except.error s!"Variable '{id}' not found"

/- Evaluate a simple expressions (a variable or a field value) to a field value -/
def eval_simple {c : ZKConfig} (env : Env c) (se : SimpleExpr c) : Except String (FF c) :=
  match se with
  | Sum.inr v  => Except.ok v -- value
  | Sum.inl id => get_var env id -- variable

/- An oracle can be used to provide intial values for program variables -/
abbrev Oracle (c : ZKConfig) := ProgVarID → (FF c)

/- The next few functions provide a semantics for simple (non-branching) instructions
   of the different commands in the core language
-/


/- Execute skip -/
def exec_skip {c : ZKConfig}
    (env : Env c) : Except String (Env c) :=
  return env

/- Execute add -/
def exec_add {c : ZKConfig}
    (env : Env c) (out : ProgVarID) (a1 a2 : SimpleExpr c) : Except String (Env c) := do
  let v1 ← eval_simple env a1
  let v2 ← eval_simple env a2
  update_var env out (v1 + v2)

/- Execute sub -/
def exec_sub
 {c : ZKConfig}
    (env : Env c) (out : ProgVarID) (a1 a2 : SimpleExpr c) : Except String (Env c) := do
  let v1 ← eval_simple env a1
  let v2 ← eval_simple env a2
  update_var env out (v1 - v2)

/- Execute mul -/
def exec_mul {c : ZKConfig}
    (env : Env c) (out : ProgVarID) (a1 a2 : SimpleExpr c) : Except String (Env c) := do
  let v1 ← eval_simple env a1
  let v2 ← eval_simple env a2
  update_var env out (v1 * v2)

/- Execute div -/
def exec_div {c : ZKConfig}
    (env : Env c) (out : ProgVarID) (a1 a2 : SimpleExpr c) : Except String (Env c) := do
  let v1 ← eval_simple env a1
  let v2 ← eval_simple env a2
  update_var env out (v1 / v2)

   -- div by zero handled in FF

/- Execute shift left -/
def exec_shl {c : ZKConfig}
    (env : Env c) (out : ProgVarID) (a : SimpleExpr c) (bits : ℕ) : Except String (Env c) := do
  let v ← eval_simple env a
  let w : BitVec c.k := BitVec.ofNat c.k v.val
  let shiftedW := w <<< bits
  let finalVal := (shiftedW.toNat : FF c)
  update_var env out finalVal

/- Execute assign -/
def exec_assign {c : ZKConfig}
    (env : Env c) (out : ProgVarID) (a : SimpleExpr c) : Except String (Env c) := do
  let val ← eval_simple env a
  update_var env out val

end Llzk.Language.Core.Semantics
