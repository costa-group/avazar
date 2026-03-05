import Llzk.Basic
import Llzk.Language.Core.Syntax.AST
import Std.Data.TreeMap.Basic

import Mathlib.Tactic.NormNum.LegendreSymbol -- needed for div in FF to compile

namespace Llzk.Language.Core.Semantics.Basic

open Llzk.Language.Core.Syntax.AST


/- This is a structure that will be passed around in the interpreter. We can encapsulate
   various things here. Separating it from the state makes things simpler. we can change
   the configuration without affecting the state, and we can also add more things to
   the configuration later without substantial changes to the code
    -/
structure SemConfig (c : ZKConfig) where
  oracle : VarID → (FF c)
  deriving Inhabited

-- Manually define how to print SemConfig
instance {c : ZKConfig} : Repr (SemConfig c) where
  reprPrec _ _ := s!"SemConfig \{ oracle := <function> }"


/- A type for arrays -/

abbrev FFArray (c : ZKConfig) := Array (FF c)

inductive Value (c : ZKConfig) where
  | scalar (v : FF c)
  | array (arr : FFArray c)
  deriving Repr, Inhabited

/- Environment: A mapping from program variables to Value -/
abbrev Env (c : ZKConfig) := Std.TreeMap VarID (Value c)

/- Empty environment -/
def emptyEnv (c : ZKConfig) : Env c := Std.TreeMap.empty

/- A state is a structure holding the environments. Maybe we add more information
   later -/
structure State (c : ZKConfig) where
  vars : Env c
  deriving Repr, Inhabited

/- The next few functions provide an abstraction of the different operations
   of an environment, so we can change the implementation later if needed
-/

/- Retrieve a value from an environment. It fails if the variable
   is not in the environment -/
def getVar {c : ZKConfig} (env : Env c) (id : VarID) : Except String (Value c) :=
  match env.get? id with
  | some v => Except.ok v
  | none   => Except.error s!"Variable '{id}' not found"

/- Set the value of a variable in an environment. It updates
   the value if it exists already. It never fails -/
def setVar {c : ZKConfig} (env : Env c) (id : VarID) (v : Value c) : Env c :=
  env.insert id v

/- Set the values of multiple variables in an environment.
-/
def setVars {c : ZKConfig}
    (env : Env c) (ids : List VarID) (vs : List (Value c)) : Except String (Env c) :=
  match ids, vs with
  | [], [] => Except.ok env
  | id :: ids, v :: vs => do
      let env' ← setVars (setVar env id v) ids vs
      Except.ok env'
  | _, _ => Except.error "Mismatched lengths of ids and values"


/- Evaluate a simple expressions (a variable or a field value) to a field value,
   by looking it up in the state. It fails if the variable is not found or if
   the variable is an array.
-/
def evalSimpleExprToFF {c : ZKConfig} (st : State c) (s : SimpleExpr c) : Except String (FF c) :=
  match s with
  | .var id => match getVar st.vars id with
    | Except.ok (Value.scalar v) => Except.ok v
    | Except.ok (Value.array _) => Except.error s!"Variable '{id}' is an array, expected scalar"
    | Except.error err => Except.error err
  | .val v => Except.ok v

/- A function for evaluating constant simple expressions -/
def evalConstSimpleExpr {c : ZKConfig}
    (st : State c) (s : SimpleExpr c) : Except String (FF c) := do
   -- Clear variable environment to ensure const-ness
  let st' := { st with vars := emptyEnv c}
  evalSimpleExprToFF st' s

/- -/
def evalSimpleExprToValue {c : ZKConfig}
    (st : State c) (s : SimpleExpr c) : Except String (Value c) := do
  match s with
  | .var id => getVar st.vars id
  | .val v => Except.ok (Value.scalar v)

def evalSimpleExprsToValue {c : ZKConfig}
    (st : State c) (l : List (SimpleExpr c)) : Except String (List (Value c)) := do
  l.mapM (evalSimpleExprToValue st)


def ensureCorrectType {c : ZKConfig} (v : Value c) (type : VarType) : Except String Unit :=
  match type, v with
  | .ff, Value.scalar _ => Except.ok ()
  | .array n, Value.array a =>
    if a.size = n then
      Except.ok ()
    else
      Except.error s!"Array size mismatch: expected {n}, got {a.size}"
  | _, _ => Except.error "Type mismatch"

def bindInParams {c : ZKConfig}
    (env : Env c) (params : List Param) (args : List (Value c)) : Except String (Env c) := do
  match params, args with
  | [], [] => Except.ok env
  | p :: ps, v :: vs =>
      ensureCorrectType v p.type
      bindInParams (setVar env p.name v) ps vs
  | _, _ => Except.error "Mismatched lengths of parameters and arguments"

def bindOutParams {c : ZKConfig}
    (env : Env c) (rets : List Param) : Except String (List (Value c)) := do
  match rets with
  | [] => Except.ok []
  | p :: rets' =>
      let v ← getVar env p.name
      ensureCorrectType v p.type
      let vs ← bindOutParams env rets'
      Except.ok (v :: vs)

/- Functions for evaluating each expression in the language
   on concrete values
-/


/- Arithmetic -/
def evalId {c : ZKConfig} (v : FF c) : FF c :=
  v

def evalNeg {c : ZKConfig} (v : FF c) : FF c :=
  -v

def evalAdd {c : ZKConfig} (v1 v2 : FF c) : FF c :=
  v1 + v2

def evalSub {c : ZKConfig} (v1 v2 : FF c) : FF c :=
  v1 - v2

def evalMul {c : ZKConfig} (v1 v2 : FF c) : FF c :=
  v1 * v2

def evalDiv {c : ZKConfig} (v1 v2 : FF c) : FF c :=
  v1 / v2

/- Bitwise -/
def evalShl {c : ZKConfig} (v1 v2 : FF c) : FF c :=
  let w : BitVec c.k := BitVec.ofNat c.k v1.val
  let shiftedW := w <<< v2.val
  let finalVal := (shiftedW.toNat : FF c)
  finalVal

def evalShr {c : ZKConfig} (v1 v2 : FF c) : FF c :=
  let w : BitVec c.k := BitVec.ofNat c.k v1.val
  let shiftedW := w >>> v2.val
  let finalVal := (shiftedW.toNat : FF c)
  finalVal

def evalAnd {c : ZKConfig} (v1 v2 : FF c) : FF c :=
  let w1 : BitVec c.k := BitVec.ofNat c.k v1.val
  let w2 : BitVec c.k := BitVec.ofNat c.k v2.val
  let andW := w1 &&& w2
  let finalVal := (andW.toNat : FF c)
  finalVal

def evalOr {c : ZKConfig} (v1 v2 : FF c) : FF c :=
  let w1 : BitVec c.k := BitVec.ofNat c.k v1.val
  let w2 : BitVec c.k := BitVec.ofNat c.k v2.val
  let orW := w1 ||| w2
  let finalVal := (orW.toNat : FF c)
  finalVal

def evalXor {c : ZKConfig} (v1 v2 : FF c) : FF c :=
  let w1 : BitVec c.k := BitVec.ofNat c.k v1.val
  let w2 : BitVec c.k := BitVec.ofNat c.k v2.val
  let xorW := w1 ^^^ w2
  let finalVal := (xorW.toNat : FF c)
  finalVal

def evalNot {c : ZKConfig} (v : FF c) : FF c :=
  let w : BitVec c.k := BitVec.ofNat c.k v.val
  let notW := BitVec.not w
  let finalVal := (notW.toNat : FF c)
  finalVal

/- Boolean -/
def evalTrue {c : ZKConfig} : FF c :=
  1

def evalFalse {c : ZKConfig} : FF c :=
  0

def evalEq {c : ZKConfig} (v1 v2 : FF c) : FF c :=
  if v1 = v2 then 1 else 0

def evalNeq {c : ZKConfig} (v1 v2 : FF c) : FF c :=
  if v1 ≠ v2 then 1 else 0

/-
https://project-llzk.github.io/llzk-lib/main/dialects.html

signed_int(f) = f    if 0 <= f < p/2 + 1
    "p/2" here is unsigned integer division rounding towards 0
signed_int(f) = f-p  if p/2 + 1 <= f < p
-/
def toSigned {c : ZKConfig} (x : FF c) : Int :=
  if x.val < c.midpoint then
    (x.val : Int)        -- 0, 1, ... midpoint-1
  else
    (x.val : Int) - c.p  -- -1 (p-1), -2 (p-2), ... -midpoint (p-midpoint)

def evalLt {c : ZKConfig} (v1 v2 : FF c) : FF c :=
  if toSigned v1 < toSigned v2 then 1 else 0

def evalGt {c : ZKConfig} (v1 v2 : FF c) : FF c :=
  if toSigned v1 > toSigned v2 then 1 else 0

def evalLe {c : ZKConfig} (v1 v2 : FF c) : FF c :=
  if toSigned v1 ≤ toSigned v2 then 1 else 0

def evalGe {c : ZKConfig} (v1 v2 : FF c) : FF c :=
  if toSigned v1 ≥ toSigned v2 then 1 else 0

def evalBor {c : ZKConfig} (v1 v2 : FF c) : FF c :=
  if v1 = 0 && v2 = 0 then 0 else 1

def evalBand {c : ZKConfig} (v1 v2 : FF c) : FF c :=
  if v1 ≠ 0 && v2 ≠ 0 then 1 else 0

def evalBneg {c : ZKConfig} (v : FF c) : FF c :=
  if v = 0 then 1 else 0



/- Functions for evaluating expressions -/
def evalExpr {c : ZKConfig} (st : State c) (e : Expr c) : Except String (FF c) := do
  match e with
  | .bop op s1 s2 => do
      let val1 ← evalSimpleExprToFF st s1
      let val2 ← evalSimpleExprToFF st s2
      match op with
      | .add => Except.ok (evalAdd val1 val2)
      | .sub => Except.ok (evalSub val1 val2)
      | .mul => Except.ok (evalMul val1 val2)
      | .div => Except.ok (evalDiv val1 val2)
      | .shl => Except.ok (evalShl val1 val2)
      | .shr => Except.ok (evalShr val1 val2)
      | .and => Except.ok (evalAnd val1 val2)
      | .or  => Except.ok (evalOr val1 val2)
      | .xor => Except.ok (evalXor val1 val2)
      | .bor => Except.ok (evalBor val1 val2)
      | .band => Except.ok (evalBand val1 val2)
      | .eq  => Except.ok (evalEq val1 val2)
      | .neq => Except.ok (evalNeq val1 val2)
      | .lt  => Except.ok (evalLt val1 val2)
      | .gt  => Except.ok (evalGt val1 val2)
      | .le  => Except.ok (evalLe val1 val2)
      | .ge  => Except.ok (evalGe val1 val2)
  | .uop op s => do
      let val ← evalSimpleExprToFF st s
      match op with
      | .neg => Except.ok (evalNeg val)
      | .not => Except.ok (evalNot val)
      | .bneg => Except.ok (evalBneg val)
  | .id s => do
      let val ← evalSimpleExprToFF st s
      Except.ok (evalId val)

/- A function for evaluating constant expressions -/
def evalConstExpr {c : ZKConfig} (st : State c) (e : Expr c) : Except String (FF c) := do
   -- Clear variable environment to ensure const-ness
  let st' := { st with vars := emptyEnv c}
  evalExpr st' e

/- A function for evaluating conditions -/
def evalCond {c : ZKConfig} (st : State c) (cond : Cond c) : Except String Bool := do
  match cond with
  | .eq s1 s2 => do
    let val1 ← evalSimpleExprToFF st s1
    let val2 ← evalSimpleExprToFF st s2
    if val1 = val2 then
      Except.ok true
    else
      Except.ok false

/- Functions for executing simple commands, like assignment, array operations, etc.
   These functions take a state and a command, and return the new state after executing
   the command. They can fail if there are errors, like variable not found, index
   out of bounds, etc.
-/

/- skip does nothing -/
def evalSkip {c : ZKConfig}
    (st : State c) : Except String (State c) :=
  Except.ok st

/- id := e -/
def evalAssign {c : ZKConfig}
    (st : State c) (id : VarID) (e : Expr c) : Except String (State c) := do
  let val ← evalExpr st e
  let newEnv := setVar st.vars id (Value.scalar val)
  Except.ok { st with vars := newEnv }

/- id := new Array(size) -/
def evalNewArray {c : ZKConfig}
    (st : State c) (id : VarID) (size : SimpleExpr c) : Except String (State c) := do
  let sizeVal ← evalConstSimpleExpr st size
  let arr := (List.replicate sizeVal.val (0 : FF c)).toArray -- initialize with zeros
  let newAEnv := setVar st.vars id (Value.array arr)
  Except.ok { st with vars := newAEnv }

def evalReadArray {c : ZKConfig}
    (st : State c) (out a : VarID) (index : SimpleExpr c) : Except String (State c) := do
  let indexVal ← evalSimpleExprToFF st index
  match getVar st.vars a with
  | Except.ok (Value.array arr) => do
      if h : indexVal.val < arr.size then
        let val := arr[indexVal.val]'h
        let newEnv := setVar st.vars out (Value.scalar val)
        Except.ok { st with vars := newEnv }
      else
        Except.error s!"Index out of bounds: {indexVal.val} >= {arr.size}"
  | _ => Except.error s!"Variable '{a}' is not an array"

def evalWriteArray {c : ZKConfig}
    (st : State c) (a : VarID) (index value : SimpleExpr c) : Except String (State c) := do
  let indexVal ← evalSimpleExprToFF st index
  let valueVal ← evalSimpleExprToFF st value
  match getVar st.vars a with
  | Except.ok (Value.array arr) => do
      if h : indexVal.val < arr.size then
        let newArr := Array.set arr indexVal.val valueVal h
        let newAEnv := setVar st.vars a (Value.array newArr)
        Except.ok { st with vars := newAEnv }
      else
        Except.error s!"Index out of bounds: {indexVal.val} >= {arr.size}"
  | _ => Except.error s!"Variable '{a}' is not an array"

def evalCopyArray {c : ZKConfig}
    (st : State c) (out a : VarID) : Except String (State c) := do
   match getVar st.vars a with
   | Except.ok (Value.array arr) => do
       let new_arr := arr
       let newAEnv := setVar st.vars out (Value.array new_arr)
       Except.ok { st with vars := newAEnv }
   | _ => Except.error s!"Variable '{a}' is not an array"


end Llzk.Language.Core.Semantics.Basic
