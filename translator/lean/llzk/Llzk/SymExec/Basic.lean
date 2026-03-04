import Llzk.Basic
import Llzk.Language.Core.Syntax.AST
import Llzk.FFConstraints.Basic
import Llzk.Language.Core.Semantics.Basic
import Std.Data.TreeMap.Basic

namespace Llzk.SymExec.Basic

open Llzk.Language.Core.Syntax.AST
open Llzk.FFConstraints.Basic
open Llzk.Language.Core.Semantics.Basic

/- This is a structure that will be passed around in the symbolic interpreter. We can
   encapsulate various things here. Separating it from the symbolic state makes things
   simpler.

   We can change the configuration without affecting the symbolic state, and we can
   also add more things to the configuration later without substantial changes
   to the code
-/
structure SymExecConfig (c : ZKConfig) where
  nextId : Nat := 0
  deriving Inhabited

/- A symbolic variable can either be a concrete value of a finite
   field or a field constraint variable -/
inductive SymFFVar (c : ZKConfig) where
  | var : FFVar → SymFFVar c
  | const : FF c → SymFFVar c
  deriving Repr, BEq, Inhabited

/- A symbolic array is an array of symbolic finite field variables -/
abbrev SymFFArray (c : ZKConfig) := Array (SymFFVar c)

/- A symbolic value can either be a SymFFVar or a SymFFArray -/
inductive SymValue (c : ZKConfig) where
  | ffVar : SymFFVar c → SymValue c
  | ffArray : SymFFArray c → SymValue c
  deriving Repr, BEq, Inhabited

/- Environment: A mapping from program variables to Value -/
abbrev SymEnv (c : ZKConfig) := Std.TreeMap VarID (SymValue c)

def emptySymEnv {c : ZKConfig} : SymEnv c := Std.TreeMap.empty



/- Retrieve a value from a symbolic environment. It fails if the variable
   is not in the environment -/
def getVar {c : ZKConfig} (env : SymEnv c) (id : VarID) : Except String (SymValue c) :=
  match env.get? id with
  | some v => Except.ok v
  | none   => Except.error s!"Variable '{id}' not found"

/- Set the value of a variable in a symbolic environment. It updates
   the value if it exists already. It never fails -/
def setVar {c : ZKConfig} (env : SymEnv c) (id : VarID) (v : SymValue c) : SymEnv c :=
  env.insert id v


/- A specification for a sequence of commands. It is a formula describing the
   relationship between the input and output symbolic environments.

   This is be extended later with more information to facilitate proofs.
    -/
structure CmdsSpec (c : ZKConfig) where
  inSymEnv : SymEnv c := emptySymEnv
  outSymEnv : SymEnv c := emptySymEnv
  f : FFFormula c := FFFormula.false
  nextId : Nat := 0
  newFFVars : FFVarSet := emptyFFVarSet
  newBoolVars : BoolVarSet := emptyBoolVarSet
  deriving Inhabited

structure ExprSpec (c : ZKConfig) where
  inSymEnv : SymEnv c := emptySymEnv
  f : FFFormula c := FFFormula.false
  resVar : FFVar := default
  nextId : Nat := 0
  newFFVars : FFVarSet := emptyFFVarSet
  newBoolVars : BoolVarSet := emptyBoolVarSet
  deriving Inhabited

structure CondSpec (c : ZKConfig) where
  inSymEnv : SymEnv c := emptySymEnv
  f : FFFormula c := FFFormula.false
  nextId : Nat := 0
  newFFVars : FFVarSet := emptyFFVarSet
  newBoolVars : BoolVarSet := emptyBoolVarSet
  deriving Inhabited

structure IfSpec (c : ZKConfig) where
  inSymEnv : SymEnv c := emptySymEnv
  outSymEnv : SymEnv c := emptySymEnv
  tbF : FFFormula c := FFFormula.false
  ebF : FFFormula c := FFFormula.false
  nextId : Nat := 0
  newFFVars : FFVarSet := emptyFFVarSet
  newBoolVars : BoolVarSet := emptyBoolVarSet
  deriving Inhabited

structure FuncSpec (c : ZKConfig) where
  name : String := ""
  inSymEnv : SymEnv c := emptySymEnv
  outSymEnv : SymEnv c := emptySymEnv
  f : FFMacro c := default
  nextId : Nat := 0
  -- Concrete information about the parameters and return values
  params : List Param
  rets : List Param
  -- Variables that correspond to params
  numAuxFFVars : Nat := 0
  numAuxBoolVars : Nat := 0
  deriving Inhabited

structure RetVarsSpec (c : ZKConfig) where
  outSymEnv : SymEnv c := emptySymEnv
  nextId : Nat := 0
  newFFVars : FFVarSet := emptyFFVarSet
  actRetsVars : List (MacroCallParam c) := []
  deriving Inhabited


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


def simpleExprToTerm {c : ZKConfig}
  (senv : SymEnv c) (s : SimpleExpr c)
  : Except String (FFTerm c) :=
  match s with
  | .var id => match getVar senv id with
    | Except.ok (SymValue.ffVar (SymFFVar.const v)) => Except.ok (FFTerm.const v)
    | Except.ok (SymValue.ffVar (SymFFVar.var v)) => Except.ok (FFTerm.var v)
    | Except.ok (SymValue.ffArray _) => Except.error s!"Variable '{id}' is an array"
    | Except.error err => Except.error err
  | .val v => Except.ok (FFTerm.const v)

def symVarToTerm {c : ZKConfig} (v : SymFFVar c) : FFTerm c :=
  match v with
  | SymFFVar.const val => FFTerm.const val
  | SymFFVar.var v => FFTerm.var v

/- Try to evaluate an expression to a finite field value. This is used for constant propagation when
   possible.
-/
def evalExpr {c : ZKConfig}
  (senv : SymEnv c) (e : Expr c)
  : Except String (FF c) := do
  match e with
  -- arithmetic
  | .id s => Except.ok (evalId (← simpleExprToFF senv s))
  | .neg s => Except.ok (evalNeg (← simpleExprToFF senv s))
  | .add s1 s2 => Except.ok (evalAdd (← simpleExprToFF senv s1) (← simpleExprToFF senv s2))
  | .sub s1 s2 => Except.ok (evalSub (← simpleExprToFF senv s1) (← simpleExprToFF senv s2))
  | .mul s1 s2 => Except.ok (evalMul (← simpleExprToFF senv s1) (← simpleExprToFF senv s2))
  | .div s1 s2 => Except.ok (evalDiv (← simpleExprToFF senv s1) (← simpleExprToFF senv s2))
  -- bitwise
  | .shl s bits => Except.ok (evalShl (← simpleExprToFF senv s) (← simpleExprToFF senv bits))
  | .shr s bits => Except.ok (evalShr (← simpleExprToFF senv s) (← simpleExprToFF senv bits))
  | .and s1 s2 => Except.ok (evalAnd (← simpleExprToFF senv s1) (← simpleExprToFF senv s2))
  | .or s1 s2 => Except.ok (evalOr (← simpleExprToFF senv s1) (← simpleExprToFF senv s2))
  | .xor s1 s2 => Except.ok (evalXor (← simpleExprToFF senv s1) (← simpleExprToFF senv s2))
  | .not s => Except.ok (evalNot (← simpleExprToFF senv s))
   -- boolean
  | .True => Except.ok evalTrue
  | .False => Except.ok evalFalse
  | .eq s1 s2 => Except.ok (evalEq (← simpleExprToFF senv s1) (← simpleExprToFF senv s2))
  | .neq s1 s2 => Except.ok (evalNeq (← simpleExprToFF senv s1) (← simpleExprToFF senv s2))
  | .lt s1 s2 => Except.ok (evalLt (← simpleExprToFF senv s1) (← simpleExprToFF senv s2))
  | .gt s1 s2 => Except.ok (evalGt (← simpleExprToFF senv s1) (← simpleExprToFF senv s2))
  | .le s1 s2 => Except.ok (evalLe (← simpleExprToFF senv s1) (← simpleExprToFF senv s2))
  | .ge s1 s2 => Except.ok (evalGe (← simpleExprToFF senv s1) (← simpleExprToFF senv s2))
  | .bor s1 s2 => Except.ok (evalBor (← simpleExprToFF senv s1) (← simpleExprToFF senv s2))
  | .band s1 s2 => Except.ok (evalBand (← simpleExprToFF senv s1) (← simpleExprToFF senv s2))
  | .bneg s => Except.ok (evalBneg (← simpleExprToFF senv s))

/- Try to evaluate a condition to a boolean value. This is used to discard
   infeasible branches in if-statements.
-/
def evalCond {c : ZKConfig}
  (_cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c)
  (cond : Cond c)
  : Except String Bool := do
  match cond with
  | .eq s1 s2 =>
    let v1 ← simpleExprToFF senv s1
    let v2 ← simpleExprToFF senv s2
    return v1 == v2
  | .neq s1 s2 =>
    let v1 ← simpleExprToFF senv s1
    let v2 ← simpleExprToFF senv s2
    return v1 != v2

/- Symbolic execution of conditions -/
def sEvalCond {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (cond : Cond c)
  : Except String (CondSpec c) := do
  match cond with
  | .eq s1 s2 =>
    let v1 ← simpleExprToTerm senv s1
    let v2 ← simpleExprToTerm senv s2
    return {
      inSymEnv := senv,
      f := .eq v1 v2,
      nextId := cfg.nextId,
      newFFVars := emptyFFVarSet,
      newBoolVars := emptyBoolVarSet
    }
  | .neq s1 s2 =>
    let v1 ← simpleExprToTerm senv s1
    let v2 ← simpleExprToTerm senv s2
    return {
      inSymEnv := senv,
      f := .not (.eq v1 v2),
      nextId := cfg.nextId,
      newFFVars := emptyFFVarSet,
      newBoolVars := emptyBoolVarSet
    }

/- Symbolic expression of .id expression -/
def sEvalExprId {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (s : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v ← simpleExprToTerm senv s
  return {
          inSymEnv := senv,
          f := FFFormula.eq (FFTerm.var outFFVar) v, -- outVar = v
          resVar := outFFVar,
          nextId := cfg.nextId
  }

/- Symbolic expression of .neg expression -/
def sEvalExprNeg {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (s : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v ← simpleExprToTerm senv s
  return {
          inSymEnv := senv,
          f := FFFormula.eq (FFTerm.var outFFVar) (FFTerm.neg v), -- outVar = -v
          resVar := outFFVar,
          nextId := cfg.nextId
  }

/- Symbolic expression of .add expression -/
def sEvalExprAdd {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  return {
          inSymEnv := senv,
          f := FFFormula.eq (FFTerm.var outFFVar) (FFTerm.add v1 v2), -- outVar = v1 + v2
          resVar := outFFVar,
          nextId := cfg.nextId
  }

/- Symbolic expression of .sub expression -/
def sEvalExprSub {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  return {
          inSymEnv := senv,
          f := FFFormula.eq (FFTerm.var outFFVar) (FFTerm.sub v1 v2), -- outVar = v1 - v2
          resVar := outFFVar,
          nextId := cfg.nextId
  }

/- Symbolic expression of .mul expression -/
def sEvalExprMul {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  return {
          inSymEnv := senv,
          f := FFFormula.eq (FFTerm.var outFFVar) (FFTerm.mul v1 v2), -- outVar = v1 * v2
          resVar := outFFVar,
          nextId := cfg.nextId
  }

/- Symbolic expression of .div expression -/
def sEvalExprDiv {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  return {
          inSymEnv := senv,
          -- outVar*v2 = v1
          f := FFFormula.eq (FFTerm.mul (FFTerm.var outFFVar) v2) v1,  -- (outVar = v1 / v2)
          resVar := outFFVar,
          nextId := cfg.nextId
  }


def sEvalTrue {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD) (senv : SymEnv c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  return {
          inSymEnv := senv,
          f := FFFormula.eq (FFTerm.var outFFVar) (FFTerm.const 1), -- outVar = 1
          resVar := outFFVar,
          nextId := cfg.nextId
  }

def sEvalFalse {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD) (senv : SymEnv c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  return {
          inSymEnv := senv,
          f := FFFormula.eq (FFTerm.var outFFVar) (FFTerm.const 0), -- outVar = 0
          resVar := outFFVar,
          nextId := cfg.nextId
  }


def sEvalEq {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  return {
          inSymEnv := senv,
          f := FFFormula.ite
                 (FFFormula.eq v1 v2)
                 (FFFormula.eq (FFTerm.var outFFVar) (FFTerm.const 1))
                 (FFFormula.eq (FFTerm.var outFFVar) (FFTerm.const 0)),
          resVar := outFFVar,
          nextId := cfg.nextId
  }

def sEvalNeq {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  return {
          inSymEnv := senv,
          f := FFFormula.ite
                 (FFFormula.not (FFFormula.eq v1 v2))
                 (FFFormula.eq (FFTerm.var outFFVar) (FFTerm.const 0))
                 (FFFormula.eq (FFTerm.var outFFVar) (FFTerm.const 1)),
          resVar := outFFVar,
          nextId := cfg.nextId
  }

def sEvalBor {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  return {
          inSymEnv := senv,
          f : FFFormula c :=
               .ite (.or (.eq v1 (.const 1)) (.eq v2 (.const 1)))
                    (.eq (.var outFFVar) (.const 1))
                    (.eq (.var outFFVar) (.const 0)),
          resVar := outFFVar,
          nextId := cfg.nextId
  }

def sEvalAnd {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (s1 s2 : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v1 ← simpleExprToTerm senv s1
  let v2 ← simpleExprToTerm senv s2
  return {
          inSymEnv := senv,
          f : FFFormula c :=
               .ite (.and (.eq v1 (.const 1)) (.eq v2 (.const 1)))
                    (.eq (.var outFFVar) (.const 1))
                    (.eq (.var outFFVar) (.const 0)),
          resVar := outFFVar,
          nextId := cfg.nextId
  }

def sEvalNeg {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD)
  (senv : SymEnv c) (s : SimpleExpr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  let v ← simpleExprToTerm senv s
  return {
          inSymEnv := senv,
          f : FFFormula c :=
               .ite (.eq v (FFTerm.const 1))
                    (.eq (FFTerm.var outFFVar) (.const 0))
                    (.eq (FFTerm.var outFFVar) (.const 1)),
          resVar := outFFVar,
          nextId := cfg.nextId
  }

def sEvalExpr {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD) (symEnv : SymEnv c) (e : Expr c) (outFFVar : FFVar)
  : Except String (ExprSpec c) := do
  match e with
  -- arithmetic
  | .id s => sEvalExprId cfg md symEnv s outFFVar
  | .neg s => sEvalExprNeg cfg md symEnv s outFFVar
  | .add s1 s2 => sEvalExprAdd cfg md symEnv s1 s2 outFFVar
  | .sub s1 s2 => sEvalExprSub cfg md symEnv s1 s2 outFFVar
  | .mul s1 s2 => sEvalExprMul cfg md symEnv s1 s2 outFFVar
  | .div s1 s2 => sEvalExprDiv cfg md symEnv s1 s2 outFFVar
  -- bitwise are all missing
  -- boolean
  | .True => sEvalTrue cfg md symEnv outFFVar
  | .False => sEvalFalse cfg md symEnv outFFVar
  | .eq s1 s2 => sEvalEq cfg md symEnv s1 s2 outFFVar
  | .neq s1 s2 => sEvalNeq cfg md symEnv s1 s2 outFFVar
  -- missing lt, le, gt, and ge
  | .bor s1 s2 => sEvalBor cfg md symEnv s1 s2 outFFVar
  | .and s1 s2 => sEvalAnd cfg md symEnv s1 s2 outFFVar
  | .bneg s => sEvalNeg cfg md symEnv s outFFVar
   -- bitwise operations and comparisons are not implemented yet
  | _ => Except.error s!"Expression evaluation not implemented yet"


/- Symbolic execution of 'skip' -/
def seSkip {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD) (symEnv : SymEnv c) : Except String (CmdsSpec c) := do
  return { inSymEnv := symEnv, outSymEnv := symEnv, f := FFFormula.true, nextId := cfg.nextId }

/- Symbolic execution of constant assignment -/
def seAssignmentConst {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD) (symEnv : SymEnv c) (id : String) (e : Expr c)
  : Except String (CmdsSpec c) := do
  let r ← evalExpr symEnv e
  let newSymEnv := setVar symEnv id (SymValue.ffVar (SymFFVar.const r))
  return { inSymEnv := symEnv,
           outSymEnv := newSymEnv,
           f := FFFormula.true,
           nextId := cfg.nextId,
           newFFVars := emptyFFVarSet,
           newBoolVars := emptyBoolVarSet
  }

/- Symbolic execution of non-constant assignment -/
def seAssignmentNonConst {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD) (symEnv : SymEnv c) (id : VarID) (e : Expr c)
  : Except String (CmdsSpec c) := do
  -- new variable for the result of the expression
  let outFFVar : FFVar := { id := cfg.nextId,
                            meta_data := { src_info := md.src_info, orig_name := id}
                          }
  -- increment the nextId in the config for the next variable
  let cfg' : SymExecConfig c := { cfg with nextId := cfg.nextId + 1 }
  -- calculate the spec for the expression
  let exprSpec ← sEvalExpr cfg' md symEnv e outFFVar
  -- update the symbolic environment with the new variable
  let newSymEnv := setVar symEnv id (SymValue.ffVar (SymFFVar.var outFFVar))
  -- the command spec
  return { inSymEnv := symEnv,
           outSymEnv := newSymEnv,
           f := exprSpec.f,
           nextId := exprSpec.nextId,
           newFFVars := exprSpec.newFFVars.insert outFFVar,
           newBoolVars := exprSpec.newBoolVars }

/- Symbolic execution of assignment -/
def seAssignment {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD) (symEnv : SymEnv c) (id : VarID) (e : Expr c)
  : Except String (CmdsSpec c) := do
  match seAssignmentConst cfg md symEnv id e with -- try to do constant propagation first
  | Except.ok spec => return spec
  | Except.error _ => seAssignmentNonConst cfg md symEnv id e

/- Symbolic execution of array creation -/
def seNewArray {c : ZKConfig}
  (_cfg : SymExecConfig c) (_md : CmdMD) (symEnv : SymEnv c) (id : VarID) (size : SimpleExpr c)
  : Except String (CmdsSpec c) := do
  match simpleExprToFF symEnv size with
  | Except.error err => Except.error ("seNewArray: failed to evaluate size expression: " ++ err)
  | Except.ok sz =>
    let arr : SymFFArray c := (List.replicate sz.val (.const 0)).toArray
    let newSymEnv := setVar symEnv id (SymValue.ffArray arr)
    return { inSymEnv := symEnv,
             outSymEnv := newSymEnv,
             f := FFFormula.true,
             nextId := _cfg.nextId,
             newFFVars := emptyFFVarSet,
             newBoolVars := emptyBoolVarSet
    }


def seArrayReadConstIdx {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD) (symEnv : SymEnv c)
  (out : VarID) (a : VarID) (idx : SimpleExpr c)
  : Except String (CmdsSpec c) := do
  let idxVal ← simpleExprToFF symEnv idx
  match getVar symEnv a with
  | Except.error err => Except.error ("seArrayReadConstIdx: failed to get array variable: " ++ err)
  | Except.ok (SymValue.ffArray arr) =>
    if h : idxVal.val < arr.size then
      let elem := arr[idxVal.val]'h
      match elem with
      | SymFFVar.const v =>
        let newSymEnv := setVar symEnv out (SymValue.ffVar (SymFFVar.const v))
        return { inSymEnv := symEnv,
                 outSymEnv := newSymEnv,
                 f := FFFormula.true,
                 nextId := cfg.nextId,
                 newFFVars := emptyFFVarSet,
                 newBoolVars := emptyBoolVarSet
        }
      | SymFFVar.var v =>
        let newSymEnv := setVar symEnv out (SymValue.ffVar (SymFFVar.var v))
        return { inSymEnv := symEnv,
                 outSymEnv := newSymEnv,
                 f := FFFormula.true,
                 nextId := cfg.nextId,
                 newFFVars := emptyFFVarSet,
                 newBoolVars := emptyBoolVarSet
        }
    else
      Except.error
         s!"seArrayReadConstIdx: index {idxVal.val} out of bounds for array of size {arr.size}"
  | Except.ok _ => Except.error s!"seArrayReadConstIdx: variable '{a}' is not an array"

/- Symbolic execution of array read -/
def seArrayRead {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD) (symEnv : SymEnv c)
  (out : VarID) (a : VarID) (idx : SimpleExpr c)
  : Except String (CmdsSpec c) := do
  match seArrayReadConstIdx cfg md symEnv out a idx with
  | Except.ok spec => return spec
  | Except.error _ =>
    throw s!"seArrayRead operations with non-constant index not implemented yet"


def simpleExprToSymFFVar {c : ZKConfig}
  (senv : SymEnv c) (s : SimpleExpr c)
  : Except String (SymFFVar c) :=
  match s with
  | .var id => match getVar senv id with
    | Except.ok (SymValue.ffVar v) => Except.ok v
    | Except.ok (SymValue.ffArray _) => Except.error s!"Variable '{id}' is an array"
    | Except.error err => Except.error err
  | .val v => Except.ok (SymFFVar.const v)

def seArrayWriteConstIdx {c : ZKConfig}
  (cfg : SymExecConfig c) (_md : CmdMD) (symEnv : SymEnv c)
  (a : VarID) (idx : SimpleExpr c) (value : SimpleExpr c)
  : Except String (CmdsSpec c) := do
  let idxVal ← simpleExprToFF symEnv idx
  let valueVal ← simpleExprToSymFFVar symEnv value
  match getVar symEnv a with
  | Except.error err => Except.error ("seArrayWriteConstIdx: failed to get array variable: " ++ err)
  | Except.ok (SymValue.ffArray arr) =>
    if h : idxVal.val < arr.size then
      let newArr := arr.set idxVal.val valueVal
      let newSymEnv := setVar symEnv a (SymValue.ffArray newArr)
      return { inSymEnv := symEnv,
               outSymEnv := newSymEnv,
               f := FFFormula.true,
               nextId := cfg.nextId,
               newFFVars := emptyFFVarSet,
               newBoolVars := emptyBoolVarSet
      }
    else
      Except.error
         s!"seArrayWriteConstIdx: index {idxVal.val} out of bounds for array of size {arr.size}"
  | Except.ok _ => Except.error s!"seArrayWriteConstIdx: variable '{a}' is not an array"

def seArrayWrite {c : ZKConfig}
  (cfg : SymExecConfig c) (md : CmdMD) (symEnv : SymEnv c)
  (a : VarID) (idx : SimpleExpr c) (value : SimpleExpr c)
  : Except String (CmdsSpec c) := do
  match seArrayWriteConstIdx cfg md symEnv a idx value with
  | Except.ok spec => return spec
  | Except.error e =>
     throw s!"seArrayWrite operations not implemented yet: {e}"

def seArrayCopy {c : ZKConfig}
  (_cfg : SymExecConfig c) (_md : CmdMD) (_symEnv : SymEnv c) (_out : VarID) (_a : VarID)
  : Except String (CmdsSpec c) := do
  throw s!"seArrayCopy operations not implemented yet"

end Llzk.SymExec.Basic
