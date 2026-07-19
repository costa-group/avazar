import Corellzk2smt.Basic
import Corellzk2smt.Language.Core.Syntax.AST
import Corellzk2smt.Language.Core.Syntax.Printer
import Corellzk2smt.FFConstraints.Basic
import Corellzk2smt.Language.Core.Semantics.Basic
import Std.Data.TreeMap.Basic

namespace Corellzk2smt.SymExec.Basic

open Corellzk2smt.Language.Core.Syntax.AST
open Corellzk2smt.FFConstraints.Basic
open Corellzk2smt.Language.Core.Semantics.Basic


/- This is a structure that will be passed around in the symbolic interpreter. We can
   encapsulate various things here. Separating it from the symbolic state makes things
   simpler.

   The most important part of the configuration is the 'nextVarId', which is indicates what is
   the next identifier (for the constraints) to be used to generate new variables. We should
   guarantee that it is fresh, i.e., it is not used in the current symbolic state.
-/
structure SymExecConfig (c : ZKConfig) where
  nextVarId : Nat := 0
  deriving Repr, BEq, Inhabited


/- A binary representation of a finite field variable. The first element of
   the list corresponds to the least significant bit. -/
abbrev bits (c : ZKConfig) := Option (List (FFTerm c))


/- A structure representing a finite field variable along with its binary representation. The
   binary representation is optional, and is usually calculated the first time it is needed
   and then reused.
-/
structure FFVarWithBinRep (c : ZKConfig) where
  var : FFVar
  bits : Option (bits c)
  deriving Repr, BEq, Inhabited


/- Simple symbolic value can be either a concrete finite
   field value or a field constraint variable
-/
inductive SimpleSymVal (c : ZKConfig) where
  | ffvar : FFVarWithBinRep c → SimpleSymVal c
  | const : FF c → SimpleSymVal c
  deriving Repr, BEq, Inhabited

/- A symbolic array is an array of simple symbolic values -/
abbrev SymArray (c : ZKConfig) := Array (SimpleSymVal c)

/- A symbolic value can either be a simple symbolic value or a symbolic array -/
inductive SymValue (c : ZKConfig) where
  | simple : SimpleSymVal c → SymValue c
  | array : SymArray c → SymValue c
  deriving Repr, BEq, Inhabited

/- A symbolic environment is a mapping from program variables to symbolic values -/
abbrev SymEnv (c : ZKConfig) := Std.TreeMap VarID (SymValue c)

/-- An empty symbolic environment. -/
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

/- Check if a variable is defined in a symbolic environment. -/
def isDefinedVar {c : ZKConfig} (env : SymEnv c) (id : VarID) : Bool :=
  env.contains id

/-- Set several variables at once in a symbolic environment -- the symbolic mirror of
    `Semantics.Basic.setVars`, used by `seFuncCall` to bind a call's fresh output values into
    the caller's `outs`. -/
def setVars {c : ZKConfig} (env : SymEnv c) (ids : List VarID) (vs : List (SymValue c))
    : Except String (SymEnv c) :=
  match ids, vs with
  | [], [] => Except.ok env
  | id :: ids, v :: vs =>
    match setVars (setVar env id v) ids vs with
    | Except.ok env' => Except.ok env'
    | Except.error err => Except.error err
  | _, _ => Except.error "Mismatched lengths of ids and values"


/- A formula representing a functional relationship. In particular, its satisfiablity does not
   depend on the values of the variables in 'inVars'.

   TODO: move this defintion to FFConstraints later.
-/

structure FunctionalFormula (c : ZKConfig) where
  f : FFFormula c := FFFormula.false
  vars : VarSet := emptyVarSet
  inVars : VarSet := emptyVarSet
  deriving Repr, BEq, Inhabited



/- A specification for a sequence of commands.
-/
structure CmdsSpec (c : ZKConfig) where
  inSymEnv : SymEnv c := emptySymEnv
  outSymEnv : SymEnv c := emptySymEnv
  f : FFFormula c := FFFormula.false
  -- these are variables in f that appear in
  -- the inSymEnv and outSymEnv. Without the parts
  -- of the binary expansion, these always appear
  -- as auxiliary variables so far.
  fVars : VarSet := emptyVarSet
  -- these are variables that are in f but not
  -- in the inSymEnv and outSymEnv.
  auxVars : VarSet := emptyVarSet

  -- We need a proposition stating that the variables of f
  -- are exactly the union of fVars and auxVars.

  nextVarId : Nat := 0

structure FuncSpec (c : ZKConfig) where
  name : String := ""
  inSymEnv : SymEnv c := emptySymEnv
  outSymEnv : SymEnv c := emptySymEnv
  f : FFMacro c := default
  nextVarId : Nat := 0
  -- Concrete information about the function's parameters and return values -- needed by
  -- `seFuncCall` at a call site to know how to flatten actual arguments/outputs (each `.array
  -- size` param/ret becomes `size` consecutive macro parameters, matching `f.params`'s layout).
  params : List Param := []
  rets : List Param := []
  -- How many trailing macro parameters (beyond the flattened params/rets) are auxiliary
  -- (internal to the function, not part of its input/output signature) -- `seFuncCall` mints
  -- this many fresh call-site variables to fill those slots.
  numAuxFFVars : Nat := 0
  numAuxBoolVars : Nat := 0

/-- Fetch a function's spec by name from a list of specs. Mirrors `fetchFunc`/`fetchMacro`'s
    shape, but doesn't need to return the remaining list (`specs` isn't consumed structurally
    the way `Prog`/`List (FFMacro c)` are during a recursive call -- `seFuncCall` doesn't
    recurse into the callee's own body, that's `H_funcCall`'s separate concern). -/
def fetchFuncSpec {c : ZKConfig} (specs : List (FuncSpec c)) (fname : FName)
    : Except String (FuncSpec c) :=
  match specs with
  | [] => Except.error s!"Function spec for '{fname}' not found"
  | spec :: rest => if spec.name == fname then Except.ok spec else fetchFuncSpec rest fname

/-

structure ExprSpec (c : ZKConfig) where
  inSymEnv : SymEnv c := emptySymEnv
  outSymEnv : SymEnv c := emptySymEnv
  f : FFFormula c := FFFormula.false

structure ExprSpec (c : ZKConfig) where
  inSymEnv : SymEnv c := emptySymEnv
  outSymEnv : SymEnv c := emptySymEnv
  f : FFFormula c := FFFormula.false
  -- resVar is not really used now. Maybe it will
  -- be useful for the proofs later.
  resTerm : FFTerm c := default
  res : SymFFVar c := default
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

structure BitifySpec (c : ZKConfig) where
  nextId : Nat := 0
  f : FFFormula c := FFFormula.false
  bits : List (FFTerm c) := []
  vars : List FFVar := []
  bitifedTerm : FFTerm c := default
  newFFVars : FFVarSet := emptyFFVarSet
  newBoolVars : BoolVarSet := emptyBoolVarSet
  deriving Inhabited


structure BinExpanSpec (c : ZKConfig) where

  -- input and output symbolic environments. The output is needed because we are
  -- suppose to memoize the binary expansion.
  inSymEnv : SymEnv c := emptySymEnv
  outSymEnv : SymEnv c := emptySymEnv

  -- the next available variable id after the binary expansion
  nextId : Nat := 0

  -- The formula that relates the bits to the original term, if needed (if it
  -- has been binary expanded already, or it is a constant, then no need)
  f : FFFormula c := FFFormula.true

  -- The list of bits as terms, in the order from least significant to most significant.
  -- The maximum length is c.k, and it can be shorter if the term is binary expanded
  -- with fewer bits (e.g., a constant). The remaining up to c.k are 0.
  bits : List (FFTerm c) := []

  -- New variables introduced during encoding
  newFFVars : FFVarSet := emptyFFVarSet
  newBoolVars : BoolVarSet := emptyBoolVarSet
  deriving Inhabited

-/

end Corellzk2smt.SymExec.Basic
