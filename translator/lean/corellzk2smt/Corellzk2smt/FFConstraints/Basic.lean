import Corellzk2smt.Basic
import Corellzk2smt.Language.Core.Syntax.AST

/- This module defines the syntax of constraint systems over finite fields
   and boolean variables -/

namespace Corellzk2smt.FFConstraints.Basic
open Corellzk2smt.Language.Core.Syntax.AST


/- A finite field variable -/
abbrev FFVar := ℕ

/- A boolean variable -/
abbrev BoolVar := ℕ

/- A variable, which can be either a finite field variable or a boolean variable -/
inductive Var where
  | ffv (v : FFVar) : Var
  | boolv (v : BoolVar) : Var
  deriving Repr, BEq, Inhabited

/- Metadata for FF variables -/
structure VarMetaData where
  orig_name : String
  src_info : SrcInfo
  deriving Repr, BEq, Inhabited

-- A FF or a bool value
inductive Const (c : ZKConfig) where
  | ffc (v : FF c) : Const c
  | boolc (v : Bool) : Const c
  deriving Repr, BEq, Inhabited

/- When calling a macro we provide a value or a variable -/
inductive MacroCallParam (c : ZKConfig) where
  | var (v : Var) : MacroCallParam c
  | const  (v : Const c) : MacroCallParam c
  deriving Repr, BEq, Inhabited


/- ToString instance for FFVar -/
instance : ToString Var where
  toString v := match v with
  | .ffv n => s!"v_{n}"
  | .boolv n => s!"v_{n}"


/-  Ordering (Ord) of Var. Needed if we use ordered sets
    or maps. Bool variables are considered greater than FF variables.
-/
instance : Ord Var where
  compare a b := match a, b with
  | .ffv id1, .ffv id2 => compare id1 id2
  | .boolv id1, .boolv id2 => compare id1 id2
  | .ffv _, .boolv _ => Ordering.lt
  | .boolv _, .ffv _ => Ordering.gt


/-  Hashing (Hashable) of Var. Needed if we use this in a HashMap or HashSet -/
instance : Hashable Var where
  hash a := match a with
  | .ffv n => mixHash (hash "ffv") (hash n)
  | .boolv n => mixHash (hash "boolv") (hash n)


/- Variable information -/
abbrev VarInfo := Std.TreeMap Var VarMetaData compare
abbrev emptyVarInfo : VarInfo := Std.TreeMap.empty

-- abbrev VarInfo := Var -> Option VarMetaData
-- abbrev emptyVarInfo : VarInfo := fun _ => none

def addVarInfo (v : Var) (info : VarMetaData) (vi : VarInfo) : VarInfo :=
  vi.insert v info

def lookupVarInfo (v : Var) (vi : VarInfo) : Option VarMetaData :=
  vi.get? v
/- -/


/- Var set -/
abbrev VarSet := Std.TreeSet Var compare
abbrev emptyVarSet : VarSet := Std.TreeSet.empty


mutual
/- Term is a polynomial expression over finite fields -/
inductive FFTerm (c : ZKConfig) where
  | val : FF c →  FFTerm c
  | var : FFVar → FFTerm c
  | add : FFTerm c → FFTerm c → FFTerm c
  | sub : FFTerm c → FFTerm c → FFTerm c
  | mul : FFTerm c → FFTerm c → FFTerm c
  | neg : FFTerm c → FFTerm c
  | ite : FFFormula c → FFTerm c → FFTerm c → FFTerm c  -- term if-then-else
  deriving Repr, BEq, Inhabited


/- A formula is a boolean formula with P(x)=0 as atoms.  -/
inductive FFFormula (c : ZKConfig) where
  | true   : FFFormula c
  | false  : FFFormula c
  | range  : FFTerm c → FF c -> FF c -> FFFormula c        -- P(x) in the range of the field
  | bool   : BoolVar → FFFormula c        -- A boolean variable
  | eq     : FFTerm c → FFTerm c → FFFormula c       -- P1(x) = P2(x)
  | lt     : FFTerm c → FFTerm c → FFFormula c       -- P1(x) < P2(x)
  | gt     : FFTerm c → FFTerm c → FFFormula c       -- P1(x) > P2(x)
  | le     : FFTerm c → FFTerm c → FFFormula c       -- P1(x) <= P2(x)
  | ge     : FFTerm c → FFTerm c → FFFormula c       -- P1(x) >= P2(x)
  -- TODO add lt, etc with the same semantics as in the interpreter
  | and    : FFFormula c → FFFormula c → FFFormula c -- and
  | or     : FFFormula c → FFFormula c → FFFormula c -- or
  | not    : FFFormula c → FFFormula c -- negation
  | ite    : FFFormula c → FFFormula c → FFFormula c → FFFormula c  -- bool if-then-else
  | imply  : FFFormula c → FFFormula c → FFFormula c  -- implication
  | iff    : FFFormula c → FFFormula c → FFFormula c  -- if and only if
  | call   : String → List (MacroCallParam c) → FFFormula c  -- macro call
  deriving Repr, BEq, Inhabited

end

/- Trivial definition for size of formula, to be used for proving termination.
   Tried to use the default sizeOf but failed to unfold at some point.
   Revisit this later. -/

mutual

def sizeOfTerm {c : ZKConfig} : FFTerm c → Nat
  | .val _ => 1
  | .var _ => 1
  | .add a b | .sub a b | .mul a b => 1 + sizeOfTerm a + sizeOfTerm b
  | .neg a => 1 + sizeOfTerm a
  | .ite c t e => 1 + sizeOfFormula c + sizeOfTerm t + sizeOfTerm e

def sizeOfFormula {c : ZKConfig} : FFFormula c → Nat
  | .true | .false => 1
  | .range t _ _=> 1 + sizeOfTerm t
  | .bool _ => 1
  | .eq a b => 1 + sizeOfTerm a + sizeOfTerm b
  | .lt a b => 1 + sizeOfTerm a + sizeOfTerm b
  | .gt a b => 1 + sizeOfTerm a + sizeOfTerm b
  | .le a b => 1 + sizeOfTerm a + sizeOfTerm b
  | .ge a b => 1 + sizeOfTerm a + sizeOfTerm b
  | .and a b => 1 + sizeOfFormula a + sizeOfFormula b
  | .or a b => 1 + sizeOfFormula a + sizeOfFormula b
  | .imply a b => 1 + sizeOfFormula a + sizeOfFormula b
  | .iff a b => 1 + sizeOfFormula a + sizeOfFormula b
  | .not a => 1 + sizeOfFormula a
  | .ite c t e => 1 + sizeOfFormula c + sizeOfFormula t + sizeOfFormula e
  | .call _ _ => 1

end


/- Relates a VarID in a macro and the exit information for it, that can be:
    - a FFVar
    - a constant FF value
    - an array of FFVar or constant values
 -/
inductive MacroExitVarInfo (c : ZKConfig)
| ffVar (v : FFVar)
| const (val : FF c)
| array (arr : List (FFVar ⊕ FF c)) -- an array can contain either variables or constants
  deriving Repr, BEq, Inhabited

abbrev MacroExitVarsInfo (c : ZKConfig) := List (VarID × MacroExitVarInfo c)



/- A macro is a named formula with parameters -/
structure FFMacro (c : ZKConfig) where
  name : String
  params : List Var
  body : FFFormula c
  vars_info : MacroExitVarsInfo c := default
  deriving Repr, BEq, Inhabited

/- A constraint system consists of a list of macros and the name of the main macro -/
structure FFConstraintSystem (c : ZKConfig) where
  macros : List (FFMacro c)
  main : String
  deriving Repr, BEq, Inhabited

/-- Fetch a macro by name from a list of macros. Throws an error if
    the macro is not found. -/
/- FIXME: can we return the list of macros after removing the fetched
   macro? Macros cannot be recursive
-/
def fetchMacro {c : ZKConfig}
    (ms : List (FFMacro c)) (name : String) : Except String (FFMacro c × List (FFMacro c)) :=
  match ms with
  | [] => Except.error s!"Macro {name} not found"
  | m :: rest =>
      if m.name == name then Except.ok (m, rest)
      else fetchMacro rest name

/- The main formula of a constraint system is a call to the
   main macro -/
def mainFormula {c : ZKConfig} (sys : FFConstraintSystem c)
    : Except String (FFFormula c × List Var) :=
  match fetchMacro sys.macros sys.main with
  | Except.error msg => Except.error msg
  | Except.ok (m, _) =>
      let params := m.params.map (fun v => (MacroCallParam.var v))
      Except.ok (FFFormula.call m.name params, m.params)

end Corellzk2smt.FFConstraints.Basic
