import Corellzk2smt.Basic
import Corellzk2smt.Language.Core.Syntax.AST
import Corellzk2smt.Config

/- This module defines the syntax of constraint systems over finite fields
   and boolean variables -/

namespace Corellzk2smt.FFConstraints.Basic

open Corellzk2smt.Config (GlobalConfig)
open Corellzk2smt.Language.Core.Syntax.AST (SrcInfo VarID)


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
  orig_name : VarID
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
  | .boolv n => s!"b_{n}"


/-  Ordering (Ord) of Var. Needed if we use ordered sets
    or maps. Bool variables are considered greater than FF variables.
-/
instance : Ord Var where
  compare a b := match a, b with
  | .ffv id1, .ffv id2 => compare id1 id2
  | .boolv id1, .boolv id2 => compare id1 id2
  | .ffv _, .boolv _ => Ordering.lt
  | .boolv _, .ffv _ => Ordering.gt


/-  OrientedCmp for Var: `compare a b = (compare b a).swap`.
    - Same-constructor cases delegate to Nat (OrientedOrd Nat, from Mathlib).
    - Cross-constructor cases: .lt and .gt are swaps of each other. -/
instance : Std.OrientedCmp (compare : Var → Var → Ordering) where
  eq_swap := by
    intro a b
    match a, b with
    | .ffv n,   .ffv m   =>
      change compare n m = (compare m n).swap
      exact Std.OrientedCmp.eq_swap
    | .boolv n, .boolv m =>
      change compare n m = (compare m n).swap
      exact Std.OrientedCmp.eq_swap
    | .ffv _,   .boolv _ => rfl
    | .boolv _, .ffv _   => rfl

/-  TransCmp for Var: `(compare a b).isLE → (compare b c).isLE → (compare a c).isLE`.
    - Same-constructor cases delegate to Nat (TransOrd Nat, from Mathlib).
    - Cross-constructor cases are settled by the fixed ordering ffv < boolv:
        the conclusion is trivially true, or a hypothesis is absurd (gt.isLE = false). -/
instance : Std.TransCmp (compare : Var → Var → Ordering) where
  isLE_trans {a b c} h1 h2 := by
    -- Nat's TransCmp instance (via Mathlib's TransOrd Nat)
    have natTC := (inferInstance : Std.TransCmp (compare : Nat → Nat → Ordering))
    match a, b, c with
    | .ffv n,   .ffv m,   .ffv k   =>
      -- (compare (ffv n) (ffv m)) reduces definitionally to (compare n m : Nat)
      have h1' : (compare n m).isLE := h1
      have h2' : (compare m k).isLE := h2
      exact natTC.isLE_trans h1' h2'
    | .boolv n, .boolv m, .boolv k =>
      have h1' : (compare n m).isLE := h1
      have h2' : (compare m k).isLE := h2
      exact natTC.isLE_trans h1' h2'
    -- ffv ≤ ffv ≤ boolv  →  ffv < boolv  (Ordering.lt.isLE = true, trivial)
    | .ffv _,   .ffv _,   .boolv _ => trivial
    -- ffv < boolv ≤ boolv  →  ffv < boolv  (same)
    | .ffv _,   .boolv _, .boolv _ => trivial
    -- boolv > ffv: compare(.boolv,.ffv) = .gt, so .isLE = false, h1 absurd
    | .boolv n, .ffv m,   _        =>
      have : (compare (Var.boolv n) (Var.ffv m)).isLE = false := rfl
      simp [this] at h1
    -- boolv ≥ boolv, boolv > ffv: h2 : compare(.boolv,.ffv).isLE = false, absurd
    | .boolv _, .boolv m, .ffv k   =>
      have : (compare (Var.boolv m) (Var.ffv k)).isLE = false := rfl
      simp [this] at h2
    -- ffv < boolv, boolv > ffv: h2 absurd
    | .ffv _,   .boolv m, .ffv k   =>
      have : (compare (Var.boolv m) (Var.ffv k)).isLE = false := rfl
      simp [this] at h2

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

instance : HasSubset VarSet where
  Subset s t := ∀ x, x ∈ s → x ∈ t


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
  | and    : FFFormula c → FFFormula c → FFFormula c -- and
  | or     : FFFormula c → FFFormula c → FFFormula c -- or
  | not    : FFFormula c → FFFormula c -- negation
  | ite    : FFFormula c → FFFormula c → FFFormula c → FFFormula c  -- bool if-then-else
  | imply  : FFFormula c → FFFormula c → FFFormula c  -- implication
  | iff    : FFFormula c → FFFormula c → FFFormula c  -- if and only if
  | call   : String → List (MacroCallParam c) → FFFormula c  -- macro call
  | anno   : FFFormula c → String → FFFormula c  -- annotated formula
  deriving Repr, BEq, Inhabited

end

/- Trivial definition for size of formula, to be used for proving termination.
   Tried to use the default sizeOf but failed to unfold at some point.
   Revisit this later. -/

mutual

def sizeOfTerm {c : ZKConfig} (ffterm : FFTerm c) : Nat :=
  match ffterm with
  | .val _ => 1
  | .var _ => 1
  | .add a b | .sub a b | .mul a b =>
      1 + sizeOfTerm a + sizeOfTerm b
  | .neg a => 1 + sizeOfTerm a
  | .ite c t e => 1 + sizeOfFormula c + sizeOfTerm t + sizeOfTerm e

def sizeOfFormula {c : ZKConfig} (f: FFFormula c) : Nat :=
  match f with
  | .true | .false => 1
  | .range t _ _=> 1 + sizeOfTerm t
  | .bool _ => 1
  | .eq a b => 1 + sizeOfTerm a + sizeOfTerm b
  | .and a b => 1 + sizeOfFormula a + sizeOfFormula b
  | .or a b => 1 + sizeOfFormula a + sizeOfFormula b
  | .imply a b => 1 + sizeOfFormula a + sizeOfFormula b
  | .iff a b => 1 + sizeOfFormula a + sizeOfFormula b
  | .not a => 1 + sizeOfFormula a
  | .ite c t e => 1 + sizeOfFormula c + sizeOfFormula t + sizeOfFormula e
  | .call _ _ => 1
  | .anno f _ => 1 + sizeOfFormula f

end


/- FFVariables in a term and formula -/
mutual

def ffVarsOfTerm {c : ZKConfig} (t : FFTerm c) : VarSet :=
  match t with
  | .val _     => emptyVarSet
  | .var n     => emptyVarSet.insert (Var.ffv n)
  | .add a b
  | .sub a b
  | .mul a b   => ffVarsOfTerm a ∪ ffVarsOfTerm b
  | .neg a     => ffVarsOfTerm a
  | .ite f a b => ffVarsOfFormula f ∪ ffVarsOfTerm a ∪ ffVarsOfTerm b

def ffVarsOfFormula {c : ZKConfig} (f : FFFormula c) : VarSet :=
  match f with
  | .true | .false => emptyVarSet
  | .range t _ _   => ffVarsOfTerm t
  | .bool _        => emptyVarSet
  | .eq a b        => ffVarsOfTerm a ∪ ffVarsOfTerm b
  | .and a b
  | .or a b
  | .imply a b
  | .iff a b       => ffVarsOfFormula a ∪ ffVarsOfFormula b
  | .not a         => ffVarsOfFormula a
  | .ite c a b     => ffVarsOfFormula c ∪ ffVarsOfFormula a ∪ ffVarsOfFormula b
  | .call _ params =>
      params.foldl (fun acc p => match p with
        | .var (.ffv n) => acc.insert (Var.ffv n)
        | _             => acc) emptyVarSet
  |.anno f _ => ffVarsOfFormula f

end


/- Boolean variables in a term and formula -/
mutual

def bVarsOfTerm {c : ZKConfig} (t : FFTerm c) : VarSet :=
  match t with
  | .val _     => emptyVarSet
  | .var _     => emptyVarSet
  | .add a b
  | .sub a b
  | .mul a b   => bVarsOfTerm a ∪ bVarsOfTerm b
  | .neg a     => bVarsOfTerm a
  | .ite f a b => bVarsOfFormula f ∪ bVarsOfTerm a ∪ bVarsOfTerm b

def bVarsOfFormula {c : ZKConfig} (f : FFFormula c) : VarSet :=
  match f with
  | .true | .false => emptyVarSet
  | .range t _ _   => bVarsOfTerm t
  | .bool n        => emptyVarSet.insert (Var.boolv n)
  | .eq a b        => bVarsOfTerm a ∪ bVarsOfTerm b
  | .and a b
  | .or a b
  | .imply a b
  | .iff a b       => bVarsOfFormula a ∪ bVarsOfFormula b
  | .not a         => bVarsOfFormula a
  | .ite c a b     => bVarsOfFormula c ∪ bVarsOfFormula a ∪ bVarsOfFormula b
  | .call _ params =>
      params.foldl (fun acc p => match p with
        | .var (.boolv n) => acc.insert (Var.boolv n)
        | _               => acc) emptyVarSet
  | .anno f _ => bVarsOfFormula f

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
    (gconf : GlobalConfig c) (ms : List (FFMacro c)) (name : String)
    : Except String (FFMacro c × List (FFMacro c)) :=
  match ms with
  | [] => Except.error s!"Macro {name} not found"
  | m :: rest =>
      if m.name == name then Except.ok (m, rest)
      else fetchMacro gconf rest name

theorem fetchMacroLT {c : ZKConfig} (gconf : GlobalConfig c) (ms ms' : List (FFMacro c))
    (name : String) (m : FFMacro c) :
  fetchMacro gconf ms name = Except.ok (m, ms') → ms'.length < ms.length := by
  cases ms with
  | nil => simp [fetchMacro]
  | cons head tail =>
      simp only [fetchMacro]
      by_cases h : head.name = name
      · simp only [h, BEq.rfl, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq, List.length_cons,
        Order.lt_add_one_iff, and_imp] at *
        intro  h1 h2
        rw [h2]
      · simp only [h, not_false_eq_true, beq_iff_eq, ↓reduceIte, List.length_cons,
        Order.lt_add_one_iff] at *
        intro h1
        have h2 := fetchMacroLT gconf tail ms' name m h1
        grind

/- The main formula of a constraint system is a call to the
   main macro -/
def mainFormula {c : ZKConfig} (gconf : GlobalConfig c) (sys : FFConstraintSystem c)
    : Except String (FFFormula c × List Var) :=
  match fetchMacro gconf sys.macros sys.main with
  | Except.error msg => Except.error msg
  | Except.ok (m, _) =>
      let params := m.params.map (fun v => (MacroCallParam.var v))
      Except.ok (FFFormula.call m.name params, m.params)

end Corellzk2smt.FFConstraints.Basic
