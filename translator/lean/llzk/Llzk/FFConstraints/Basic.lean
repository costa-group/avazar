import Llzk.Basic
import Llzk.Language.Core.Syntax.AST
import Std.Data.ExtTreeSet.Basic

/- This module defines the syntax of constraint systems over finite fields
   and boolean variables -/

namespace Llzk.FFConstraints.Basic

open Llzk.Language.Core.Syntax.AST

/- Metadata for FF variables -/
structure FFVarMetaData where
  orig_name : String
  src_info : SrcInfo
  deriving Repr, BEq, Inhabited, Ord

structure BoolVarMetaData where
  orig_name : String
  src_info : SrcInfo
  deriving Repr, BEq, Inhabited, Ord

/- A finite field variable -/
structure FFVar where
  id : ℕ
  meta_data: FFVarMetaData
  deriving Repr, BEq, Inhabited, Ord

/- A boolean variable -/
structure BoolVar where
  id : ℕ
  meta_data: BoolVarMetaData
  deriving Repr, BEq, Inhabited, Ord

/- A variable, which can be either a finite field variable or a boolean variable -/
abbrev Var := FFVar ⊕ BoolVar

/- When calling a macro we provide a value or a variable -/
inductive MacroCallParam (c : ZKConfig) where
  | var (v : Var) : MacroCallParam c
  | ff (t : FF c) : MacroCallParam c
  | bool (b : Bool) : MacroCallParam c
  deriving Repr, BEq, Inhabited

-- /-  Equality (BEq) of FFVar -/
-- instance : BEq FFVar where
--   beq a b := a.id == b.id &&
--   a.meta_data.orig_name == b.meta_data.orig_name &&
--   a.meta_data.src_info == b.meta_data.src_info

-- /-  Equality (BEq) of BoolVar -/
-- instance : BEq BoolVar where
--   beq a b := a.id == b.id &&
--   a.meta_data.orig_name == b.meta_data.orig_name &&
--   a.meta_data.src_info == b.meta_data.src_info

-- /- ToString instance for FFVar -/
-- instance : ToString FFVar where
--   toString v :=
--     s!"v_{v.id}_{v.meta_data.orig_name}_L{v.meta_data.src_info.row}_C{v.meta_data.src_info.col}"

-- /- ToString instance for BoolVar -/
-- instance : ToString BoolVar where
--   toString v :=
--     s!"v_{v.id}_{v.meta_data.orig_name}_L{v.meta_data.src_info.row}_C{v.meta_data.src_info.col}"

-- /-  Ordering (Ord) of FFVar. Needed if we use ordered sets -/
-- instance : Ord FFVar where
--   compare a b := compare (toString a) (toString b)

-- /-  Ordering (Ord) of BoolVar. Needed if we use ordered sets -/
-- instance : Ord BoolVar where
--   compare a b := compare (toString a) (toString b)

/-  Equality (BEq) of FFVar -/
--instance : BEq FFVar where
--  beq a b := a.id == b.id

/-  Equality (BEq) of BoolVar -/
--instance : BEq BoolVar where
--  beq a b := a.id == b.id

/- ToString instance for FFVar -/
instance : ToString FFVar where
  toString v := s!"v_{v.id}"

/- ToString instance for BoolVar -/
instance : ToString BoolVar where
  toString v := s!"v_{v.id}"

/-  Ordering (Ord) of FFVar. Needed if we use ordered sets -/
--instance : Ord FFVar where
--  compare a b := compareLex

/-  Ordering (Ord) of BoolVar. Needed if we use ordered sets -/
--instance : Ord BoolVar where
--  compare a b := compare a.id b.id

#check Std.TransCmp

instance : Std.TransCmp (compare (α := FFVar)) where
  isLE_trans := by
    intros a b c h_a_b h_b_c
    simp only [compare, instOrdFFVar.ord] at h_a_b
    cases h_comp_aid_bid : compareOfLessAndEq a.id b.id with
    | lt =>
      simp [h_comp_aid_bid] at h_a_b
      simp only [compare, instOrdFFVar.ord] at h_b_c
      cases h_comp_bid_cid : compareOfLessAndEq b.id c.id with
      | lt =>
        simp [h_comp_bid_cid] at h_b_c
        simp only [compare, instOrdFFVar.ord]
        rw [compareOfLessAndEq_eq_lt] at h_comp_aid_bid
        rw [compareOfLessAndEq_eq_lt] at h_comp_bid_cid
        have h_a_c : a.id < c.id := by grind
        rw [← compareOfLessAndEq_eq_lt] at h_a_c
        simp [h_a_c]
      | eq =>
        simp [h_comp_bid_cid] at h_b_c
        simp only [compare, instOrdFFVar.ord]
        rw [compareOfLessAndEq_eq_lt] at h_comp_aid_bid
        rw [compareOfLessAndEq_eq_eq] at h_comp_bid_cid
        · have h_a_c : a.id < c.id := by
            rw [← h_comp_bid_cid]
            exact h_comp_aid_bid
          rw [← compareOfLessAndEq_eq_lt] at h_a_c
          simp [h_a_c]
        · intros x
          apply Nat.le_refl
        · intros x y
          apply Nat.not_le
      | gt =>
        simp [h_comp_bid_cid] at h_b_c
    | eq =>
        · simp only [compare, instOrdFFVar.ord] at h_b_c
          simp only [h_comp_aid_bid, Ordering.then_eq, Ordering.eq_then] at h_a_b
          rw [compareOfLessAndEq_eq_eq] at h_comp_aid_bid
          · have h_meta_a_b := (@Ordering.isLE_iff_eq_lt_or_eq_eq
               (instOrdFFVarMetaData.ord a.meta_data b.meta_data)).mp h_a_b
            rcases h_meta_a_b with h_lt | h_eq
            · sorry
            · sorry
          · intros x
            apply Nat.le_refl
          · intros x y
            apply Nat.not_le
    | gt =>
        rw [h_comp_aid_bid, Ordering.then, Ordering.isLE] at h_a_b
        · contradiction
        · intros hh
          contradiction

  eq_swap {a b} := by
    simp only [compare, instOrdFFVar.ord, compareOfLessAndEq, instOrdFFVarMetaData.ord]
    by_cases h_aid_bid : a.id < b.id
    · simp only [h_aid_bid, ↓reduceIte, Ordering.then_eq, Ordering.lt_then]
      apply Nat.lt_le_asymm at h_aid_bid
      rw [Nat.le_iff_lt_or_eq] at h_aid_bid
      push_neg at h_aid_bid
      rcases h_aid_bid with ⟨h_aid_lt_bid, h_aid_neq_bid⟩
      apply Nat.le_lt_asymm at h_aid_lt_bid
      simp only [h_aid_lt_bid, ↓reduceIte]
      simp only [h_aid_neq_bid, ↓reduceIte, Ordering.gt_then, Ordering.swap_gt]
    · simp only [h_aid_bid, ↓reduceIte, Ordering.then_eq]
      by_cases h_aid_eq_bid : a.id = b.id
      · simp only [h_aid_eq_bid, ↓reduceIte, Ordering.eq_then, lt_self_iff_false]
        sorry
      · simp only [h_aid_eq_bid, ↓reduceIte, Ordering.gt_then]
        sorry

instance : Std.TransCmp (compare (α := BoolVar)) := by
  sorry

#check compareLex

#check compareOfLessAndEq_eq_eq
#check instOrdSrcInfo.compare
#check compareOfLessAndEq_eq_eq
#check compare_eq_iff_eq


instance : Std.LawfulEqCmp (compare (α := FFVar)) where
  eq_of_compare {a b} := by
    intros h
    cases a  with | mk id_a m_a =>
    cases b  with | mk id_b m_b =>
    cases m_a with | mk orig_a src_a =>
    cases m_b with | mk orig_b src_b =>
    simp only [compare, instOrdFFVar.ord, instOrdFFVarMetaData.ord,
      Ordering.then_eq, Ordering.then_eq_eq] at h
    rcases h with ⟨h_id, h_orig, h_src⟩
    rw [compareOfLessAndEq_eq_eq] at h_id
    · rw [compareOfLessAndEq_eq_eq] at h_orig
      · have h_eq : src_a = src_b := by
          simp only [instOrdSrcInfo.ord, Ordering.then_eq,
            Ordering.then_eq_eq, Std.LawfulEqCmp.compare_eq_iff_eq] at h_src
          cases src_a with | mk row_a col_a =>
          cases src_b with | mk row_b col_b =>
          simp only at h_src
          rcases h_src with ⟨h_row, h_col⟩
          rw [h_row, h_col]
        rw [h_id, h_orig, h_eq]
      · apply String.le_refl
      · apply String.not_le
    · intros x
      apply Nat.le_refl
    · intros x y
      apply Nat.not_le



instance : Std.LawfulEqCmp (compare (α := BoolVar)) where
  eq_of_compare {a b} := by
    intros h
    cases a  with | mk id_a m_a =>
    cases b  with | mk id_b m_b =>
    cases m_a with | mk orig_a src_a =>
    cases m_b with | mk orig_b src_b =>
    simp only [compare, instOrdBoolVar.ord, instOrdBoolVarMetaData.ord,
      Ordering.then_eq, Ordering.then_eq_eq] at h
    rcases h with ⟨h_id, h_orig, h_src⟩
    rw [compareOfLessAndEq_eq_eq] at h_id
    · rw [compareOfLessAndEq_eq_eq] at h_orig
      · have h_eq : src_a = src_b := by
          simp only [instOrdSrcInfo.ord, Ordering.then_eq,
            Ordering.then_eq_eq, Std.LawfulEqCmp.compare_eq_iff_eq] at h_src
          cases src_a with | mk row_a col_a =>
          cases src_b with | mk row_b col_b =>
          simp only at h_src
          rcases h_src with ⟨h_row, h_col⟩
          rw [h_row, h_col]
        rw [h_id, h_orig, h_eq]
      · apply String.le_refl
      · apply String.not_le
    · intros x
      apply Nat.le_refl
    · intros x y
      apply Nat.not_le


/-  Hashing (Hashable) of FFVar. Needed if we use this in a HashMap or HashSet -/
instance : Hashable FFVar where
  hash a := mixHash (hash a.id) (hash a.meta_data.orig_name)

/-  Hashing (Hashable) of BoolVar. Needed if we use this in a HashMap or HashSet -/
instance : Hashable BoolVar where
  hash a := mixHash (hash a.id) (hash a.meta_data.orig_name)



/- FFVar set -/
abbrev FFVarSet := Std.ExtTreeSet FFVar compare
abbrev emptyFFVarSet : FFVarSet := Std.ExtTreeSet.empty

-- FFVarSet has ⊆
instance : HasSubset FFVarSet where
  Subset s1 s2 := ∀ x, x ∈ s1 → x ∈ s2

/- BoolVar set -/
abbrev BoolVarSet := Std.ExtTreeSet BoolVar compare
abbrev emptyBoolVarSet : BoolVarSet := Std.ExtTreeSet.empty

-- BoolVarSet has ⊆
instance : HasSubset BoolVarSet where
  Subset s1 s2 := ∀ x, x ∈ s1 → x ∈ s2


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


-- FF vars in a FFFormula
mutual

def ffvarsTerm {c : ZKConfig} : FFTerm c → FFVarSet
  | .val _ => emptyFFVarSet
  | .var v => emptyFFVarSet.insert v
  | .add a b | .sub a b | .mul a b => (ffvarsTerm a).union (ffvarsTerm b)
  | .neg a => ffvarsTerm a
  | .ite cond t e => (ffvars cond).union ((ffvarsTerm t).union (ffvarsTerm e))

def ffvars {c : ZKConfig} : FFFormula c -> FFVarSet
  | .true | .false => emptyFFVarSet
  | .range t _ _ => ffvarsTerm t
  | .bool _ => emptyFFVarSet
  | .eq a b | .lt a b | .gt a b | .le a b | .ge a b => (ffvarsTerm a).union (ffvarsTerm b)
  | .and a b | .or a b | .imply a b | .iff a b => (ffvars a).union (ffvars b)
  | .not a => ffvars a
  | .ite cond t e => (ffvars cond).union ((ffvars t).union (ffvars e))
  | .call _ _ => emptyFFVarSet -- TODO

end


-- Bool vars in a FFFormula
mutual

def boolvarsTerm {c : ZKConfig} : FFTerm c → BoolVarSet
  | .val _ => emptyBoolVarSet
  | .var _ => emptyBoolVarSet
  | .add a b | .sub a b | .mul a b => (boolvarsTerm a).union (boolvarsTerm b)
  | .neg a => boolvarsTerm a
  | .ite cond t e => (boolvars cond).union ((boolvarsTerm t).union (boolvarsTerm e))

def boolvars {c : ZKConfig} : FFFormula c -> BoolVarSet
  | .true | .false => emptyBoolVarSet
  | .range t _ _ => boolvarsTerm t
  | .bool v => emptyBoolVarSet.insert v
  | .eq a b | .lt a b | .gt a b | .le a b | .ge a b => (boolvarsTerm a).union (boolvarsTerm b)
  | .and a b | .or a b | .imply a b | .iff a b => (boolvars a).union (boolvars b)
  | .not a => boolvars a
  | .ite cond t e => (boolvars cond).union ((boolvars t).union (boolvars e))
  | .call _ _ => emptyBoolVarSet -- TODO

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


/- A macro is a named formula with parameters -/
structure FFMacro (c : ZKConfig) where
  name : String
  params : List Var
  body : FFFormula c
  deriving Repr, BEq, Inhabited

/- A constraint system consists of a list of macros and the name of the main macro -/
structure FFConstraintSystem (c : ZKConfig) where
  macros : List (FFMacro c)
  main : String
  deriving Repr, BEq, Inhabited

/-- Fetch a macro by name from a list of macros. Throws an error if
    the macro is not found. -/
def fetchMacro {c : ZKConfig}
    (ms : List (FFMacro c)) (name : String) : Except String (FFMacro c × List (FFMacro c)) :=
  match ms with
  | [] => Except.error s!"Macro {name} not found"
  | m :: rest =>
      if m.name == name then Except.ok (m, rest)
      else fetchMacro rest name

/- fetchMacro returns a smaller list of macros -/
theorem fetchMacroLT {c : ZKConfig} (ms ms' : List (FFMacro c)) (name : String) (m : FFMacro c) :
  fetchMacro ms name = Except.ok (m, ms') → ms'.length < ms.length := by
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
        have h2 := fetchMacroLT tail ms' name m h1
        grind

/- The main formula of a constraint system is a call to the main macro -/
def mainFormula {c : ZKConfig}
  (sys : FFConstraintSystem c) : Except String (FFFormula c × List Var) := do
  let (m,_) ← fetchMacro sys.macros sys.main
  let params : List (MacroCallParam c) := m.params.map (fun var => (.var var))
  return (FFFormula.call m.name params, m.params)

end Llzk.FFConstraints.Basic
