import Corellzk2smt.Config
import Corellzk2smt.FFConstraints.Basic
import Corellzk2smt.FFConstraints.Satisfiability
import Corellzk2smt.SymExec.Basic
import Corellzk2smt.SymExec.BinaryExpansion
import Corellzk2smt.Language.Core.Semantics.Basic
import Corellzk2smt.FFConstraints.Lemmas

/-!
Correctness of a variable's binary representation (`FFVarWithBinRep.bits`, `SymExec/Basic.lean`)
-- the ground-truth relation an emitted `BinRep(x, bits_of_x)` formula is meant to guarantee,
needed to let `TranslatesCorrectly` carry a "these bits are correct" context forward from the step
that minted them to any later step that just reuses them without re-asserting it. `BinRep` itself
just builds the formula (a purely term-level construction of `x`/`bitsOfX`, no assignment/macros
needed to build it); `ValidBinRep*` below is what actually evaluates it against an
assignment/macro list to check it holds. Left as `FFFormula.true` for now (deliberately, per the
incremental plan) -- filled in with the real term structure once `SymExec/BinaryExpansion.lean`'s
encoding itself is written.
-/

namespace Corellzk2smt.SymExec.Correctness.BinaryExpansionCorrectness

open Corellzk2smt.Config
open Corellzk2smt.FFConstraints.Basic
open Corellzk2smt.FFConstraints.Satisfiability
open Corellzk2smt.SymExec.Basic
open Corellzk2smt.SymExec.BinaryExpansion
open Corellzk2smt.Language.Core.Semantics.Basic
open Corellzk2smt.FFConstraints.Lemmas

/-- The formula whose satisfiability is exactly "`bitsOfX` is `x`'s correct binary representation
    (least-significant bit first): `x` is the weighted sum of `bitsOfX`, each of which is itself 0
    or 1." `TODO`: fill in the real definition once `SymExec/BinaryExpansion.lean` is written. -/
def BinRep {c : ZKConfig} (_gconf : GlobalConfig c) (_x : FFTerm c)
    (_bitsOfX : List (FFTerm c)) : FFFormula c :=
  FFFormula.true

/-- Whichever binary representation `sv` itself carries (if any) is a correct one for its own
    variable, under `assignment` -- vacuously `True` for a `.const` (nothing to check) or an
    as-yet-uncomputed/decided-unneeded `.bits`. `BinRep`'s formula is evaluated against an empty
    macro list: a binary-representation formula is purely local arithmetic over `x`/`bitsOfX`,
    never a macro call. -/
def ValidBinRepSimple {c : ZKConfig} (gconf : GlobalConfig c) (assignment : Assignment c)
    (sv : SimpleSymVal c) : Prop :=
  match sv with
  | .const _ => True
  | .ffvar vbr =>
    match vbr.bits with
    | some bs =>
        evalFormula gconf assignment (BinRep gconf (FFTerm.var vbr.var) bs) [] = Except.ok true
    | none => True

/-- `ValidBinRepSimple`, lifted to a full `SymValue` -- pointwise over every element for an
    array, matching `symValMatches`'s own `.simple`/`.array` case split. -/
def ValidBinRepValue {c : ZKConfig} (gconf : GlobalConfig c) (assignment : Assignment c)
    (v : SymValue c) : Prop :=
  match v with
  | .simple sv => ValidBinRepSimple gconf assignment sv
  | .array arr => ∀ sv ∈ arr, ValidBinRepSimple gconf assignment sv

/-- `ctx` correctly accounts for every binary representation currently memoized in `symEnv`: any
    assignment satisfying `ctx` already guarantees every entry's own binary representation, if it
    has one (including array elements), is a correct one. This is the invariant
    `TranslatesCorrectly` will carry forward as its `ctx` parameter -- established as
    `FFFormula.true` at the start of a function body (no bits memoized yet), and strengthened to
    `ctx.and spec.f` after each step that succeeds. `ctx` itself is evaluated against an empty
    macro list, same reason as `ValidBinRepSimple`. -/
def ValidBinRep {c : ZKConfig} (gconf : GlobalConfig c) (ctx : FFFormula c) (symEnv : SymEnv c) :
    Prop :=
  ∀ (assignment : Assignment c), evalFormula gconf assignment ctx [] = Except.ok true →
    ∀ id v, symEnv.get? id = some v → ValidBinRepValue gconf assignment v

-- ---------------------------------------------------------------------------
-- A value with no memoized bits trivially satisfies `ValidBinRep*`, for any context
-- ---------------------------------------------------------------------------

/-- `sv` carries no binary representation yet: either a constant (nothing to check, ever) or an
    `.ffvar` whose `bits` hasn't been computed. -/
def SimpleSymValNoBits {c : ZKConfig} (sv : SimpleSymVal c) : Prop :=
  match sv with
  | .const _ => True
  | .ffvar vbr => vbr.bits = none

/-- `SimpleSymValNoBits`, lifted to a full `SymValue` -- pointwise over every element for an
    array, matching `ValidBinRepValue`'s own case split. -/
def SymValueNoBits {c : ZKConfig} (v : SymValue c) : Prop :=
  match v with
  | .simple sv => SimpleSymValNoBits sv
  | .array arr => ∀ sv ∈ arr, SimpleSymValNoBits sv

/-- A `SimpleSymVal` with no memoized bits trivially satisfies `ValidBinRepSimple`, for any
    assignment -- there is nothing yet to check. -/
theorem ValidBinRepSimple_of_noBits {c : ZKConfig} (gconf : GlobalConfig c)
    (assignment : Assignment c) (sv : SimpleSymVal c) (h : SimpleSymValNoBits sv) :
    ValidBinRepSimple gconf assignment sv := by
  cases sv with
  | const _ => trivial
  | ffvar vbr =>
      simp only [SimpleSymValNoBits] at h
      simp only [ValidBinRepSimple, h]

/-- `ValidBinRepSimple_of_noBits`, lifted to a full `SymValue`. -/
theorem ValidBinRepValue_of_noBits {c : ZKConfig} (gconf : GlobalConfig c)
    (assignment : Assignment c) (v : SymValue c) (h : SymValueNoBits v) :
    ValidBinRepValue gconf assignment v := by
  cases v with
  | simple sv => exact ValidBinRepSimple_of_noBits gconf assignment sv h
  | array arr =>
      intro sv hsv
      exact ValidBinRepSimple_of_noBits gconf assignment sv (h sv hsv)

/-- A symbolic environment none of whose entries carry any memoized bits yet satisfies
    `ValidBinRep` for *any* context -- there is nothing yet for any context to have to account
    for. In particular this holds for `ctx := FFFormula.true`, which is exactly the context a
    function body starts translation with. -/
theorem ValidBinRep_of_noBits {c : ZKConfig} (gconf : GlobalConfig c) (ctx : FFFormula c)
    (symEnv : SymEnv c) (h : ∀ id v, symEnv.get? id = some v → SymValueNoBits v) :
    ValidBinRep gconf ctx symEnv := by
  intro assignment _hctx id v hv
  exact ValidBinRepValue_of_noBits gconf assignment v (h id v hv)

-- ---------------------------------------------------------------------------
-- `ValidBinRep` is, as of today, unconditionally true -- `BinRep` is still the placeholder
-- `FFFormula.true`, and `evalFormula`'s `.true` case is `Except.ok true` regardless of the
-- assignment, so `ValidBinRepSimple`'s `some bs` branch holds no matter what `bs` actually is.
-- This will stop being true once `BinRep` gets its real definition -- every call site below
-- should be revisited then.
-- ---------------------------------------------------------------------------

/-- `ValidBinRepSimple` holds for *any* `sv`/`assignment`, as of today -- see the section header
    above. -/
theorem ValidBinRepSimple_trivial {c : ZKConfig} (gconf : GlobalConfig c)
    (assignment : Assignment c) (sv : SimpleSymVal c) : ValidBinRepSimple gconf assignment sv := by
  cases sv with
  | const _ => trivial
  | ffvar vbr =>
      simp only [ValidBinRepSimple]
      cases vbr.bits with
      | none => trivial
      | some bs => simp [BinRep, evalFormula]

/-- `ValidBinRepValue_trivial`, lifted from `ValidBinRepSimple_trivial`. -/
theorem ValidBinRepValue_trivial {c : ZKConfig} (gconf : GlobalConfig c)
    (assignment : Assignment c) (v : SymValue c) : ValidBinRepValue gconf assignment v := by
  cases v with
  | simple sv => exact ValidBinRepSimple_trivial gconf assignment sv
  | array arr => intro sv _hsv; exact ValidBinRepSimple_trivial gconf assignment sv

/-- `ValidBinRep` holds for *any* `ctx`/`symEnv`, as of today -- see the section header above.
    The one-line discharge every new `ValidBinRep` proof obligation introduced by threading `ctx`
    through `TranslatesCorrectly` can use, until `BinRep` gets its real definition. -/
theorem ValidBinRep_trivial {c : ZKConfig} (gconf : GlobalConfig c) (ctx : FFFormula c)
    (symEnv : SymEnv c) : ValidBinRep gconf ctx symEnv := by
  intro assignment _hctx id v _hv
  exact ValidBinRepValue_trivial gconf assignment v

-- ---------------------------------------------------------------------------
-- `bool_ffterm` (`SymExec/BinaryExpansion.lean`) -- "this term's value is 0 or 1," under whichever
-- of the two encoding schemes (`.range`/`.mul`) `gconf.sym_exec.boolFFVarScm` selects. Proven once
-- here, generally, so every `seExprXXX_correct` that mints a fresh boolean-tagged var (starting
-- with `seExprEq`, and eventually every other `BoolExpr`/`BitwiseExpr` operator) can cite it
-- instead of re-deriving it per operator/per scheme.
-- ---------------------------------------------------------------------------

/-- Pure field-arithmetic core of the `.range` scheme: `0 ≤ toSigned x ≤ 1` holds exactly for the
    two field elements `0`/`1` themselves -- `x` in the "positive half" (`x.val < midpoint`) forces
    `x.val ≤ 1` (hence `x = 0` or `x = 1` by `.val` injectivity), while `x` in the "negative half"
    makes `toSigned x` itself negative, contradicting `0 ≤ toSigned x`. -/
theorem bool_ffterm_range_iff {c : ZKConfig} (x : FF c) :
    (toSigned (0 : FF c) ≤ toSigned x ∧ toSigned x ≤ toSigned (1 : FF c)) ↔ (x = 0 ∨ x = 1) := by
  have hmid2 : 2 ≤ c.midpoint := by
    have := c.midpoint_ok; have := c.p_prime.two_le; omega
  have h0val : (0 : FF c).val = 0 := ZMod.val_zero
  haveI : Fact (1 < c.p) := ⟨c.p_prime.one_lt⟩
  have h1val : (1 : FF c).val = 1 := ZMod.val_one c.p
  have h0signed : toSigned (0 : FF c) = 0 := by
    have hh : (0 : FF c).val < c.midpoint := by rw [h0val]; omega
    simp only [toSigned, hh, if_true]
    simp [h0val]
  have h1signed : toSigned (1 : FF c) = 1 := by
    have hh : (1 : FF c).val < c.midpoint := by rw [h1val]; omega
    simp only [toSigned, hh, if_true]
    simp [h1val]
  rw [h0signed, h1signed]
  by_cases hlt : x.val < c.midpoint
  · have hxsigned : toSigned x = (x.val : Int) := by
      simp only [toSigned, hlt, if_true]
    rw [hxsigned]
    constructor
    · rintro ⟨_, h1⟩
      have hxval1 : x.val ≤ 1 := by exact_mod_cast h1
      interval_cases hv : x.val
      · exact Or.inl ((ZMod.val_eq_zero x).mp hv)
      · exact Or.inr (ZMod.val_injective c.p (by rw [hv, h1val]))
    · rintro (rfl | rfl) <;> simp [h0val, h1val]
  · have hxsigned : toSigned x = (x.val : Int) - c.p := by
      simp only [toSigned, if_neg hlt]
    have hxlt : x.val < c.p := ZMod.val_lt x
    have hxge : c.midpoint ≤ x.val := by omega
    apply iff_of_false
    · rintro ⟨h0, _⟩
      rw [hxsigned] at h0
      have : (x.val : Int) < c.p := by exact_mod_cast hxlt
      omega
    · rintro (rfl | rfl)
      · rw [h0val] at hxge; omega
      · rw [h1val] at hxge; omega

/-- Pure field-arithmetic core of the `.mul` scheme: the classic boolean gadget `x*(1-x) = 0` holds
    exactly for `x = 0`/`x = 1` -- a field has no zero divisors, so the product vanishes only when
    one of its two factors does. -/
theorem bool_ffterm_mul_iff {c : ZKConfig} (x : FF c) :
    x * (1 - x) = 0 ↔ (x = 0 ∨ x = 1) := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1).symm
  · rintro (rfl | rfl) <;> ring

/-- `bool_ffterm gconf sconf (FFTerm.var n)` never rejects a variable -- the `.val`-only failure
    case (`SymExec/BinaryExpansion.lean`) can't trigger since `FFTerm.var n` never matches `.val`,
    so the wildcard branch always fires and always returns `Except.ok`. Every call site that mints
    a fresh var (as every `seExprXXX` does) can use this to discharge `bool_ffterm`'s error branch
    without inspecting the scheme itself. -/
theorem bool_ffterm_var_isOk {c : ZKConfig} (gconf : GlobalConfig c) (sconf : SymExecConfig c)
    (n : FFVar) : ∃ f, bool_ffterm gconf sconf (FFTerm.var n) = Except.ok f := by
  simp only [bool_ffterm]
  cases gconf.sym_exec.boolFFVarScm <;> exact ⟨_, rfl⟩

/-- `bool_ffterm gconf sconf (FFTerm.var n)`, whenever it succeeds with some `f`, is satisfied by
    `assignment` iff `n`'s value under `assignment` really is `0` or `1` -- regardless of which of
    the two encoding schemes `gconf` picks. This is the one fact every call site needs: it lets a
    proof construct/consume the boolean-tag conjunct purely in terms of the variable's value,
    without ever case-splitting on `gconf.sym_exec.boolFFVarScm` itself. -/
theorem evalFormula_bool_ffterm_var_iff {c : ZKConfig} (gconf : GlobalConfig c)
    (sconf : SymExecConfig c) (assignment : Assignment c) (ms : List (FFMacro c)) (n : FFVar)
    (f : FFFormula c) (hf : bool_ffterm gconf sconf (FFTerm.var n) = Except.ok f) :
    evalFormula gconf assignment f ms = Except.ok true ↔
      (assignment.ff n = 0 ∨ assignment.ff n = 1) := by
  cases hscm : gconf.sym_exec.boolFFVarScm with
  | range =>
      simp only [bool_ffterm, hscm] at hf
      injection hf with hf
      subst hf
      have hrange : evalFormula gconf assignment (FFFormula.range (FFTerm.var n) 0 1) ms
            = Except.ok true ↔
          toSigned (0 : FF c) ≤ toSigned (assignment.ff n) ∧
            toSigned (assignment.ff n) ≤ toSigned (1 : FF c) := by
        simp only [evalFormula, evalTerm]
        by_cases h1 : toSigned (0 : FF c) ≤ toSigned (assignment.ff n) <;>
          by_cases h2 : toSigned (assignment.ff n) ≤ toSigned (1 : FF c) <;>
          simp [evalLe, h1, h2]
      rw [hrange]
      exact bool_ffterm_range_iff (assignment.ff n)
  | mul =>
      simp only [bool_ffterm, hscm] at hf
      injection hf with hf
      subst hf
      simp only [evalFormula, evalTerm, Except.ok.injEq, beq_iff_eq]
      exact bool_ffterm_mul_iff (assignment.ff n)

/-- `bool_ffterm gconf sconf (FFTerm.var n)`, whenever it succeeds with some `f`, has `n` as its
    only FF-variable -- true under either scheme (`.range` mentions only the term it's given;
    `.mul`'s `x*(1-x)=0` mentions `x` twice but introduces nothing new). -/
theorem mem_ffVarsOfFormula_bool_ffterm_var {c : ZKConfig} (gconf : GlobalConfig c)
    (sconf : SymExecConfig c) (n : FFVar) (f : FFFormula c)
    (hf : bool_ffterm gconf sconf (FFTerm.var n) = Except.ok f) (v' : Var) :
    v' ∈ ffVarsOfFormula f ↔ Var.ffv n = v' := by
  cases hscm : gconf.sym_exec.boolFFVarScm with
  | range =>
      simp only [bool_ffterm, hscm] at hf
      injection hf with hf
      subst hf
      simp [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_insert, Std.TreeSet.mem_union_iff,
        Std.TreeSet.not_mem_emptyc, or_self]
  | mul =>
      simp only [bool_ffterm, hscm] at hf
      injection hf with hf
      subst hf
      simp [ffVarsOfFormula, ffVarsOfTerm, Std.TreeSet.mem_insert, Std.TreeSet.mem_union_iff,
        Std.TreeSet.not_mem_emptyc, or_self]

/-- `bool_ffterm gconf sconf (FFTerm.var n)`, whenever it succeeds with some `f`, never mentions a
    bool-typed variable -- it's built entirely out of FF-level arithmetic/comparison, under either
    scheme. -/
theorem not_mem_bVarsOfFormula_bool_ffterm_var {c : ZKConfig} (gconf : GlobalConfig c)
    (sconf : SymExecConfig c) (n : FFVar) (f : FFFormula c)
    (hf : bool_ffterm gconf sconf (FFTerm.var n) = Except.ok f) (v' : Var) :
    v' ∉ bVarsOfFormula f := by
  cases hscm : gconf.sym_exec.boolFFVarScm with
  | range =>
      simp only [bool_ffterm, hscm] at hf
      injection hf with hf
      subst hf
      simp [bVarsOfFormula, bVarsOfTerm, Std.TreeSet.mem_union_iff, Std.TreeSet.not_mem_emptyc]
  | mul =>
      simp only [bool_ffterm, hscm] at hf
      injection hf with hf
      subst hf
      simp [bVarsOfFormula, bVarsOfTerm, Std.TreeSet.mem_union_iff, Std.TreeSet.not_mem_emptyc]

/-- `bool_ffterm gconf sconf (FFTerm.var n)`, whenever it succeeds with some `f`, never calls any
    macro (under either scheme, it's built entirely out of local FF arithmetic/comparison) -- so
    it can never mention `badName`, whatever `badName` is. -/
theorem FormulaNamesBelow_bool_ffterm_var {c : ZKConfig} (gconf : GlobalConfig c)
    (sconf : SymExecConfig c) (n : FFVar) (f : FFFormula c)
    (hf : bool_ffterm gconf sconf (FFTerm.var n) = Except.ok f) (badName : String) :
    FormulaNamesBelow f badName := by
  cases hscm : gconf.sym_exec.boolFFVarScm with
  | range =>
      simp only [bool_ffterm, hscm] at hf
      injection hf with hf
      subst hf
      simp [FormulaNamesBelow, TermNamesBelow]
  | mul =>
      simp only [bool_ffterm, hscm] at hf
      injection hf with hf
      subst hf
      simp [FormulaNamesBelow, TermNamesBelow]

end Corellzk2smt.SymExec.Correctness.BinaryExpansionCorrectness
