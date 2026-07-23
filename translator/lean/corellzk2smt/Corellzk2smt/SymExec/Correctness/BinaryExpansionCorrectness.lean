import Corellzk2smt.Config
import Corellzk2smt.FFConstraints.Basic
import Corellzk2smt.FFConstraints.Satisfiability
import Corellzk2smt.SymExec.Basic

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

end Corellzk2smt.SymExec.Correctness.BinaryExpansionCorrectness
