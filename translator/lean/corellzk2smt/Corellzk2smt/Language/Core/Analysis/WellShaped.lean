import Corellzk2smt.Basic
import Corellzk2smt.Config
import Corellzk2smt.Language.Core.Syntax.AST
import Corellzk2smt.Language.Core.Semantics.Basic
import Corellzk2smt.Language.Core.Semantics.BigStep

/- `WellShapedCom`/`WellShapedCmds` originally captured a handful of semantic well-formedness
   preconditions a command tree needs for symbolic execution's correctness proof to go through --
   things that, at first glance, looked like genuine assumptions about the *program* (not checkable
   by the language's weak static typing, see `DefinedVars.lean`), needed alongside a successful
   `seCmd`/`seCmds`/`seIfStmt`/`seFuncCall` run.

   As of 2026, EVERY one of those conjuncts has turned out to be unnecessary -- each one is either
   already forced by the symbolic execution having succeeded (readable straight back out of that
   success), or by a whole-program invariant that's cheap to thread and discharge once, elsewhere.
   `WellShapedCom`/`WellShapedCmds` are consequently now pure structural recursion with no
   remaining side condition at all (`if_stmt`/`loop_exp`/`loop` just recurse into their sub-lists;
   everything else, including `func_call`, is `True`) -- i.e. every command tree is trivially
   well-shaped. The predicate is kept (rather than deleted outright) only because it's still
   threaded through every proof in `SymExec/PartialCorrectness/*` as a formal parameter; nothing
   about its *content* does any work anymore.

   What each removed conjunct was, and why it turned out unnecessary:
   - `if`-statement branches used to require both branches to always succeed from any environment
     and agree in shape on every output variable. Not read off `seIfStmt`'s own success via
     `evalFormula`/`evalCmd`-level unfolding, but one level *deeper* -- `mergeSymValue`
     (`SymExec/BigStep.lean`) is what actually enforces shape agreement while merging two symbolic
     values, and its own error cases *are* `sameShape`'s `False` cases exactly (array-size-mismatch,
     scalar/array cross-mismatch) -- so `mergeSymEnv`'s success (itself forced by `seIfStmt`'s
     success, since `mergeIfBranches` fails whenever `mergeSymEnv` does) already proves the
     shape-agreement fact `seIfStmt_correct` needs, with no reference to any concrete environment.
   - `loop_exp` used to require its repetition count be a syntactic literal (`SimpleExpr.val`).
     `tryEvalSimpleExprToFFValue` resolving `rep` to *some* value under `symEnv`, together with
     `tryEvalSimpleExprToFFValue_correct` (`SymExec/Lemmas.lean` -- a `.const` symbolic binding
     forces the matching concrete env to hold exactly that value, via `EnvMatches`), gives
     everything needed without assuming anything about `rep`'s syntax up front.
   - `if`-statement conditions used to require `evalCond` be defined on every concrete environment.
     In `seIfStmt_correct`'s "condition doesn't constant-fold" branch, `encodeCond symEnv cond`
     succeeding is *already* forced by `seIfStmt`'s own success (`mergeIfBranches` fails whenever
     `encodeCond` does), extractable directly from the success hypothesis.
   - `func_call` sites used to require: `outs.Nodup` (unnecessary -- `EnvMatches_setVars`,
     `SymExec/FuncCallCorrectness.lean`, preserves `EnvMatches` across a repeated-`outs` call fine,
     since concrete/symbolic `setVars` both recurse over `outs` in the same left-to-right order, so
     a repeat resolves to "last write wins" identically on both sides); `args.length =
     params.length` and "arguments always concretely defined and shape-matched" (both unnecessary
     -- `flattenArgVals`'s own definition, `SymExec/BigStep.lean`, fails on a length mismatch and
     its error cases *are* `symValueMatchesType`'s cases, so `seFuncCall_correct` reads both facts
     straight back out of `seFuncCall`'s own success); the named function actually existing in the
     (remaining) program (unnecessary -- see below); and `outs.length = rets.length` arity against
     that function's actual signature (unnecessary too, once existence is -- see below).

   The last two (existence, arity) are the subtlest, since neither is readable off `seFuncCall`
   succeeding *at the call site itself* the way the others are: `H_funcCall`, the hypothesis
   `seCmd_correct`'s `.func_call` case discharges from this, has to hold *before* any success is
   known (its own conclusion, `TranslatesCorrectly`, is itself conditioned on a future success).
   Both are instead derived from whole-program invariants threaded as two new hypotheses,
   `hspecs_cover`/`hspecs_rets_cover`, added everywhere `WellShapedCom`/`H_funcCall` used to be
   consumed (`seCmd_correct`/`seCmds_correct`/`seIfStmt_correct`, `seFunc_correct` and friends, and
   the `seCmd_names_below`/`seCmds_names_below`/`seIfStmt_names_below` family in
   `SymExec/Correctness.lean`):
   - `hspecs_cover : ∀ fname', fname' ∈ specs.map (·.name) → fname' ∈ p.map funcWithMDName` --
     every function whose spec has already been accumulated into `specs` really is a function of
     the (remaining) program.
   - `hspecs_rets_cover : ∀ fname' fspec, fetchFuncSpec specs fname' = Except.ok fspec → ∀ md func
     p', fetchFunc p fname' = Except.ok (...) → fspec.rets.length = (func's own rets).length` --
     whenever a spec and the concrete function it names both resolve, their return-arity agrees.

   `seCmd_correct`'s `.func_call` case derives both by casing on `fetchFuncSpec specs fname` (a
   plain, non-monadic first step of `seFuncCall`'s definition, decidable independent of the
   surrounding success): if it errors, `seFuncCall` inherits the error and the goal is vacuous; if
   it succeeds with some `fspec`, `fetchFuncSpec_sound` (`SymExec/Correctness.lean`) gives `fname ∈
   specs.map (·.name)`, `hspecs_cover` lifts that to `fname ∈ p.map funcWithMDName`, and
   `fetchFunc_of_mem` (`Language/Core/Syntax/AST.lean`) turns that membership into the actual
   `fetchFunc` witness; a second unfold of the same success (through `resolveSimpleExprsToSymValue`/
   `flattenArgVals`/`mintFreshRets`/`setVars`, using the new `setVars_length_of_ok`,
   `SymExec/FuncCallCorrectness.lean`) gives `outs.length = fspec.rets.length`, and
   `hspecs_rets_cover` bridges that to the concrete function's own `rets.length`. Both new
   hypotheses are discharged, with no deep new proof content, at `seExecFuncs_loop_correct`'s level
   (`SymExec/PartialCorrectness/ProgCorrectness.lean`): `hspecs_cover` directly from the
   already-proven `hnames_corr : specs.map (·.name) = donePart.map funcWithMDName` (an equality,
   hence trivially a one-directional membership implication too); `hspecs_rets_cover` by a small
   induction mirroring `hnames_corr`'s own threading, using `seFunc_eq_shape`'s `hrets_eq : fspec.
   rets = rets` (a purely structural fact about `seFunc`'s own construction, no execution needed)
   for the newly-added function at each step, and the inherited old `hspecs_rets_cover` fact
   (via `fetchFuncSpec_prepend_indep`/`fetchFunc_skip_ne`) for every function already accumulated.
-/

namespace Corellzk2smt.Language.Core.Analysis.WellShaped

open Corellzk2smt.Config
open Corellzk2smt.Language.Core.Syntax.AST
open Corellzk2smt.Language.Core.Semantics.Basic
open Corellzk2smt.Language.Core.Semantics.BigStep

mutual

def WellShapedCom {c : ZKConfig} (gconf : GlobalConfig c) (p : Prog c) (cmd : Com c) : Prop :=
  match cmd with
  | .if_stmt _cond tb eb => WellShapedCmds gconf p tb ∧ WellShapedCmds gconf p eb
  | .loop_exp _rep body => WellShapedCmds gconf p body
  | .loop _rep body => WellShapedCmds gconf p body
  | _ => True

def WellShapedCmds {c : ZKConfig} (gconf : GlobalConfig c) (p : Prog c)
    (cmds : List (ComWithMD c)) : Prop :=
  match cmds with
  | [] => True
  | i :: rest =>
    match i with
    | .mk _ cmd => WellShapedCom gconf p cmd ∧ WellShapedCmds gconf p rest

end

-- `funcWithMDName`/`funcWithMDBody` now live in `Language/Core/Syntax/AST.lean` (needed there
-- too, by `hasDupFuncNames`), and are available here via the `AST` import/open above.

/-- A whole program is well-shaped: every function's body is `WellShapedCmds` against exactly the
    remainder `fetchFunc` would give it (i.e. every function-body's `p'` parameter throughout this
    program is really the tail *right after* that function -- matching `fetchFunc`'s own
    remainder semantics, since a function's own name being unique within the whole program
    (enforced by the second conjunct below) means `fetchFunc` on the whole list finds it right at
    the head), together with global function-name uniqueness (a function's name never recurs among
    the functions after it -- combined recursively, this gives uniqueness across the whole
    program). Needed so that `seExecFuncs_correct`'s `specs` accumulator can invoke
    `TranslatesCorrectly_prepend` at each step: a newly-added function's name is disjoint from
    every spec already built for the functions after it. -/
def WellShapedProg {c : ZKConfig} (gconf : GlobalConfig c) (p : Prog c) : Prop :=
  match p with
  | [] => True
  | f :: rest =>
      WellShapedCmds gconf rest (funcWithMDBody f) ∧
      (∀ f' ∈ rest, funcWithMDName f' ≠ funcWithMDName f) ∧
      WellShapedProg gconf rest

-- `seExecFuncs`'s `loop` processes a program back-to-front (via `p.reverse`), so at the point it
-- reaches a given function `x`, the relevant program (for `fetchFunc`/`WellShapedProg` purposes)
-- decomposes as `A ++ (x :: B)` -- `A` the functions processed *before* `x` in loop order (i.e.
-- *after* `x` in the original list, already irrelevant to `x` itself), and `B` the functions not
-- yet reached (i.e. genuinely after `x`, the ones its body may call into). This extracts exactly
-- what's needed for `x` at that point from the whole `WellShapedProg` fact -- including `x`'s
-- name being disjoint from *both* `A` and `B` (full pairwise uniqueness, needed so `fetchFunc`
-- on the combined list actually finds `x` at its true position with remainder `B`), without
-- needing to unfold `WellShapedProg`'s own recursion at `x`'s exact position (which the
-- definition can't do directly, since it always peels from the head) -- by induction on `A`.
theorem WellShapedProg_head_after_prefix {c : ZKConfig} (gconf : GlobalConfig c) :
    ∀ (A B : Prog c) (x : FuncWithMD c),
      WellShapedProg gconf (A ++ (x :: B)) →
      WellShapedCmds gconf B (funcWithMDBody x) ∧
      (∀ f ∈ B, funcWithMDName f ≠ funcWithMDName x) ∧
      (∀ f ∈ A, funcWithMDName f ≠ funcWithMDName x) := by
  intro A
  induction A with
  | nil =>
      intro B x h
      simp only [List.nil_append, WellShapedProg] at h
      exact ⟨h.1, h.2.1, fun f hf => absurd hf (List.not_mem_nil)⟩
  | cons a A' ih =>
      intro B x h
      simp only [List.cons_append, WellShapedProg] at h
      obtain ⟨_, hadisj, hrest⟩ := h
      obtain ⟨hshaped, hBdisj, hA'disj⟩ := ih B x hrest
      refine ⟨hshaped, hBdisj, fun f hf => ?_⟩
      rcases List.mem_cons.mp hf with hf | hf
      · have hxa : funcWithMDName x ≠ funcWithMDName a :=
          hadisj x (List.mem_append_right A' (List.mem_cons_self ..))
        rw [hf]
        exact fun heq => hxa heq.symm
      · exact hA'disj f hf

end Corellzk2smt.Language.Core.Analysis.WellShaped
