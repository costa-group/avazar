import Corellzk2smt.Basic
import Corellzk2smt.Config
import Corellzk2smt.Language.Core.Syntax.AST
import Corellzk2smt.Language.Core.Semantics.Basic
import Corellzk2smt.Language.Core.Semantics.BigStep

/- A program is "well-shaped" when:
   (a) [REMOVED 2026 -- see below] `if`-statement branches used to additionally require both
       branches to always succeed from any environment and agree in shape on every output
       variable. Also turned out to be unnecessary, but for a different reason than (b)/(c): it
       isn't read straight off `seIfStmt`'s own success in the "condition doesn't fold" branch
       via `evalFormula`/`evalCmd`-level unfolding, but one level *deeper* -- `mergeSymValue`
       (`SymExec/BigStep.lean`) is the thing that actually enforces shape agreement while merging
       two symbolic values, and its own cases *are* `sameShape`'s cases (array-size-mismatch and
       scalar/array-mismatch both error, matching `sameShape`'s `False` cases exactly) -- so
       `mergeSymEnv`'s success (itself forced by `seIfStmt`'s success, since `mergeIfBranches`
       fails whenever `mergeSymEnv` does) already proves the shape-agreement fact `seIfStmt_correct`
       needs for its own merge, with no reference to any concrete environment at all;
   (b) [REMOVED 2026 -- see below] `loop_exp` used to additionally require its repetition count
       be a syntactic literal (`SimpleExpr.val`); that turned out to be unnecessary.
       `seCmd_correct`'s `.loop_exp` case no longer needs it: `tryEvalSimpleExprToFFValue`
       resolving `rep` to *some* value under `symEnv` already, together with
       `tryEvalSimpleExprToFFValue_correct` (`SymExec/Lemmas.lean` -- a `.const` symbolic binding
       forces the matching concrete env to hold exactly that value, via `EnvMatches`), gives
       everything needed to show the concrete side resolves `rep` to the *same* value, without
       assuming anything about `rep`'s syntax up front;
   (c) [REMOVED 2026 -- see below] `if`-statement conditions used to additionally require
       `evalCond` be defined on every concrete environment; also turned out to be unnecessary, for
       the same reason as (b): in `seIfStmt_correct`'s "condition doesn't constant-fold" branch,
       `encodeCond symEnv cond` succeeding is *already* forced by `seIfStmt`'s own success (it
       fails via `mergeIfBranches` whenever `encodeCond` does), so it can be extracted directly
       from the success hypothesis instead of assumed up front via `encodeCond_defined`; and
   (d) [REMOVED 2026 -- see below] `func_call` sites used to additionally require the named
       function to actually exist in the (remaining) program (`∃ md func p', fetchFunc p fname =
       Except.ok (...) ∧ ...`) -- that existence part also turned out to be unnecessary, leaving
       only the arity fact (`outs.length = rets.length`, now phrased as a plain conditional:
       `∀ md func p', fetchFunc p fname = Except.ok (...) → outs.length = rets.length`, since
       there's no longer an existence witness to hang an existential on). The elimination doesn't
       come from `seFuncCall` succeeding *at this call site* (unlike (a)-(c) -- `H_funcCall`,
       the hypothesis `seCmd_correct`'s `.func_call` case discharges from this, has to hold before
       any success is known, since its own conclusion is itself conditioned on success). Instead
       it comes from a *whole-program* invariant threaded in as a new hypothesis, `hspecs_cover :
       ∀ fname', fname' ∈ specs.map (·.name) → fname' ∈ p.map funcWithMDName` (added to
       `seCmd_correct`/`seCmds_correct`/`seIfStmt_correct`, `seFunc_correct` and friends, and
       the `seCmd_names_below`/`seCmds_names_below`/`seIfStmt_names_below` family in
       `SymExec/Correctness.lean`): every function whose spec has already been accumulated into
       `specs` really is a function of the (remaining) program. `seCmd_correct`'s `.func_call` case
       proves this by casing on `fetchFuncSpec specs fname` (a plain, non-monadic first step of
       `seFuncCall`'s definition, decidable independent of the surrounding success): if it errors,
       `seFuncCall` inherits the error and the goal is vacuous; if it succeeds with some `fspec`,
       `fetchFuncSpec_sound` (`SymExec/Correctness.lean`) gives `fname ∈ specs.map (·.name)`,
       `hspecs_cover` lifts that to `fname ∈ p.map funcWithMDName`, and `fetchFunc_of_mem`
       (`Language/Core/Syntax/AST.lean`) turns that membership into the actual `fetchFunc`
       witness -- at which point the arity fact above supplies the rest. `hspecs_cover` itself is
       discharged, with no new proof content, at `seExecFuncs_loop_correct`'s level
       (`SymExec/PartialCorrectness/ProgCorrectness.lean`) directly from the already-proven
       `hnames_corr : specs.map (·.name) = donePart.map funcWithMDName` (an equality, hence
       trivially a one-directional membership implication too). Three other things that used to be
       part of this clause turned out unnecessary the same way, each removed once actually checked
       rather than assumed necessary:
       - `outs.Nodup`: `EnvMatches_setVars` (`SymExec/FuncCallCorrectness.lean`) preserves
         `EnvMatches` across a repeated-`outs` call just fine, since both the concrete and symbolic
         `setVars` recurse over `outs` in the same left-to-right order and so resolve a repeat to
         "last write wins" identically on both sides -- no distinctness needed for that argument.
       - `args.length = params.length` (arity on the *arguments* side): `flattenArgVals`'s own
         definition (`SymExec/BigStep.lean`) fails on a length mismatch, so `seFuncCall_correct`
         reads this straight back out of `seFuncCall`'s own success instead of needing it supplied.
       - the "arguments always concretely defined and shape-matched" `∀ env` clause: for the same
         reason, `flattenArgVal`'s cases *are* `symValueMatchesType`'s cases, so a successful
         `flattenArgVals` already proves the shape match, no separate assumption needed.

   The language isn't strongly typed (see `DefinedVars.lean`), so this can't be checked by a
   static type system -- it's a semantic well-formedness precondition on the *program*,
   assumed rather than verified, exactly mirroring the precondition `mergeSymValue`
   (`SymExec/BigStep.lean`) already requires to merge two branches' values at all: shape
   disagreement makes merging undefined, not just unproven.

   This is checked structurally the same way `DefinedVarsCom`/`DefinedVarsCmds` are (mirroring
   their recursion shape one-for-one) -- it doesn't need to descend into a called function's own
   body (that's a separate, whole-program-level well-shapedness concern -- see
   `SymExec/FuncCorrectness.lean`'s whole-program correctness notes), only check the call *site*
   itself.
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
  | .func_call outs fname _args =>
      ∀ md func p', fetchFunc p fname = Except.ok (FuncWithMD.mk md func, p') →
        match func with
        | Func.mk _ _ rets _ => outs.length = rets.length
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
