import Corellzk2smt.Basic
import Corellzk2smt.Config
import Corellzk2smt.Language.Core.Syntax.AST
import Corellzk2smt.Language.Core.Semantics.Basic
import Corellzk2smt.Language.Core.Semantics.BigStep

/- A program is "well-shaped" when:
   (a) at every `if`-statement it contains, the two branches never disagree on a variable's
       shape (scalar vs. array, or array length) -- i.e. a variable is never a scalar coming
       out of one branch and an array (or a differently-sized array) coming out of the other,
       for any concrete starting environment that reaches that `if`-statement;
   (b) every `loop_exp`'s repetition count is a syntactic literal (`SimpleExpr.val`) -- so
       symbolic execution's unrolling (`tryEvalSimpleExprToFFValue`) never depends on a
       variable's runtime value, matching `AST.lean`'s own comment that a loop/array bound
       "is supposed to be a constant expression";
   (c) every `if`-statement's condition is defined on any concrete environment reaching it --
       i.e. `evalCond` never errors out (a missing/mistyped variable), which is what lets
       `encodeCond` be shown to always succeed symbolically too (`encodeCond_defined`,
       `SymExec/Lemmas.lean`), mirroring (b)'s role for `loop_exp`; and
   (d) every `func_call` site names a function that actually exists in the (remaining) program,
       called with the right arity (`args`/`outs` lengths matching the callee's declared
       `params`/`rets`), no-repeat `outs`, and arguments that are always concretely defined *and*
       already shape-matched to the callee's declared param types (`ValuesMatchParams`) -- the
       call-site well-formedness `seFuncCall_correct` (`SymExec/FuncCallCorrectness.lean`) itself
       needs as hypotheses, now phrased once here so `H_funcCall` (`SymExec/Correctness.lean`)
       can be discharged from it instead of assumed unconditionally (see that file's `H_funcCall`
       design notes for why the unconditional form is never actually provable).

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
  | .if_stmt cond tb eb =>
      (∀ (env : Env c), ∃ b, evalCond env cond = Except.ok b) ∧
      WellShapedCmds gconf p tb ∧ WellShapedCmds gconf p eb ∧
      ∀ (env envTb envEb : Env c),
        evalCmds gconf p env tb = Except.ok envTb →
        evalCmds gconf p env eb = Except.ok envEb →
        ∀ (id : VarID) (v1 v2 : Value c),
          envTb.get? id = some v1 → envEb.get? id = some v2 → sameShapeValue v1 v2
  | .loop_exp rep body => (∃ v, rep = SimpleExpr.val v) ∧ WellShapedCmds gconf p body
  | .loop _rep body => WellShapedCmds gconf p body
  | .func_call outs fname args =>
      ∃ md func p', fetchFunc p fname = Except.ok (FuncWithMD.mk md func, p') ∧
        match func with
        | Func.mk _ params rets _ =>
          args.length = params.length ∧ outs.length = rets.length ∧ outs.Nodup ∧
          ∀ (env : Env c), ∃ vs : List (Value c),
            evalSimpleExprsToValue env args = Except.ok vs ∧ ValuesMatchParams vs params
  | _ => True

def WellShapedCmds {c : ZKConfig} (gconf : GlobalConfig c) (p : Prog c)
    (cmds : List (ComWithMD c)) : Prop :=
  match cmds with
  | [] => True
  | i :: rest =>
    match i with
    | .mk _ cmd => WellShapedCom gconf p cmd ∧ WellShapedCmds gconf p rest

end

-- The name of a function within a `FuncWithMD` -- a small accessor since `Func`/`FuncWithMD` are
-- plain (single-constructor) `inductive`s, not `structure`s, so no dot-notation projection is
-- generated automatically.
def funcWithMDName {c : ZKConfig} (f : FuncWithMD c) : FName :=
  match f with | FuncWithMD.mk _ func => match func with | Func.mk name _ _ _ => name

-- The body of a function within a `FuncWithMD` -- see `funcWithMDName`.
def funcWithMDBody {c : ZKConfig} (f : FuncWithMD c) : List (ComWithMD c) :=
  match f with | FuncWithMD.mk _ func => match func with | Func.mk _ _ _ body => body

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
