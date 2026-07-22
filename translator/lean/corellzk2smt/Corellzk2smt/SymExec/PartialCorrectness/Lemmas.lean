import Corellzk2smt.SymExec.Lemmas

/-
Partial-correctness reformulation of `Corellzk2smt.SymExec.Lemmas.TranslatesCorrectly`.

The original `TranslatesCorrectly` requires `symbolic` to *always* succeed (an unconditional,
existentially-witnessed `∃ spec, symbolic symEnv = Except.ok spec ∧ ...`). Proving that for a
whole program requires an external guarantee (`WellShapedCmds`/`WellShapedProg`) that rules out
every way `seCmd`/`seFunc`/`seExecFuncs` could fail -- literal loop bounds, callees existing with
matching arg shapes, etc. It also means a genuinely unimplemented piece (`seSimpleCmd`, currently
a stub that always errors) can only ever be threaded through as a *permanently admitted*
hypothesis, since "always succeeds" is simply false for it today.

This version instead only requires soundness+completeness *given* that `symbolic` succeeds for
the `symEnv` in question (`∀ spec, symbolic symEnv = Except.ok spec → ...`). Two consequences:

1. Whatever facts `WellShapedCmds`/`WellShapedProg` used to supply externally (a loop's literal
   bound, a call's callee existing with matching shapes, ...) can instead be *recovered* from the
   success hypothesis itself, by case-splitting on `symbolic`'s own definition -- `seCmd`/`seFunc`/
   `seExecFuncs` only ever succeed when those conditions hold, so a success witness already
   proves they held, with no separate assumption needed.
2. A statement like "if `seSimpleCmd` succeeds, then sound+complete" is *vacuously, unconditionally
   true right now* (it never succeeds), so it stops being a standing admitted hypothesis and
   becomes a genuine `sorry`-free theorem -- one that automatically says something stronger, with
   no restatement needed anywhere downstream, as more of the stub gets implemented.

See the design discussion in `SymExec/ProgCorrectness.lean`'s header (and the surrounding
conversation) for the full rationale, including which parts of the old development (`EnvMatches`,
`agreesOnFF`/`agreesOnBool`, `mergeSymEnv`'s own correctness, `seqComposition_correct`,
`noop_spec_correct`, ...) are orthogonal to this change and get reused here unchanged, imported
directly rather than re-derived.
-/
namespace Corellzk2smt.SymExec.PartialCorrectness.Lemmas

open Corellzk2smt.Config (GlobalConfig)
open Corellzk2smt.Language.Core.Syntax.AST
open Corellzk2smt.Language.Core.Semantics.Basic
open Corellzk2smt.Language.Core.Semantics.BigStep
open Corellzk2smt.SymExec.Basic
open Corellzk2smt.SymExec.BigStep
open Corellzk2smt.FFConstraints.Basic
open Corellzk2smt.FFConstraints.Satisfiability
open Corellzk2smt.FFConstraints.Satisfiability_th
open Corellzk2smt.SymExec.Lemmas

/-- The soundness half of `TranslatesCorrectly`: every concrete success extends to a satisfying
    assignment, agreeing with the given one outside `spec`'s own vars (the frame condition). Named
    on its own so it can be stated/reused independent of the freshness bookkeeping -- doesn't need
    `sconf` at all, only `spec`/`symEnv`/`concrete`'s own content. -/
def TranslatesCorrectly_soundness {c : ZKConfig} (gconf : GlobalConfig c)
    (specs : List (FuncSpec c)) (symEnv : SymEnv c) (spec : CmdsSpec c)
    (concrete : Env c → Except String (Env c)) : Prop :=
  ∀ (env : Env c) (assignment : Assignment c),
    EnvMatches assignment symEnv env →
    ∀ env', concrete env = Except.ok env' →
      ∃ assignment',
        agreesOnFF (symEnvVars symEnv) assignment assignment' ∧
        agreesOnBool (symEnvVars symEnv) assignment assignment' ∧
        (∀ n, Var.ffv n ∉ specVars spec → assignment'.ff n = assignment.ff n) ∧
        (∀ n, Var.boolv n ∉ specVars spec → assignment'.bool n = assignment.bool n) ∧
        evalFormula gconf assignment' spec.f (specs.map (·.f)) = Except.ok true ∧
        EnvMatches assignment' spec.outSymEnv env'

/-- The completeness half of `TranslatesCorrectly`: every satisfying extension of a matching
    assignment corresponds to an actual concrete success. See `TranslatesCorrectly_soundness`. -/
def TranslatesCorrectly_completeness {c : ZKConfig} (gconf : GlobalConfig c)
    (specs : List (FuncSpec c)) (symEnv : SymEnv c) (spec : CmdsSpec c)
    (concrete : Env c → Except String (Env c)) : Prop :=
  ∀ (env : Env c) (assignment : Assignment c),
    EnvMatches assignment symEnv env →
    ∀ assignment', agreesOnFF (symEnvVars symEnv) assignment assignment' →
      evalFormula gconf assignment' spec.f (specs.map (·.f)) = Except.ok true →
      ∃ env', concrete env = Except.ok env' ∧ EnvMatches assignment' spec.outSymEnv env'

/-- Partial-correctness analogue of `Corellzk2smt.SymExec.Lemmas.TranslatesCorrectly`: identical
    freshness/soundness/completeness payload, but conditioned on `symbolic` actually succeeding
    for the given `symEnv`, rather than asserting it always does. See this file's header. -/
def TranslatesCorrectly {c : ZKConfig} (gconf : GlobalConfig c) (sconf : SymExecConfig c)
    (specs : List (FuncSpec c))
    (concrete : Env c → Except String (Env c))
    (symbolic : SymEnv c → Except String (CmdsSpec c)) : Prop :=
  ∀ (symEnv : SymEnv c),
    varSetBelow (symEnvVars symEnv) sconf.nextVarId →
    ∀ spec, symbolic symEnv = Except.ok spec →
      spec.inSymEnv = symEnv ∧
      sconf.nextVarId ≤ spec.nextVarId ∧
      (∀ v ∈ specVars spec, v ∈ symEnvVars symEnv ∨ sconf.nextVarId ≤ varIndex v) ∧
      varSetBelow (specVars spec) spec.nextVarId ∧
      varSetBelow (symEnvVars spec.outSymEnv) spec.nextVarId ∧
      (∀ v ∈ symEnvVars spec.outSymEnv, v ∈ symEnvVars symEnv ∨ sconf.nextVarId ≤ varIndex v) ∧
      TranslatesCorrectly_soundness gconf specs symEnv spec concrete ∧
      TranslatesCorrectly_completeness gconf specs symEnv spec concrete

/-- `TranslatesCorrectly`, but additionally conditioned on an extra `guard symEnv` hypothesis
    (alongside the existing `varSetBelow`/success ones) before the payload has to hold. Used by
    `seCmd_correct`/`seCmds_correct`/`seIfStmt_correct` (`PartialCorrectness/Correctness.lean`) to
    state their domain-preservation precondition (`∀ id, id ∈ definedVarsCmds vars cmds →
    symEnv.contains id`, from `Language/Core/Analysis/DefinedVars.lean`) -- the replacement for
    the old, permanently-assumed (and, as stated, false) `H_domain` hypothesis. `TranslatesCorrectly
    gconf sconf specs concrete symbolic` itself is the special case `guard := fun _ => True`
    (see `TranslatesCorrectlyGiven_of_TranslatesCorrectly` below). -/
def TranslatesCorrectlyGiven {c : ZKConfig} (gconf : GlobalConfig c) (sconf : SymExecConfig c)
    (specs : List (FuncSpec c)) (guard : SymEnv c → Prop)
    (concrete : Env c → Except String (Env c))
    (symbolic : SymEnv c → Except String (CmdsSpec c)) : Prop :=
  ∀ (symEnv : SymEnv c),
    varSetBelow (symEnvVars symEnv) sconf.nextVarId →
    guard symEnv →
    ∀ spec, symbolic symEnv = Except.ok spec →
      spec.inSymEnv = symEnv ∧
      sconf.nextVarId ≤ spec.nextVarId ∧
      (∀ v ∈ specVars spec, v ∈ symEnvVars symEnv ∨ sconf.nextVarId ≤ varIndex v) ∧
      varSetBelow (specVars spec) spec.nextVarId ∧
      varSetBelow (symEnvVars spec.outSymEnv) spec.nextVarId ∧
      (∀ v ∈ symEnvVars spec.outSymEnv, v ∈ symEnvVars symEnv ∨ sconf.nextVarId ≤ varIndex v) ∧
      TranslatesCorrectly_soundness gconf specs symEnv spec concrete ∧
      TranslatesCorrectly_completeness gconf specs symEnv spec concrete

/-- A plain `TranslatesCorrectly` fact trivially satisfies `TranslatesCorrectlyGiven` for *any*
    guard, since it doesn't need the extra hypothesis at all -- used at `seCmd_correct`'s
    `.func_call`/simple-command cases, which delegate entirely to `H_funcCall`/`H_simple` (still
    plain `TranslatesCorrectly` facts, unaffected by the domain-precondition threading). -/
theorem TranslatesCorrectlyGiven_of_TranslatesCorrectly {c : ZKConfig} (gconf : GlobalConfig c)
    (sconf : SymExecConfig c) (specs : List (FuncSpec c)) (guard : SymEnv c → Prop)
    (concrete : Env c → Except String (Env c))
    (symbolic : SymEnv c → Except String (CmdsSpec c))
    (h : TranslatesCorrectly gconf sconf specs concrete symbolic) :
    TranslatesCorrectlyGiven gconf sconf specs guard concrete symbolic := by
  intro symEnv hbelow _hguard spec hspec_eq
  exact h symEnv hbelow spec hspec_eq

end Corellzk2smt.SymExec.PartialCorrectness.Lemmas
