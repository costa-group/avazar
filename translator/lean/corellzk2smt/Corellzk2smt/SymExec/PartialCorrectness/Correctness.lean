import Corellzk2smt.SymExec.Lemmas
import Corellzk2smt.Language.Core.Analysis.WellShaped
import Corellzk2smt.SymExec.PartialCorrectness.Lemmas
import Corellzk2smt.SymExec.FuncCallCorrectness

/-
This file merges what used to be two files: `SymExec/Correctness.lean` ("shared machinery" for
`seCmd`/`seCmds`/`seIfStmt`/`seFuncCall` correctness, not stated in terms of `TranslatesCorrectly`
at all -- `evalFuncCallCmd`, the `_prepend_indep`/`_names_below` families, `noop_spec_correct`,
`seqComposition_correct`, `fetchFuncSpec_sound`, etc.) and `SymExec/PartialCorrectness/
Correctness.lean` (the actual `seIfStmt_correct`/`seCmd_correct`/`seCmds_correct` theorems built on
top of it). They were originally separate because the shared machinery was meant to be reusable by
both an unconditional and a conditional (`TranslatesCorrectly`) formalization; the unconditional one
was deleted once the conditional one fully superseded it (see
`project_corellzk2smt_wholeprogram_design` in this project's session history), leaving the split
purely historical -- merged back into one file/namespace now that there's only one consumer.

Partial-correctness analogues of `seIfStmt_correct`/`seCmd_correct`/`seCmds_correct`: every one of
these now takes the produced `spec` and the success witness `symbolic symEnv = Except.ok spec` as
*given* (via `TranslatesCorrectly`), rather than proving `symbolic` always succeeds and producing
`spec` as an existential witness.

Everything genuinely combinatorial -- `seqComposition_correct`, `noop_spec_correct`,
`mergeIfBranches_sound`/`mergeIfBranches_complete`, the `mergeSymEnv_*` family,
`tryEvalCondToConcreteValue_correct`, `encodeCond_vars_subset` -- is reused unchanged (now living
earlier in this same file): none of it is stated in terms of `TranslatesCorrectly` at all, just
explicit hypotheses about specific `CmdsSpec`s. Only the three theorems that *construct*
`TranslatesCorrectly`'s existential/conditional form change, and the change is mechanical:
everywhere the old proof did `obtain ⟨spec, hspec_eq, ...⟩ := someRecursiveCall ...` (destructuring
an existential), the new proof instead does `cases hspec_eq : someComputation ... with | error e
=> ... | ok spec => ...` (case-splitting on the actual computation) and then applies the recursive
correctness fact to the *discovered* `spec`/`hspec_eq` -- the `error` branch is dismissed by
unfolding the *caller's* own `hspec_eq` (the given success witness) far enough to see it would also
have to be `Except.error`, contradiction.

`H_domain` no longer exists as a hypothesis here either (same fate as `H_shape`): it was false as
a blanket claim (`seFuncCall`'s `setVars` call can grow a symbolic environment's domain, nothing
rules that out from `seCmds` succeeding alone). The replacement is `SymExec/Lemmas.lean`'s
already-proven `seCmds_domain_of_defined`/`seCmd_domain_of_defined`/`seIfStmt_domain_of_defined`,
which need an extra premise: `∀ id, id ∈ definedVarsCmds vars cmds → symEnv.contains id` for some
`vars` (every variable `cmds` could ever write is already in `symEnv`'s domain). All three
theorems below gain a `vars : VarIDSet` parameter and their conclusion becomes
`TranslatesCorrectlyGiven ... guard ...` instead of plain `TranslatesCorrectly` (`guard` being
exactly that premise, phrased over `definedVarsCom`/`definedVarsCmds` for whichever `cmd`/`cmds`
the theorem is about) -- `TranslatesCorrectlyGiven_of_TranslatesCorrectly` handles the
`.func_call`/simple-command cases, which delegate entirely to `H_funcCall`/`H_simple` (still plain
`TranslatesCorrectly` facts, since neither of those needs the domain premise at all). The one
actual *use* of the domain fact (building `hdom_contains` inside `seIfStmt_correct`'s merge
branch) now calls `seCmds_domain_of_defined` directly, reusing the very same `vars`/precondition
already constructed to satisfy the recursive `seCmds_correct` calls.

Note on `hshaped`/`WellShapedCom`/`WellShapedCmds`: these predicates are now provably `True` for
every command/program (see `Language/Core/Analysis/WellShaped.lean`), but `seIfStmt_correct`/
`seCmd_correct`/`seCmds_correct` below (and the `_names_below` family earlier in this file) still
take a real `hshaped` parameter unchanged -- removing it was tried and found to make this file's
mutual, well-founded-recursive elaboration take 40+ minutes instead of under a minute (see
`feedback_lean_slow_build_diagnosis` in this project's session history). Every *caller* outside
this file manufactures the witness on the spot via `trivialWSCom`/`trivialWSCmds`
(`Language/Core/Analysis/WellShaped.lean`) instead of proving one, so nothing further up the chain
is burdened by this -- it's purely an internal implementation detail of this one file's proof.
-/
namespace Corellzk2smt.SymExec.PartialCorrectness.Correctness

open Corellzk2smt.Config
open Corellzk2smt.Language.Core.Syntax.AST
open Corellzk2smt.Language.Core.Semantics.Basic
open Corellzk2smt.Language.Core.Semantics.BigStep
open Corellzk2smt.Language.Core.Analysis.WellShaped
open Corellzk2smt.Language.Core.Analysis.DefinedVars
open Corellzk2smt.SymExec.Basic
open Corellzk2smt.SymExec.BigStep
open Corellzk2smt.FFConstraints.Basic
open Corellzk2smt.FFConstraints.Satisfiability
open Corellzk2smt.FFConstraints.Satisfiability_th
open Corellzk2smt.SymExec.Lemmas
open Corellzk2smt.SymExec.FuncCallCorrectness
open Corellzk2smt.SymExec.PartialCorrectness.Lemmas

-- ---------------------------------------------------------------------------
-- `seCmd`/`seCmds`/`seIfStmt`/`seFuncCall`'s symbolic *output* is unaffected by prepending a
-- spec whose name is unreachable from `p` -- the whole-program correctness argument
-- (`seExecFuncs_correct`) needs this alongside `evalFormula_prepend_indep`: `specs` appears not
-- just as `TranslatesCorrectly`'s own explicit parameter (handled by `evalFormula_prepend_indep`
-- alone), but also *inside* `seFuncCall`'s own computation (via `fetchFuncSpec`), which
-- `seCmd`/`seCmds`/`seIfStmt` thread through unchanged across their whole mutual recursion.
-- ---------------------------------------------------------------------------

/-- `fetchFuncSpec`'s search skips straight past a prepended spec that doesn't match the name
    being searched for, continuing exactly as it would without it -- the `FuncSpec` mirror of
    `fetchMacro_prepend_indep`. -/
theorem fetchFuncSpec_prepend_indep {c : ZKConfig} (fspec_new : FuncSpec c)
    (specs : List (FuncSpec c)) (fname : FName) (hne : fspec_new.name ≠ fname) :
    fetchFuncSpec (fspec_new :: specs) fname = fetchFuncSpec specs fname := by
  simp only [fetchFuncSpec]
  rw [if_neg (by simpa using hne)]

/-- `seFuncCall` only ever reads `specs` through the single `fetchFuncSpec specs fname` lookup at
    its very start -- everything downstream (`resolveSimpleExprsToSymValue`, `flattenArgVals`,
    `mintFreshRets`/`mintFreshAuxParams`, `setVars`) depends only on the *result* of that lookup,
    never on `specs` itself. So if the lookup is unaffected by prepending (given the prepended
    spec's name doesn't match `fname`), the whole call's output is too. -/
theorem seFuncCall_prepend_indep {c : ZKConfig} (gconf : GlobalConfig c) (sconf : SymExecConfig c)
    (symEnv : SymEnv c) (fspec_new : FuncSpec c) (specs : List (FuncSpec c)) (fname : FName)
    (args : List (SimpleExpr c)) (outs : List VarID) (hne : fspec_new.name ≠ fname) :
    seFuncCall gconf sconf symEnv (fspec_new :: specs) fname args outs =
      seFuncCall gconf sconf symEnv specs fname args outs := by
  simp only [seFuncCall, fetchFuncSpec_prepend_indep fspec_new specs fname hne]

-- ---------------------------------------------------------------------------
-- `seCmd`/`seCmds`/`seIfStmt`/`seFuncCall`'s output formula never directly calls a name that
-- isn't reachable from `p` -- together with `evalFormula_names_below_indep`, this is what lets
-- the whole-program correctness argument shrink a `TranslatesCorrectly` completeness hypothesis
-- (stated against the *already-extended* specs list) back down to the smaller list a single
-- function's own proof was built against. None of the "glue" formulas `seCmd`/`seCmds`/
-- `seIfStmt` build along the way (`encodeCond`'s output, `mergeSymEnv`'s tie-back equations,
-- the `.true` no-op) ever contain a `.call` node at all -- only `seFuncCall` ever introduces one,
-- and always for a name found via `fetchFuncSpec specs fname`, i.e. always a member of `specs`.
-- ---------------------------------------------------------------------------

/-- `fetchFuncSpec` only ever returns a spec whose own `.name` field matches the search key, and
    which is a member of the searched list -- mirrors `fetchMacro_sound`'s shape. -/
theorem fetchFuncSpec_sound {c : ZKConfig} :
    ∀ (specs : List (FuncSpec c)) (fname : FName) (spec : FuncSpec c),
      fetchFuncSpec specs fname = Except.ok spec → spec.name = fname ∧ spec ∈ specs := by
  intro specs
  induction specs with
  | nil => intro fname spec h; simp [fetchFuncSpec] at h
  | cons head tail ih =>
      intro fname spec h
      simp only [fetchFuncSpec] at h
      by_cases hc : head.name = fname
      · simp only [hc, BEq.rfl, ↓reduceIte, Except.ok.injEq] at h
        exact ⟨h ▸ hc, h ▸ List.mem_cons_self ..⟩
      · simp only [hc, beq_iff_eq, ↓reduceIte] at h
        obtain ⟨hname, hmem⟩ := ih fname spec h
        exact ⟨hname, List.mem_cons_of_mem _ hmem⟩

/-- `simpleSymValToTerm`'s output is always a bare `.val`/`.var` leaf -- trivially `NamesBelow`
    any name, since it can't contain a `.call` at all. -/
theorem simpleSymValToTerm_names_below {c : ZKConfig} (sv : SimpleSymVal c) (badName : String) :
    TermNamesBelow (simpleSymValToTerm sv) badName := by
  cases sv <;> simp [simpleSymValToTerm, TermNamesBelow]

/-- `mergeSimpleSymVal` only ever extends `tbExtra`/`ebExtra` by conjoining an equation between a
    fresh variable and `simpleSymValToTerm` of one of the two inputs -- never introducing a
    `.call` -- so `NamesBelow` propagates from input to output for any name. -/
theorem mergeSimpleSymVal_names_below {c : ZKConfig} (nv : Nat) (tbExtra ebExtra : FFFormula c)
    (svTb svEb : SimpleSymVal c) (badName : String)
    (htb : FormulaNamesBelow tbExtra badName) (heb : FormulaNamesBelow ebExtra badName) :
    FormulaNamesBelow (mergeSimpleSymVal nv tbExtra ebExtra svTb svEb).2.2.1 badName ∧
    FormulaNamesBelow (mergeSimpleSymVal nv tbExtra ebExtra svTb svEb).2.2.2 badName := by
  simp only [mergeSimpleSymVal]
  split
  · exact ⟨htb, heb⟩
  · simp only [FormulaNamesBelow, TermNamesBelow]
    exact ⟨⟨htb, trivial, simpleSymValToTerm_names_below svTb badName⟩,
      ⟨heb, trivial, simpleSymValToTerm_names_below svEb badName⟩⟩

/-- `List.foldl`-invariant version of `mergeSimpleSymVal_names_below`, for `mergeSymValue`'s array
    branch: `NamesBelow` of the running `(tbExtra, ebExtra)` accumulator is preserved through the
    whole fold. -/
theorem foldl_mergeSimpleSymVal_names_below {c : ZKConfig} (badName : String) :
    ∀ (pairs : List (SimpleSymVal c × SimpleSymVal c)) (nv : Nat) (tbExtra ebExtra : FFFormula c)
      (merged : List (SimpleSymVal c)),
      FormulaNamesBelow tbExtra badName → FormulaNamesBelow ebExtra badName →
      FormulaNamesBelow
        (pairs.foldl (fun acc p =>
            let (nextVarId, tbExtra, ebExtra, merged) := acc
            let (mergedVal, nv, tbE, ebE) := mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2
            (nv, tbE, ebE, mergedVal :: merged)) (nv, tbExtra, ebExtra, merged)).2.1
        badName ∧
      FormulaNamesBelow
        (pairs.foldl (fun acc p =>
            let (nextVarId, tbExtra, ebExtra, merged) := acc
            let (mergedVal, nv, tbE, ebE) := mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2
            (nv, tbE, ebE, mergedVal :: merged)) (nv, tbExtra, ebExtra, merged)).2.2.1
        badName := by
  intro pairs
  induction pairs with
  | nil => intro nv tbExtra ebExtra merged htb heb; exact ⟨htb, heb⟩
  | cons p ps ih =>
      intro nv tbExtra ebExtra merged htb heb
      simp only [List.foldl_cons]
      have hstep := mergeSimpleSymVal_names_below nv tbExtra ebExtra p.1 p.2 badName htb heb
      exact ih _ _ _ _ hstep.1 hstep.2

/-- `mergeSymValue` only ever routes through `mergeSimpleSymVal` (directly, or per-position via
    the array fold) -- `NamesBelow` propagates from input to output for any name. -/
theorem mergeSymValue_names_below {c : ZKConfig} (nv : Nat) (tbExtra ebExtra : FFFormula c)
    (svTb svEb : SymValue c) (badName : String)
    (result : SymValue c × Nat × FFFormula c × FFFormula c)
    (h : mergeSymValue nv tbExtra ebExtra svTb svEb = Except.ok result)
    (htb : FormulaNamesBelow tbExtra badName) (heb : FormulaNamesBelow ebExtra badName) :
    FormulaNamesBelow result.2.2.1 badName ∧ FormulaNamesBelow result.2.2.2 badName := by
  simp only [mergeSymValue] at h
  match svTb, svEb, h with
  | .simple s1, .simple s2, h =>
      simp only [Except.ok.injEq] at h
      have := mergeSimpleSymVal_names_below nv tbExtra ebExtra s1 s2 badName htb heb
      rw [← h]
      exact this
  | .array arrTb, .array arrEb, h =>
      by_cases hsize : arrTb.size = arrEb.size
      · simp only [hsize, ↓reduceIte, Except.ok.injEq] at h
        have := foldl_mergeSimpleSymVal_names_below badName (arrTb.toList.zip arrEb.toList) nv
          tbExtra ebExtra [] htb heb
        rw [← h]
        exact this
      · simp [hsize] at h
  | .simple _, .array _, h => simp at h
  | .array _, .simple _, h => simp at h

/-- `mergeSymEnvKeys`'s running `(tbExtra, ebExtra)` accumulator's `NamesBelow` is preserved
    across the whole per-key fold. -/
theorem mergeSymEnvKeys_names_below {c : ZKConfig} (badName : String) :
    ∀ (nv : Nat) (tbEnv ebEnv : SymEnv c) (tbExtra ebExtra : FFFormula c) (keys : List VarID)
      (result : SymEnv c × Nat × FFFormula c × FFFormula c),
      mergeSymEnvKeys nv tbEnv ebEnv tbExtra ebExtra keys = Except.ok result →
      FormulaNamesBelow tbExtra badName → FormulaNamesBelow ebExtra badName →
      FormulaNamesBelow result.2.2.1 badName ∧ FormulaNamesBelow result.2.2.2 badName := by
  intro nv tbEnv ebEnv tbExtra ebExtra keys
  induction keys generalizing nv tbExtra ebExtra with
  | nil =>
      intro result h htb heb
      simp only [mergeSymEnvKeys, Except.ok.injEq] at h
      rw [← h]
      exact ⟨htb, heb⟩
  | cons id rest ih =>
      intro result h htb heb
      simp only [mergeSymEnvKeys] at h
      cases hget1 : getVar tbEnv id with
      | error e => rw [hget1] at h; simp at h
      | ok svTb =>
        rw [hget1] at h
        simp only [] at h
        cases hget2 : getVar ebEnv id with
        | error e => rw [hget2] at h; simp at h
        | ok svEb =>
          rw [hget2] at h
          simp only [] at h
          cases hmerge : mergeSymValue nv tbExtra ebExtra svTb svEb with
          | error e => rw [hmerge] at h; simp at h
          | ok mergeResult =>
            rw [hmerge] at h
            simp only [] at h
            have hmb := mergeSymValue_names_below nv tbExtra ebExtra svTb svEb badName
              mergeResult hmerge htb heb
            cases hrest : mergeSymEnvKeys mergeResult.2.1 tbEnv ebEnv mergeResult.2.2.1
                mergeResult.2.2.2 rest with
            | error e => rw [hrest] at h; simp at h
            | ok restResult =>
              rw [hrest] at h
              simp only [Except.ok.injEq] at h
              have hih := ih mergeResult.2.1 mergeResult.2.2.1 mergeResult.2.2.2 restResult hrest
                hmb.1 hmb.2
              rw [← h]
              exact hih

/-- `mergeSymEnv` starts its fold from `(.true, .true)` -- both trivially `NamesBelow` any name
    -- so the whole result is, via `mergeSymEnvKeys_names_below`. -/
theorem mergeSymEnv_names_below {c : ZKConfig} (badName : String) (nv : Nat)
    (tbEnv ebEnv : SymEnv c) (result : SymEnv c × Nat × FFFormula c × FFFormula c)
    (h : mergeSymEnv nv tbEnv ebEnv = Except.ok result) :
    FormulaNamesBelow result.2.2.1 badName ∧ FormulaNamesBelow result.2.2.2 badName := by
  simp only [mergeSymEnv] at h
  exact mergeSymEnvKeys_names_below badName nv tbEnv ebEnv FFFormula.true FFFormula.true
    tbEnv.keys result h trivial trivial

/-- The "no-op" formula every empty command-list / zero-iteration loop produces is `FFFormula.true`
    -- trivially `NamesBelow` any name. -/
theorem default_names_below {c : ZKConfig} (badName : String) :
    FormulaNamesBelow (default : FFFormula c) badName := by
  change FormulaNamesBelow FFFormula.true badName
  trivial

/-- `encodeCond`'s output is always a bare `.eq` of `simpleSymValToTerm` results -- trivially
    `NamesBelow` any name. -/
theorem encodeCond_names_below {c : ZKConfig} (badName : String) (symEnv : SymEnv c) (cond : Cond c)
    (g : FFFormula c) (h : encodeCond symEnv cond = Except.ok g) :
    FormulaNamesBelow g badName := by
  match cond, h with
  | .eq s1 s2, h =>
      simp only [encodeCond] at h
      cases h1 : resolveSimpleExpr symEnv s1 with
      | error e => rw [h1] at h; simp at h
      | ok sv1 =>
          rw [h1] at h
          simp only [] at h
          cases h2 : resolveSimpleExpr symEnv s2 with
          | error e => rw [h2] at h; simp at h
          | ok sv2 =>
              rw [h2] at h
              simp only [Except.ok.injEq] at h
              simp only [FormulaNamesBelow, ← h]
              exact ⟨simpleSymValToTerm_names_below sv1 badName,
                simpleSymValToTerm_names_below sv2 badName⟩

mutual
theorem seIfStmt_names_below {c : ZKConfig} (gconf : GlobalConfig c) (p : Prog c)
    (badName : String) (hunreach : ∀ r, fetchFunc p badName ≠ Except.ok r)
    (sconf : SymExecConfig c) (symEnv : SymEnv c) (specs : List (FuncSpec c))
    (hspecs_wf : ∀ spec ∈ specs, spec.f.name = spec.name)
    (hspecs_cover : ∀ fname', fname' ∈ specs.map (·.name) → fname' ∈ p.map funcWithMDName)
    (md : CmdMD) (cond : Cond c) (tb eb : List (ComWithMD c))
    (hshaped : WellShapedCom gconf p (Com.if_stmt cond tb eb))
    (spec : CmdsSpec c) (hspec_eq : seIfStmt gconf sconf symEnv specs md cond tb eb = Except.ok spec) :
    FormulaNamesBelow spec.f badName := by
  obtain ⟨hshapedTb, hshapedEb⟩ := hshaped
  simp only [seIfStmt] at hspec_eq
  cases hcv : tryEvalCondToConcreteValue gconf sconf symEnv md cond with
  | error e =>
      rw [hcv] at hspec_eq
      simp only [] at hspec_eq
      cases htb : seCmds gconf sconf symEnv specs tb with
      | error msg => rw [htb] at hspec_eq; simp at hspec_eq
      | ok tbSpec =>
          rw [htb] at hspec_eq
          simp only [] at hspec_eq
          cases heb : seCmds gconf sconf symEnv specs eb with
          | error msg => rw [heb] at hspec_eq; simp at hspec_eq
          | ok ebSpec =>
              rw [heb] at hspec_eq
              simp only [] at hspec_eq
              have ihTb := seCmds_names_below gconf p badName hunreach sconf symEnv specs
                hspecs_wf hspecs_cover tb hshapedTb tbSpec htb
              have ihEb := seCmds_names_below gconf p badName hunreach sconf symEnv specs
                hspecs_wf hspecs_cover eb hshapedEb ebSpec heb
              simp only [mergeIfBranches] at hspec_eq
              cases hg : encodeCond symEnv cond with
              | error e => rw [hg] at hspec_eq; simp at hspec_eq
              | ok g =>
                  rw [hg] at hspec_eq
                  simp only [] at hspec_eq
                  cases hme : mergeSymEnv (max tbSpec.nextVarId ebSpec.nextVarId) tbSpec.outSymEnv
                      ebSpec.outSymEnv with
                  | error e => rw [hme] at hspec_eq; simp at hspec_eq
                  | ok meResult =>
                      rw [hme] at hspec_eq
                      simp only [] at hspec_eq
                      have hgb := encodeCond_names_below badName symEnv cond g hg
                      have hmb := mergeSymEnv_names_below badName
                        (max tbSpec.nextVarId ebSpec.nextVarId) tbSpec.outSymEnv ebSpec.outSymEnv
                        meResult hme
                      injection hspec_eq with hspec_eq
                      simp only [FormulaNamesBelow, ← hspec_eq]
                      exact ⟨hgb, ⟨ihTb, hmb.1⟩, ⟨ihEb, hmb.2⟩⟩
  | ok condVal =>
      rw [hcv] at hspec_eq
      simp only [] at hspec_eq
      cases condVal with
      | true =>
          simp only [↓reduceIte] at hspec_eq
          exact seCmds_names_below gconf p badName hunreach sconf symEnv specs hspecs_wf
            hspecs_cover tb hshapedTb spec hspec_eq
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hspec_eq
          exact seCmds_names_below gconf p badName hunreach sconf symEnv specs hspecs_wf
            hspecs_cover eb hshapedEb spec hspec_eq
termination_by (numOfLoopExpComs tb + numOfLoopExpComs eb, sizeOfComs tb + sizeOfComs eb)
decreasing_by
  · have h1 : numOfLoopExpComs tb ≤ numOfLoopExpComs tb + numOfLoopExpComs eb := by grind
    rcases Nat.lt_or_eq_of_le h1 with h_less | h_equal
    · exact Prod.Lex.left _ _ h_less
    · rw [← h_equal]; exact Prod.Lex.right _ (sizeOfComs_a_lt_a_plus_b tb eb)
  · have h1 : numOfLoopExpComs eb ≤ numOfLoopExpComs tb + numOfLoopExpComs eb := by grind
    rcases Nat.lt_or_eq_of_le h1 with h_less | h_equal
    · exact Prod.Lex.left _ _ h_less
    · rw [← h_equal, ← Nat.add_comm]; exact Prod.Lex.right _ (sizeOfComs_a_lt_a_plus_b eb tb)
  · have h1 : numOfLoopExpComs eb ≤ numOfLoopExpComs tb + numOfLoopExpComs eb := by grind
    rcases Nat.lt_or_eq_of_le h1 with h_less | h_equal
    · exact Prod.Lex.left _ _ h_less
    · rw [← h_equal, ← Nat.add_comm]; exact Prod.Lex.right _ (sizeOfComs_a_lt_a_plus_b eb tb)
  · have h1 : numOfLoopExpComs tb ≤ numOfLoopExpComs tb + numOfLoopExpComs eb := by grind
    rcases Nat.lt_or_eq_of_le h1 with h_less | h_equal
    · exact Prod.Lex.left _ _ h_less
    · rw [← h_equal]; exact Prod.Lex.right _ (sizeOfComs_a_lt_a_plus_b tb eb)

theorem seCmd_names_below {c : ZKConfig} (gconf : GlobalConfig c) (p : Prog c)
    (badName : String) (hunreach : ∀ r, fetchFunc p badName ≠ Except.ok r)
    (sconf : SymExecConfig c) (symEnv : SymEnv c) (specs : List (FuncSpec c))
    (hspecs_wf : ∀ spec ∈ specs, spec.f.name = spec.name)
    (hspecs_cover : ∀ fname', fname' ∈ specs.map (·.name) → fname' ∈ p.map funcWithMDName)
    (i : ComWithMD c) (hshaped : WellShapedCom gconf p (match i with | .mk _ cmd => cmd))
    (spec : CmdsSpec c) (hspec_eq : seCmd gconf sconf symEnv specs i = Except.ok spec) :
    FormulaNamesBelow spec.f badName := by
  match i, hshaped with
  | .mk md cmd, hshaped =>
    match cmd, hshaped with
    | .if_stmt cond tb eb, hshaped =>
        simp only [seCmd] at hspec_eq
        exact seIfStmt_names_below gconf p badName hunreach sconf symEnv specs hspecs_wf
          hspecs_cover md cond tb eb hshaped spec hspec_eq
    | .loop_exp repSExp body, hshaped =>
        have hshapedBody : WellShapedCmds gconf p body := hshaped
        simp only [seCmd] at hspec_eq
        cases hrep : tryEvalSimpleExprToFFValue symEnv repSExp with
        | error e => rw [hrep] at hspec_eq; simp at hspec_eq
        | ok rep =>
            rw [hrep] at hspec_eq
            simp only [] at hspec_eq
            exact seCmd_names_below gconf p badName hunreach sconf symEnv specs hspecs_wf
              hspecs_cover (ComWithMD.mk md (Com.loop rep.val body)) hshapedBody spec hspec_eq
    | .loop (rep + 1) body, hshaped =>
        have hshapedBody : WellShapedCmds gconf p body := hshaped
        simp only [seCmd] at hspec_eq
        cases hfirst : seCmds gconf sconf symEnv specs body with
        | error msg => rw [hfirst] at hspec_eq; simp at hspec_eq
        | ok specFirstIter =>
            rw [hfirst] at hspec_eq
            simp only [] at hspec_eq
            have ihFirst := seCmds_names_below gconf p badName hunreach sconf symEnv specs
              hspecs_wf hspecs_cover body hshapedBody specFirstIter hfirst
            cases hrest : seCmd gconf { sconf with nextVarId := specFirstIter.nextVarId }
                specFirstIter.outSymEnv specs (ComWithMD.mk md (Com.loop rep body)) with
            | error msg => rw [hrest] at hspec_eq; simp at hspec_eq
            | ok specRestIter =>
                rw [hrest] at hspec_eq
                simp only [] at hspec_eq
                have ihRest := seCmd_names_below gconf p badName hunreach
                  { sconf with nextVarId := specFirstIter.nextVarId } specFirstIter.outSymEnv specs
                  hspecs_wf hspecs_cover (ComWithMD.mk md (Com.loop rep body)) hshapedBody
                  specRestIter hrest
                simp only [seqComposition] at hspec_eq
                injection hspec_eq with hspec_eq
                simp only [FormulaNamesBelow, ← hspec_eq]
                exact ⟨ihFirst, ihRest⟩
    | .loop 0 _body, _hshaped =>
        simp only [seCmd] at hspec_eq
        injection hspec_eq with hspec_eq
        rw [← hspec_eq]
        exact default_names_below badName
    | .func_call outs fname args, _hshaped =>
        simp only [seCmd] at hspec_eq
        simp only [seFuncCall] at hspec_eq
        cases hfetchSpec : fetchFuncSpec specs fname with
        | error e => rw [hfetchSpec] at hspec_eq; simp at hspec_eq
        | ok fspec =>
            rw [hfetchSpec] at hspec_eq
            simp only [] at hspec_eq
            obtain ⟨hspecname, hspecmem⟩ :=
              fetchFuncSpec_sound specs fname fspec hfetchSpec
            have hmem_specs : fname ∈ specs.map (·.name) := by
              rw [← hspecname]; exact List.mem_map_of_mem hspecmem
            obtain ⟨md', func, p', hfetch⟩ :=
              fetchFunc_of_mem p fname (hspecs_cover fname hmem_specs)
            have hne : badName ≠ fname := by
              intro heq
              exact hunreach (FuncWithMD.mk md' func, p') (heq ▸ hfetch)
            cases hargs : resolveSimpleExprsToSymValue symEnv args with
            | error e => rw [hargs] at hspec_eq; simp at hspec_eq
            | ok argVals =>
                rw [hargs] at hspec_eq
                simp only [] at hspec_eq
                cases hflat : flattenArgVals fspec.params argVals with
                | error e => rw [hflat] at hspec_eq; simp at hspec_eq
                | ok inputParams =>
                    rw [hflat] at hspec_eq
                    simp only [] at hspec_eq
                    cases hsv : setVars symEnv outs
                        (mintFreshRets sconf.nextVarId fspec.rets).2.2 with
                    | error e => rw [hsv] at hspec_eq; simp at hspec_eq
                    | ok outSymEnv' =>
                        rw [hsv] at hspec_eq
                        simp only [] at hspec_eq
                        injection hspec_eq with hspec_eq
                        have hfname_eq : fspec.f.name = fname := by
                          rw [hspecs_wf fspec hspecmem, hspecname]
                        simp only [FormulaNamesBelow, ← hspec_eq]
                        rw [hfname_eq]
                        exact fun heq => hne heq.symm
    | .assign _ _, _hshaped =>
        simp only [seCmd, seSimpleCmd] at hspec_eq; simp at hspec_eq
    | .new_array _ _, _hshaped =>
        simp only [seCmd, seSimpleCmd] at hspec_eq; simp at hspec_eq
    | .read_array _ _ _, _hshaped =>
        simp only [seCmd, seSimpleCmd] at hspec_eq; simp at hspec_eq
    | .write_array _ _ _, _hshaped =>
        simp only [seCmd, seSimpleCmd] at hspec_eq; simp at hspec_eq
    | .copy_array _ _, _hshaped =>
        simp only [seCmd, seSimpleCmd] at hspec_eq; simp at hspec_eq
termination_by (numOfLoopExpCom i, sizeOfCom i)
decreasing_by
  · simp only [numOfLoopExpCom]
    apply Prod.Lex.right
    simp only [sizeOfCom]
    grind
  · simp only [numOfLoopExpCom]
    apply Prod.Lex.left
    grind
  · simp only [numOfLoopExpCom]
    apply Prod.Lex.right
    simp only [sizeOfCom]
    grind
  · simp only [numOfLoopExpCom]
    apply Prod.Lex.right
    simp only [sizeOfCom]
    grind

theorem seCmds_names_below {c : ZKConfig} (gconf : GlobalConfig c) (p : Prog c)
    (badName : String) (hunreach : ∀ r, fetchFunc p badName ≠ Except.ok r)
    (sconf : SymExecConfig c) (symEnv : SymEnv c) (specs : List (FuncSpec c))
    (hspecs_wf : ∀ spec ∈ specs, spec.f.name = spec.name)
    (hspecs_cover : ∀ fname', fname' ∈ specs.map (·.name) → fname' ∈ p.map funcWithMDName)
    (cmds : List (ComWithMD c)) (hshaped : WellShapedCmds gconf p cmds)
    (spec : CmdsSpec c) (hspec_eq : seCmds gconf sconf symEnv specs cmds = Except.ok spec) :
    FormulaNamesBelow spec.f badName := by
  match cmds, hshaped with
  | [], _hshaped =>
      simp only [seCmds] at hspec_eq
      injection hspec_eq with hspec_eq
      rw [← hspec_eq]
      exact default_names_below badName
  | cmd :: rest, hshaped =>
    match cmd, hshaped with
    | ComWithMD.mk md cmd', hshaped =>
      obtain ⟨hshapedCmd, hshapedRest⟩ := hshaped
      simp only [seCmds] at hspec_eq
      cases hcmd : seCmd gconf sconf symEnv specs (ComWithMD.mk md cmd') with
      | error e => rw [hcmd] at hspec_eq; simp at hspec_eq
      | ok cmdSpec =>
          rw [hcmd] at hspec_eq
          simp only [] at hspec_eq
          have ihCmd := seCmd_names_below gconf p badName hunreach sconf symEnv specs hspecs_wf
            hspecs_cover (ComWithMD.mk md cmd') hshapedCmd cmdSpec hcmd
          cases hrest : seCmds gconf { sconf with nextVarId := cmdSpec.nextVarId }
              cmdSpec.outSymEnv specs rest with
          | error e => rw [hrest] at hspec_eq; simp at hspec_eq
          | ok cmdsSpec =>
              rw [hrest] at hspec_eq
              simp only [] at hspec_eq
              have ihRest := seCmds_names_below gconf p badName hunreach
                { sconf with nextVarId := cmdSpec.nextVarId } cmdSpec.outSymEnv specs hspecs_wf
                hspecs_cover rest hshapedRest cmdsSpec hrest
              simp only [seqComposition] at hspec_eq
              injection hspec_eq with hspec_eq
              simp only [FormulaNamesBelow, ← hspec_eq]
              exact ⟨ihCmd, ihRest⟩
termination_by (numOfLoopExpComs cmds, sizeOfComs cmds)
decreasing_by
  · have h1 : numOfLoopExpCom (ComWithMD.mk md cmd') ≤
        numOfLoopExpCom (ComWithMD.mk md cmd') + numOfLoopExpComs rest := by
      grind
    rcases Nat.lt_or_eq_of_le h1 with h_less | h_equal
    · apply Prod.Lex.left
      simp only [numOfLoopExpComs]
      exact h_less
    · simp only [numOfLoopExpComs]
      rw [← h_equal]
      apply Prod.Lex.right
      simp only [sizeOfComs]
      grind
  · have h1 : numOfLoopExpComs rest ≤
        numOfLoopExpCom (ComWithMD.mk md cmd') + numOfLoopExpComs rest := by
      grind
    rcases Nat.lt_or_eq_of_le h1 with h_less | h_equal
    · apply Prod.Lex.left
      simp only [numOfLoopExpComs]
      exact h_less
    · simp only [numOfLoopExpComs]
      rw [← h_equal]
      apply Prod.Lex.right
      simp only [sizeOfComs]
      grind
end


-- ---------------------------------------------------------------------------
-- Step 5: `seCmd`/`seCmds`/`seIfStmt` are correct
-- ---------------------------------------------------------------------------

/-- A `CmdsSpec` whose formula is trivially `true`: the "no-op" spec both `seCmds []` and
    `seCmd (Com.loop 0 _)` produce. Both proofs below (`nil`/`loop 0`) share this exact
    shape -- identity concrete computation, no formula content. -/
theorem noop_spec_correct {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (symEnv : SymEnv c)
    (hbelow : varSetBelow (symEnvVars symEnv) sconf.nextVarId)
    (concrete : Env c → Except String (Env c)) (hconcrete : ∀ env, concrete env = Except.ok env)
    (symbolic : SymEnv c → Except String (CmdsSpec c))
    (hsymbolic : symbolic symEnv
      = Except.ok { inSymEnv := symEnv, outSymEnv := symEnv, f := FFFormula.true,
                     nextVarId := sconf.nextVarId }) :
    ∃ spec, symbolic symEnv = Except.ok spec ∧
      spec.inSymEnv = symEnv ∧
      sconf.nextVarId ≤ spec.nextVarId ∧
      (∀ v ∈ specVars spec, v ∈ symEnvVars symEnv ∨ sconf.nextVarId ≤ varIndex v) ∧
      varSetBelow (specVars spec) spec.nextVarId ∧
      varSetBelow (symEnvVars spec.outSymEnv) spec.nextVarId ∧
      (∀ v ∈ symEnvVars spec.outSymEnv, v ∈ symEnvVars symEnv ∨ sconf.nextVarId ≤ varIndex v) ∧
      (∀ (env : Env c) (assignment : Assignment c),
        EnvMatches assignment symEnv env →
        ∀ env', concrete env = Except.ok env' →
          ∃ assignment',
            agreesOnFF (symEnvVars symEnv) assignment assignment' ∧
            agreesOnBool (symEnvVars symEnv) assignment assignment' ∧
            (∀ n, Var.ffv n ∉ specVars spec → assignment'.ff n = assignment.ff n) ∧
            (∀ n, Var.boolv n ∉ specVars spec → assignment'.bool n = assignment.bool n) ∧
            evalFormula gconf assignment' spec.f (specs.map (·.f)) = Except.ok true ∧
            EnvMatches assignment' spec.outSymEnv env') ∧
      (∀ (env : Env c) (assignment : Assignment c),
        EnvMatches assignment symEnv env →
        ∀ assignment', agreesOnFF (symEnvVars symEnv) assignment assignment' →
          evalFormula gconf assignment' spec.f (specs.map (·.f)) = Except.ok true →
          ∃ env', concrete env = Except.ok env' ∧ EnvMatches assignment' spec.outSymEnv env') := by
  refine ⟨_, hsymbolic, rfl, le_refl _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rcases Std.TreeSet.mem_union_iff.mp hv with h | h <;>
      exact absurd h Std.TreeSet.not_mem_emptyc
  · intro v hv
    rcases Std.TreeSet.mem_union_iff.mp hv with h | h <;>
      exact absurd h Std.TreeSet.not_mem_emptyc
  · exact hbelow
  · exact fun v hv => Or.inl hv
  · intro env assignment hmatch env' hc
    rw [hconcrete] at hc
    injection hc with hc
    refine ⟨assignment, (fun n _ => rfl), (fun n _ => rfl), (fun n _ => rfl),
      (fun n _ => rfl), ?_, ?_⟩
    · simp only [evalFormula]
    · rw [← hc]; exact hmatch
  · intro env assignment hmatch assignment' hagree _heval
    exact ⟨env, hconcrete env, EnvMatches_agreesOnFF_preserves assignment assignment' symEnv env
      hagree hmatch⟩

/-- Reassembles two `TranslatesCorrectly`-shaped bundles (for `spec1`/`concrete1`, then
    `spec2`/`concrete2` starting from `spec1`'s output) into one bundle for their
    `seqComposition`. Pure bookkeeping on top of `seqComposition_sound`/`_complete`
    (which already do the hard freshness/disjointness work) plus the `outSymEnv`-freshness
    conjunct (needed to restate `spec2`'s freshness, phrased relative to its own input
    `spec1.outSymEnv`, in terms of the original `symEnv`). -/
theorem seqComposition_correct {c : ZKConfig} (gconf : GlobalConfig c) (sconf : SymExecConfig c)
    (specs : List (FuncSpec c)) (cmd : ComWithMD c) (symEnv : SymEnv c)
    (hbelow : varSetBelow (symEnvVars symEnv) sconf.nextVarId)
    (concrete1 concrete2 concrete : Env c → Except String (Env c))
    (hconcrete : ∀ env, concrete env = (concrete1 env).bind concrete2)
    (spec1 : CmdsSpec c)
    (h1_in : spec1.inSymEnv = symEnv)
    (h1_mono : sconf.nextVarId ≤ spec1.nextVarId)
    (h1_fresh : ∀ v ∈ specVars spec1, v ∈ symEnvVars symEnv ∨ sconf.nextVarId ≤ varIndex v)
    (h1_below : varSetBelow (specVars spec1) spec1.nextVarId)
    (h1_outfresh : ∀ v ∈ symEnvVars spec1.outSymEnv, v ∈ symEnvVars symEnv ∨
      sconf.nextVarId ≤ varIndex v)
    (h1_sound : ∀ env assignment, EnvMatches assignment spec1.inSymEnv env →
        ∀ env', concrete1 env = Except.ok env' →
          ∃ assignment', agreesOnFF (symEnvVars spec1.inSymEnv) assignment assignment' ∧
            (∀ n, Var.ffv n ∉ specVars spec1 → assignment'.ff n = assignment.ff n) ∧
            (∀ n, Var.boolv n ∉ specVars spec1 → assignment'.bool n = assignment.bool n) ∧
            evalFormula gconf assignment' spec1.f (specs.map (·.f)) = Except.ok true ∧
            EnvMatches assignment' spec1.outSymEnv env')
    (h1_complete : ∀ env assignment, EnvMatches assignment spec1.inSymEnv env →
        ∀ assignment', agreesOnFF (symEnvVars spec1.inSymEnv) assignment assignment' →
          evalFormula gconf assignment' spec1.f (specs.map (·.f)) = Except.ok true →
          ∃ env1, concrete1 env = Except.ok env1 ∧ EnvMatches assignment' spec1.outSymEnv env1)
    (spec2 : CmdsSpec c)
    (h2_in : spec2.inSymEnv = spec1.outSymEnv)
    (h2_mono : spec1.nextVarId ≤ spec2.nextVarId)
    (h2_fresh : ∀ v ∈ specVars spec2, v ∈ symEnvVars spec2.inSymEnv ∨ spec1.nextVarId ≤ varIndex v)
    (h2_below : varSetBelow (specVars spec2) spec2.nextVarId)
    (h2_outbelow : varSetBelow (symEnvVars spec2.outSymEnv) spec2.nextVarId)
    (h2_outfresh : ∀ v ∈ symEnvVars spec2.outSymEnv, v ∈ symEnvVars spec2.inSymEnv ∨
      spec1.nextVarId ≤ varIndex v)
    (h2_sound : ∀ env assignment, EnvMatches assignment spec2.inSymEnv env →
        ∀ env', concrete2 env = Except.ok env' →
          ∃ assignment', agreesOnFF (symEnvVars spec2.inSymEnv) assignment assignment' ∧
            (∀ n, Var.ffv n ∉ specVars spec2 → assignment'.ff n = assignment.ff n) ∧
            (∀ n, Var.boolv n ∉ specVars spec2 → assignment'.bool n = assignment.bool n) ∧
            evalFormula gconf assignment' spec2.f (specs.map (·.f)) = Except.ok true ∧
            EnvMatches assignment' spec2.outSymEnv env')
    (h2_complete : ∀ env assignment, EnvMatches assignment spec2.inSymEnv env →
        ∀ assignment', agreesOnFF (symEnvVars spec2.inSymEnv) assignment assignment' →
          evalFormula gconf assignment' spec2.f (specs.map (·.f)) = Except.ok true →
          ∃ env2, concrete2 env = Except.ok env2 ∧ EnvMatches assignment' spec2.outSymEnv env2)
    (specComposed : CmdsSpec c)
    (heq : seqComposition gconf sconf cmd spec1 spec2 = Except.ok specComposed) :
    specComposed.inSymEnv = symEnv ∧
    sconf.nextVarId ≤ specComposed.nextVarId ∧
    (∀ v ∈ specVars specComposed, v ∈ symEnvVars symEnv ∨ sconf.nextVarId ≤ varIndex v) ∧
    varSetBelow (specVars specComposed) specComposed.nextVarId ∧
    varSetBelow (symEnvVars specComposed.outSymEnv) specComposed.nextVarId ∧
    (∀ v ∈ symEnvVars specComposed.outSymEnv, v ∈ symEnvVars symEnv ∨
      sconf.nextVarId ≤ varIndex v) ∧
    (∀ (env : Env c) (assignment : Assignment c),
      EnvMatches assignment symEnv env →
      ∀ env', concrete env = Except.ok env' →
        ∃ assignment',
          agreesOnFF (symEnvVars symEnv) assignment assignment' ∧
          agreesOnBool (symEnvVars symEnv) assignment assignment' ∧
          (∀ n, Var.ffv n ∉ specVars specComposed → assignment'.ff n = assignment.ff n) ∧
          (∀ n, Var.boolv n ∉ specVars specComposed → assignment'.bool n = assignment.bool n) ∧
          evalFormula gconf assignment' specComposed.f (specs.map (·.f)) = Except.ok true ∧
          EnvMatches assignment' specComposed.outSymEnv env') ∧
    (∀ (env : Env c) (assignment : Assignment c),
      EnvMatches assignment symEnv env →
      ∀ assignment', agreesOnFF (symEnvVars symEnv) assignment assignment' →
        evalFormula gconf assignment' specComposed.f (specs.map (·.f)) = Except.ok true →
        ∃ env', concrete env = Except.ok env' ∧ EnvMatches assignment' specComposed.outSymEnv env') := by
  have hCompIn : specComposed.inSymEnv = spec1.inSymEnv := by
    have h := heq; simp only [seqComposition, Except.ok.injEq] at h; rw [← h]
  have hCompOut : specComposed.outSymEnv = spec2.outSymEnv := by
    have h := heq; simp only [seqComposition, Except.ok.injEq] at h; rw [← h]
  have hCompNext : specComposed.nextVarId = spec2.nextVarId := by
    have h := heq; simp only [seqComposition, Except.ok.injEq] at h; rw [← h]
  have hCompF : specComposed.f = FFFormula.and (.anno spec1.f "") spec2.f := by
    have h := heq; simp only [seqComposition, Except.ok.injEq] at h; rw [← h]
  refine ⟨hCompIn.trans h1_in, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hCompNext]; exact h1_mono.trans h2_mono
  · intro v hv
    rcases (specVars_seqComposition gconf sconf cmd spec1 spec2 specComposed heq v).mp hv
      with hv1 | hv2
    · exact h1_fresh v hv1
    · rcases h2_fresh v hv2 with h | h
      · rw [h2_in] at h; exact h1_outfresh v h
      · exact Or.inr (h1_mono.trans h)
  · intro v hv
    rw [hCompNext]
    rcases (specVars_seqComposition gconf sconf cmd spec1 spec2 specComposed heq v).mp hv
      with hv1 | hv2
    · exact lt_of_lt_of_le (h1_below v hv1) h2_mono
    · exact h2_below v hv2
  · rw [hCompOut, hCompNext]; exact h2_outbelow
  · rw [hCompOut]
    intro v hv
    rcases h2_outfresh v hv with h | h
    · rw [h2_in] at h; exact h1_outfresh v h
    · exact Or.inr (h1_mono.trans h)
  · intro env assignment hmatch env' hc
    rw [hconcrete] at hc
    obtain ⟨assignment', ff_agree, frame_ff, frame_bool, heval, hmatch'⟩ :=
      seqComposition_sound gconf sconf specs spec1 spec2 concrete1 concrete2
        (h1_in ▸ hbelow) h1_mono h1_below h1_sound h2_fresh h2_sound h2_in
        env assignment (h1_in ▸ hmatch) env' hc
    rw [h1_in] at ff_agree
    refine ⟨assignment', ff_agree, agreesOnBool_symEnvVars symEnv assignment assignment',
      ?_, ?_, ?_, ?_⟩
    · intro n hn
      exact frame_ff n (fun hmem => hn ((specVars_seqComposition gconf sconf cmd spec1 spec2
        specComposed heq (Var.ffv n)).mpr (Std.TreeSet.mem_union_iff.mp hmem)))
    · intro n hn
      exact frame_bool n (fun hmem => hn ((specVars_seqComposition gconf sconf cmd spec1 spec2
        specComposed heq (Var.boolv n)).mpr (Std.TreeSet.mem_union_iff.mp hmem)))
    · rw [hCompF]; exact heval
    · rw [hCompOut]; exact hmatch'
  · intro env assignment hmatch assignment' hagree heval
    rw [hCompF] at heval
    obtain ⟨env', hbind, hmatch'⟩ := seqComposition_complete gconf specs spec1 spec2
      concrete1 concrete2 h2_in h1_complete h2_complete env assignment (h1_in ▸ hmatch)
      assignment' (h1_in ▸ hagree) heval
    refine ⟨env', ?_, ?_⟩
    · rw [hconcrete]; exact hbind
    · rw [hCompOut]; exact hmatch'

-- ---------------------------------------------------------------------------
-- seIfStmt_correct / seCmd_correct / seCmds_correct
-- ---------------------------------------------------------------------------

mutual

theorem seIfStmt_correct {c : ZKConfig} (gconf : GlobalConfig c) (p : Prog c)
    (specs : List (FuncSpec c))
    (H_simple : ∀ (sconf : SymExecConfig c) (i : ComWithMD c),
      TranslatesCorrectly gconf sconf specs (fun env => evalSimpleCmd gconf env i)
        (fun symEnv => seSimpleCmd gconf sconf symEnv specs i))
    (H_funcCall : ∀ (sconf : SymExecConfig c) (fname : FName) (args : List (SimpleExpr c))
        (outs : List VarID) (md : FuncMD) (func : Func c) (p' : Prog c),
      fetchFunc p fname = Except.ok (FuncWithMD.mk md func, p') →
      (match func with | Func.mk _ _ rets _ => outs.length = rets.length) →
      TranslatesCorrectly gconf sconf specs
        (fun env => evalFuncCallCmd gconf p fname args outs env)
        (fun symEnv => seFuncCall gconf sconf symEnv specs fname args outs))
    (hspecs_cover : ∀ fname', fname' ∈ specs.map (·.name) → fname' ∈ p.map funcWithMDName)
    (hspecs_rets_cover : ∀ fname'' fspec, fetchFuncSpec specs fname'' = Except.ok fspec →
      ∀ md func p'', fetchFunc p fname'' = Except.ok (FuncWithMD.mk md func, p'') →
        match func with | Func.mk _ _ rets _ => fspec.rets.length = rets.length)
    (vars : VarIDSet)
    (sconf : SymExecConfig c) (md : CmdMD) (cond : Cond c)
    (tb eb : List (ComWithMD c)) (hshaped : WellShapedCom gconf p (Com.if_stmt cond tb eb)) :
    TranslatesCorrectlyGiven gconf sconf specs
      (fun symEnv => ∀ id, id ∈ definedVarsCmds (definedVarsCmds vars tb) eb → symEnv.contains id)
      (fun env => evalIfStmt gconf p env md cond tb eb)
      (fun symEnv => seIfStmt gconf sconf symEnv specs md cond tb eb) := by
  obtain ⟨hshapedTb, hshapedEb⟩ := hshaped
  intro symEnv hbelow hdef spec hspec_eq
  have htb_pre : ∀ id, id ∈ definedVarsCmds vars tb → symEnv.contains id :=
    fun id hid => hdef id (definedVarsCmds_mono eb (definedVarsCmds vars tb) id hid)
  have heb_pre : ∀ id, id ∈ definedVarsCmds vars eb → symEnv.contains id :=
    fun id hid => hdef id
      (definedVarsCmds_subset_mono eb vars (definedVarsCmds vars tb)
        (fun id' hid' => definedVarsCmds_mono tb vars id' hid') id hid)
  cases htry : tryEvalCondToConcreteValue gconf sconf symEnv md cond with
  | ok condVal =>
      cases condVal with
      | true =>
          have hspec_eq' : seCmds gconf sconf symEnv specs tb = Except.ok spec := by
            have h : seIfStmt gconf sconf symEnv specs md cond tb eb =
                seCmds gconf sconf symEnv specs tb := by simp only [seIfStmt, htry, if_true]
            rw [← h]; exact hspec_eq
          obtain ⟨htbSpec_in, htbSpec_mono, htbSpec_fresh, htbSpec_below,
            htbSpec_outbelow, htbSpec_outfresh, htbSpec_sound, htbSpec_complete⟩ :=
            seCmds_correct gconf p specs H_simple H_funcCall hspecs_cover hspecs_rets_cover vars sconf tb hshapedTb
              symEnv hbelow htb_pre spec hspec_eq'
          refine ⟨htbSpec_in, htbSpec_mono, htbSpec_fresh, htbSpec_below,
            htbSpec_outbelow, htbSpec_outfresh, ?_, ?_⟩
          · intro env assignment hmatch env' hc
            have hcond : evalCond env cond = Except.ok true :=
              tryEvalCondToConcreteValue_correct gconf sconf symEnv md cond env assignment true
                hmatch htry
            simp only [evalIfStmt, hcond, if_true] at hc
            exact htbSpec_sound env assignment hmatch env' hc
          · intro env assignment hmatch assignment' hagree heval
            obtain ⟨env', hc, hmatch'⟩ :=
              htbSpec_complete env assignment hmatch assignment' hagree heval
            refine ⟨env', ?_, hmatch'⟩
            have hcond : evalCond env cond = Except.ok true :=
              tryEvalCondToConcreteValue_correct gconf sconf symEnv md cond env assignment true
                hmatch htry
            simp only [evalIfStmt, hcond, if_true]
            exact hc
      | false =>
          have hspec_eq' : seCmds gconf sconf symEnv specs eb = Except.ok spec := by
            have h : seIfStmt gconf sconf symEnv specs md cond tb eb =
                seCmds gconf sconf symEnv specs eb := by
              simp only [seIfStmt, htry, Bool.false_eq_true, if_false]
            rw [← h]; exact hspec_eq
          obtain ⟨hebSpec_in, hebSpec_mono, hebSpec_fresh, hebSpec_below,
            hebSpec_outbelow, hebSpec_outfresh, hebSpec_sound, hebSpec_complete⟩ :=
            seCmds_correct gconf p specs H_simple H_funcCall hspecs_cover hspecs_rets_cover vars sconf eb hshapedEb
              symEnv hbelow heb_pre spec hspec_eq'
          refine ⟨hebSpec_in, hebSpec_mono, hebSpec_fresh, hebSpec_below,
            hebSpec_outbelow, hebSpec_outfresh, ?_, ?_⟩
          · intro env assignment hmatch env' hc
            have hcond : evalCond env cond = Except.ok false :=
              tryEvalCondToConcreteValue_correct gconf sconf symEnv md cond env assignment false
                hmatch htry
            simp only [evalIfStmt, hcond] at hc
            exact hebSpec_sound env assignment hmatch env' hc
          · intro env assignment hmatch assignment' hagree heval
            obtain ⟨env', hc, hmatch'⟩ :=
              hebSpec_complete env assignment hmatch assignment' hagree heval
            refine ⟨env', ?_, hmatch'⟩
            have hcond : evalCond env cond = Except.ok false :=
              tryEvalCondToConcreteValue_correct gconf sconf symEnv md cond env assignment false
                hmatch htry
            simp only [evalIfStmt, hcond]
            exact hc
  | error e =>
      cases htbSpec_eq : seCmds gconf sconf symEnv specs tb with
      | error e2 => simp [seIfStmt, htry, htbSpec_eq] at hspec_eq
      | ok tbSpec =>
      cases hebSpec_eq : seCmds gconf sconf symEnv specs eb with
      | error e2 => simp [seIfStmt, htry, htbSpec_eq, hebSpec_eq] at hspec_eq
      | ok ebSpec =>
      obtain ⟨htbSpec_in, htbSpec_mono, htbSpec_fresh, htbSpec_below,
        htbSpec_outbelow, htbSpec_outfresh, htbSpec_sound, htbSpec_complete⟩ :=
        seCmds_correct gconf p specs H_simple H_funcCall hspecs_cover hspecs_rets_cover vars sconf tb hshapedTb
          symEnv hbelow htb_pre tbSpec htbSpec_eq
      obtain ⟨hebSpec_in, hebSpec_mono, hebSpec_fresh, hebSpec_below,
        hebSpec_outbelow, hebSpec_outfresh, hebSpec_sound, hebSpec_complete⟩ :=
        seCmds_correct gconf p specs H_simple H_funcCall hspecs_cover hspecs_rets_cover vars sconf eb hshapedEb
          symEnv hbelow heb_pre ebSpec hebSpec_eq
      have htbSpec_sound' : ∀ env assignment, EnvMatches assignment symEnv env →
          ∀ env', evalCmds gconf p env tb = Except.ok env' →
            ∃ assignment', agreesOnFF (symEnvVars symEnv) assignment assignment' ∧
              (∀ n, Var.ffv n ∉ specVars tbSpec → assignment'.ff n = assignment.ff n) ∧
              (∀ n, Var.boolv n ∉ specVars tbSpec → assignment'.bool n = assignment.bool n) ∧
              evalFormula gconf assignment' tbSpec.f (specs.map (·.f)) = Except.ok true ∧
              EnvMatches assignment' tbSpec.outSymEnv env' := by
        intro env assignment hmatch env' hc
        obtain ⟨a', hff, _hbool, hframeff, hframebool, heval, hmatch'⟩ :=
          htbSpec_sound env assignment hmatch env' hc
        exact ⟨a', hff, hframeff, hframebool, heval, hmatch'⟩
      have hebSpec_sound' : ∀ env assignment, EnvMatches assignment symEnv env →
          ∀ env', evalCmds gconf p env eb = Except.ok env' →
            ∃ assignment', agreesOnFF (symEnvVars symEnv) assignment assignment' ∧
              (∀ n, Var.ffv n ∉ specVars ebSpec → assignment'.ff n = assignment.ff n) ∧
              (∀ n, Var.boolv n ∉ specVars ebSpec → assignment'.bool n = assignment.bool n) ∧
              evalFormula gconf assignment' ebSpec.f (specs.map (·.f)) = Except.ok true ∧
              EnvMatches assignment' ebSpec.outSymEnv env' := by
        intro env assignment hmatch env' hc
        obtain ⟨a', hff, _hbool, hframeff, hframebool, heval, hmatch'⟩ :=
          hebSpec_sound env assignment hmatch env' hc
        exact ⟨a', hff, hframeff, hframebool, heval, hmatch'⟩
      obtain ⟨g, hg⟩ : ∃ g, encodeCond symEnv cond = Except.ok g := by
        cases hencode : encodeCond symEnv cond with
        | ok g => exact ⟨g, rfl⟩
        | error e =>
            simp [seIfStmt, htry, htbSpec_eq, hebSpec_eq, mergeIfBranches, hencode] at hspec_eq
      have hdom_contains : ∀ id, tbSpec.outSymEnv.contains id ↔ ebSpec.outSymEnv.contains id :=
        fun id => (seCmds_domain_of_defined gconf sconf symEnv specs vars tb htb_pre tbSpec
          htbSpec_eq id).symm.trans
          (seCmds_domain_of_defined gconf sconf symEnv specs vars eb heb_pre ebSpec hebSpec_eq id)
      have hdom : ∀ id, (∃ sv, tbSpec.outSymEnv.get? id = some sv) ↔
          (∃ sv, ebSpec.outSymEnv.get? id = some sv) :=
        fun id => (contains_iff_get?_isSome tbSpec.outSymEnv id).symm.trans
          ((hdom_contains id).trans (contains_iff_get?_isSome ebSpec.outSymEnv id))
      have hshape : ∀ id svTb svEb, tbSpec.outSymEnv.get? id = some svTb →
          ebSpec.outSymEnv.get? id = some svEb → sameShape svTb svEb := by
        have hspec_eq' := hspec_eq
        simp only [seIfStmt, htry, htbSpec_eq, hebSpec_eq, mergeIfBranches, hg] at hspec_eq'
        cases hmergeR : mergeSymEnv (max tbSpec.nextVarId ebSpec.nextVarId) tbSpec.outSymEnv
            ebSpec.outSymEnv with
        | error e => rw [hmergeR] at hspec_eq'; simp at hspec_eq'
        | ok mres =>
        have hmergeKeys : mergeSymEnvKeys (max tbSpec.nextVarId ebSpec.nextVarId)
            tbSpec.outSymEnv ebSpec.outSymEnv FFFormula.true FFFormula.true
            tbSpec.outSymEnv.keys = Except.ok mres := by
          rw [← hmergeR]; simp only [mergeSymEnv]
        intro id svTb svEb hsvTb hsvEb
        apply mergeSymEnvKeys_defined_of_ok (max tbSpec.nextVarId ebSpec.nextVarId)
          tbSpec.outSymEnv ebSpec.outSymEnv FFFormula.true FFFormula.true tbSpec.outSymEnv.keys
          mres hmergeKeys id ((mem_keys_iff_get?_isSome tbSpec.outSymEnv id).mpr ⟨svTb, hsvTb⟩)
          svTb svEb ((getVar_eq_ok_iff tbSpec.outSymEnv id svTb).mpr hsvTb)
          ((getVar_eq_ok_iff ebSpec.outSymEnv id svEb).mpr hsvEb)
      have htbEnvFresh : varSetBelow (symEnvVars tbSpec.outSymEnv)
          (max tbSpec.nextVarId ebSpec.nextVarId) :=
        varSetBelow_mono (le_max_left _ _) htbSpec_outbelow
      obtain ⟨_, mergedEnv, nv, tbE, ebE, hmergeEq, _, _, _, _, _⟩ :=
        mergeSymEnv_extend_tb gconf (specs.map (·.f)) (max tbSpec.nextVarId ebSpec.nextVarId)
          tbSpec.outSymEnv ebSpec.outSymEnv htbEnvFresh hdom hshape (default : Assignment c)
          (decodeSymEnv default tbSpec.outSymEnv)
          (fun id sv hsv => (EnvMatches_decodeSymEnv default tbSpec.outSymEnv).2 id sv hsv)
      obtain ⟨mergedSpec, hmergedSpec_eq⟩ :
          ∃ s, mergeIfBranches gconf sconf symEnv specs md tbSpec ebSpec cond = Except.ok s := by
        simp only [mergeIfBranches, hg, hmergeEq]
        exact ⟨_, rfl⟩
      have hCompIn : mergedSpec.inSymEnv = symEnv := by
        have h := hmergedSpec_eq
        simp only [mergeIfBranches, hg, hmergeEq, Except.ok.injEq] at h
        rw [← h]
      have hCompOut : mergedSpec.outSymEnv = mergedEnv := by
        have h := hmergedSpec_eq
        simp only [mergeIfBranches, hg, hmergeEq, Except.ok.injEq] at h
        rw [← h]
      have hCompNext : mergedSpec.nextVarId = nv := by
        have h := hmergedSpec_eq
        simp only [mergeIfBranches, hg, hmergeEq, Except.ok.injEq] at h
        rw [← h]
      have hCompF : mergedSpec.f =
          FFFormula.ite g (FFFormula.and tbSpec.f tbE) (FFFormula.and ebSpec.f ebE) := by
        have h := hmergedSpec_eq
        simp only [mergeIfBranches, hg, hmergeEq, Except.ok.injEq] at h
        rw [← h]
      have hnvMono : max tbSpec.nextVarId ebSpec.nextVarId ≤ nv :=
        mergeSymEnv_mono _ tbSpec.outSymEnv ebSpec.outSymEnv mergedEnv nv tbE ebE hmergeEq
      have houtfresh_bound : varSetBelow (symEnvVars mergedEnv) nv :=
        mergeSymEnv_out_fresh _ tbSpec.outSymEnv ebSpec.outSymEnv htbEnvFresh mergedEnv nv tbE ebE
          hmergeEq
      have houtfresh_disj : ∀ v ∈ symEnvVars mergedEnv,
          v ∈ symEnvVars tbSpec.outSymEnv ∨ max tbSpec.nextVarId ebSpec.nextVarId ≤ varIndex v :=
        mergeSymEnv_out_subset _ tbSpec.outSymEnv ebSpec.outSymEnv mergedEnv nv tbE ebE hmergeEq
      have htbE_subset : ∀ v ∈ (ffVarsOfFormula tbE ∪ bVarsOfFormula tbE),
          v ∈ symEnvVars tbSpec.outSymEnv ∨ max tbSpec.nextVarId ebSpec.nextVarId ≤ varIndex v :=
        mergeSymEnv_tbExtra_merged_subset _ tbSpec.outSymEnv ebSpec.outSymEnv mergedEnv nv tbE ebE
          hmergeEq
      have hebE_subset : ∀ v ∈ (ffVarsOfFormula ebE ∪ bVarsOfFormula ebE),
          v ∈ symEnvVars ebSpec.outSymEnv ∨ max tbSpec.nextVarId ebSpec.nextVarId ≤ varIndex v :=
        mergeSymEnv_ebExtra_merged_subset _ tbSpec.outSymEnv ebSpec.outSymEnv mergedEnv nv tbE ebE
          hmergeEq
      have htbExtra_below : varSetBelow (ffVarsOfFormula tbE ∪ bVarsOfFormula tbE) nv :=
        mergeSymEnv_tbExtra_fresh _ tbSpec.outSymEnv ebSpec.outSymEnv htbEnvFresh mergedEnv nv tbE
          ebE hmergeEq
      have hebEnvFresh : varSetBelow (symEnvVars ebSpec.outSymEnv)
          (max tbSpec.nextVarId ebSpec.nextVarId) :=
        varSetBelow_mono (le_max_right _ _) hebSpec_outbelow
      have hebExtra_below : varSetBelow (ffVarsOfFormula ebE ∪ bVarsOfFormula ebE) nv :=
        mergeSymEnv_ebExtra_fresh _ tbSpec.outSymEnv ebSpec.outSymEnv hebEnvFresh mergedEnv nv tbE
          ebE hmergeEq
      have hspecVarsIff : ∀ v, v ∈ specVars mergedSpec ↔
          v ∈ ffVarsOfFormula g ∨ v ∈ bVarsOfFormula g ∨
          v ∈ specVars tbSpec ∨ v ∈ (ffVarsOfFormula tbE ∪ bVarsOfFormula tbE) ∨
          v ∈ specVars ebSpec ∨ v ∈ (ffVarsOfFormula ebE ∪ bVarsOfFormula ebE) := by
        intro v
        simp only [specVars, hCompF, ffVarsOfFormula, bVarsOfFormula, Std.TreeSet.mem_union_iff]
        tauto
      have hgvars := encodeCond_vars_subset symEnv cond g hg
      have hseIfStmt_eq : seIfStmt gconf sconf symEnv specs md cond tb eb = Except.ok mergedSpec :=
        by simp only [seIfStmt, htry, htbSpec_eq, hebSpec_eq]; exact hmergedSpec_eq
      have hspec_merged : spec = mergedSpec := by injection (hspec_eq.symm.trans hseIfStmt_eq)
      subst hspec_merged
      refine ⟨hCompIn, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hCompNext]
        exact le_trans htbSpec_mono (le_trans (le_max_left _ _) hnvMono)
      · intro v hv
        rw [hspecVarsIff] at hv
        rcases hv with hg1 | hg2 | htb1 | htb2 | heb1 | heb2
        · exact Or.inl (hgvars.1 v hg1)
        · exact (hgvars.2 v hg2).elim
        · exact htbSpec_fresh v htb1
        · rcases htbE_subset v htb2 with h | h
          · exact htbSpec_outfresh v h
          · exact Or.inr (le_trans htbSpec_mono (le_trans (le_max_left _ _) h))
        · exact hebSpec_fresh v heb1
        · rcases hebE_subset v heb2 with h | h
          · exact hebSpec_outfresh v h
          · exact Or.inr (le_trans hebSpec_mono (le_trans (le_max_right _ _) h))
      · intro v hv
        rw [hCompNext]
        rw [hspecVarsIff] at hv
        rcases hv with hg1 | hg2 | htb1 | htb2 | heb1 | heb2
        · exact lt_of_lt_of_le (hbelow v (hgvars.1 v hg1))
            (le_trans htbSpec_mono (le_trans (le_max_left _ _) hnvMono))
        · exact (hgvars.2 v hg2).elim
        · exact lt_of_lt_of_le (htbSpec_below v htb1) (le_trans (le_max_left _ _) hnvMono)
        · exact htbExtra_below v htb2
        · exact lt_of_lt_of_le (hebSpec_below v heb1) (le_trans (le_max_right _ _) hnvMono)
        · exact hebExtra_below v heb2
      · rw [hCompOut, hCompNext]; exact houtfresh_bound
      · intro v hv
        rw [hCompOut] at hv
        rcases houtfresh_disj v hv with h | h
        · exact htbSpec_outfresh v h
        · exact Or.inr (le_trans htbSpec_mono (le_trans (le_max_left _ _) h))
      · intro env assignment hmatch env' hc
        obtain ⟨mergedSpec', hmergedSpec'_eq, assignment', aff, affframe, abframe, aeval, amatch⟩ :=
          mergeIfBranches_sound gconf sconf specs symEnv md cond tb eb p tbSpec ebSpec hbelow
            htbSpec_mono hebSpec_mono htbSpec_below hebSpec_below htbSpec_outbelow
            hebSpec_outbelow hdom hshape g hg htbSpec_sound' hebSpec_sound' env assignment hmatch
            env' hc
        have heqSpec : mergedSpec' = spec := by
          have h := hmergedSpec'_eq.symm.trans hmergedSpec_eq
          injection h
        subst heqSpec
        refine ⟨assignment', aff, agreesOnBool_symEnvVars symEnv assignment assignment', ?_, ?_,
          aeval, amatch⟩
        · intro n hn; exact affframe n (fun h => hn h)
        · intro n hn; exact abframe n (fun h => hn h)
      · intro env assignment hmatch assignment' hagree heval
        obtain ⟨env', hc, hmatch'⟩ :=
          mergeIfBranches_complete gconf sconf specs symEnv md cond tb eb p tbSpec ebSpec hdom g hg
            spec hmergedSpec_eq htbSpec_complete hebSpec_complete env assignment hmatch
            assignment' hagree heval
        exact ⟨env', hc, hmatch'⟩
termination_by (numOfLoopExpComs tb + numOfLoopExpComs eb, sizeOfComs tb + sizeOfComs eb)
decreasing_by
  -- four recursive calls into seCmds_correct (error branch: tb and eb; condVal = true: tb;
  -- condVal = false: eb) -- order-independent, each proved via `first`
  all_goals first
  | (have h1 : numOfLoopExpComs tb ≤ numOfLoopExpComs tb + numOfLoopExpComs eb := by grind
     rcases Nat.lt_or_eq_of_le h1 with h_less | h_equal
     · apply Prod.Lex.left
       exact h_less
     · rw [← h_equal]
       apply Prod.Lex.right
       exact sizeOfComs_a_lt_a_plus_b tb eb)
  | (have h1 : numOfLoopExpComs eb ≤ numOfLoopExpComs tb + numOfLoopExpComs eb := by grind
     rcases Nat.lt_or_eq_of_le h1 with h_less | h_equal
     · apply Prod.Lex.left
       exact h_less
     · rw [← h_equal]
       apply Prod.Lex.right
       rw [← Nat.add_comm]
       exact sizeOfComs_a_lt_a_plus_b eb tb)

theorem seCmd_correct {c : ZKConfig} (gconf : GlobalConfig c) (p : Prog c)
    (specs : List (FuncSpec c))
    (H_simple : ∀ (sconf : SymExecConfig c) (i : ComWithMD c),
      TranslatesCorrectly gconf sconf specs (fun env => evalSimpleCmd gconf env i)
        (fun symEnv => seSimpleCmd gconf sconf symEnv specs i))
    (H_funcCall : ∀ (sconf : SymExecConfig c) (fname : FName) (args : List (SimpleExpr c))
        (outs : List VarID) (md : FuncMD) (func : Func c) (p' : Prog c),
      fetchFunc p fname = Except.ok (FuncWithMD.mk md func, p') →
      (match func with | Func.mk _ _ rets _ => outs.length = rets.length) →
      TranslatesCorrectly gconf sconf specs
        (fun env => evalFuncCallCmd gconf p fname args outs env)
        (fun symEnv => seFuncCall gconf sconf symEnv specs fname args outs))
    (hspecs_cover : ∀ fname', fname' ∈ specs.map (·.name) → fname' ∈ p.map funcWithMDName)
    (hspecs_rets_cover : ∀ fname'' fspec, fetchFuncSpec specs fname'' = Except.ok fspec →
      ∀ md func p'', fetchFunc p fname'' = Except.ok (FuncWithMD.mk md func, p'') →
        match func with | Func.mk _ _ rets _ => fspec.rets.length = rets.length)
    (vars : VarIDSet)
    (sconf : SymExecConfig c) (md : CmdMD) (cmd : Com c) (hshaped : WellShapedCom gconf p cmd) :
    TranslatesCorrectlyGiven gconf sconf specs
      (fun symEnv => ∀ id, id ∈ definedVarsCom vars cmd → symEnv.contains id)
      (fun env => evalCmd gconf p env (ComWithMD.mk md cmd))
      (fun symEnv => seCmd gconf sconf symEnv specs (ComWithMD.mk md cmd)) := by
    match cmd, hshaped with
    | .if_stmt cond tb eb, hshaped =>
        have heq_c : (fun env => evalCmd gconf p env (ComWithMD.mk md (Com.if_stmt cond tb eb)))
            = (fun env => evalIfStmt gconf p env md cond tb eb) := by
          funext env; simp only [evalCmd]
        have heq_s : (fun symEnv => seCmd gconf sconf symEnv specs
              (ComWithMD.mk md (Com.if_stmt cond tb eb)))
            = (fun symEnv => seIfStmt gconf sconf symEnv specs md cond tb eb) := by
          funext symEnv; simp only [seCmd]
        rw [heq_c, heq_s]
        exact seIfStmt_correct gconf p specs H_simple H_funcCall hspecs_cover hspecs_rets_cover vars sconf md cond
          tb eb hshaped
    | .loop_exp repSExp body, hshaped =>
        intro symEnv hbelow hdef spec hspec_eq
        simp only [seCmd] at hspec_eq
        cases htry : tryEvalSimpleExprToFFValue symEnv repSExp with
        | error e => rw [htry] at hspec_eq; simp at hspec_eq
        | ok repVal =>
            rw [htry] at hspec_eq
            simp only [] at hspec_eq
            have hdef' : ∀ id, id ∈ definedVarsCom vars (Com.loop repVal.val body) →
                symEnv.contains id := hdef
            obtain ⟨hin, hmono, hfresh, hbel, houtbel, houtfresh, hsound, hcomplete⟩ :=
              seCmd_correct gconf p specs H_simple H_funcCall hspecs_cover hspecs_rets_cover vars sconf md
                (Com.loop repVal.val body) hshaped symEnv hbelow hdef' spec hspec_eq
            refine ⟨hin, hmono, hfresh, hbel, houtbel, houtfresh, ?_, ?_⟩
            · intro env assignment hmatch env' hconcrete
              have heval_eq : evalSimpleExprToFFValue env repSExp = Except.ok repVal :=
                tryEvalSimpleExprToFFValue_correct symEnv repSExp env assignment repVal hmatch htry
              apply hsound env assignment hmatch env'
              rw [← hconcrete]
              simp only [evalCmd, heval_eq]
            · intro env assignment hmatch assignment' hagree hformula
              obtain ⟨env', hconcrete', hmatch'⟩ :=
                hcomplete env assignment hmatch assignment' hagree hformula
              have heval_eq : evalSimpleExprToFFValue env repSExp = Except.ok repVal :=
                tryEvalSimpleExprToFFValue_correct symEnv repSExp env assignment repVal hmatch htry
              refine ⟨env', ?_, hmatch'⟩
              simp only [evalCmd, heval_eq]
              exact hconcrete'
    | .loop (rep+1) body, hshaped =>
        intro symEnv hbelow hdef spec hspec_eq
        have hbody_pre : ∀ id, id ∈ definedVarsCmds vars body → symEnv.contains id := hdef
        cases hfirstSpec_eq : seCmds gconf { nextVarId := sconf.nextVarId } symEnv specs body with
        | error e => simp [seCmd, hfirstSpec_eq] at hspec_eq
        | ok firstSpec =>
        obtain ⟨hfirstSpec_in, hfirstSpec_mono, hfirstSpec_fresh,
          hfirstSpec_below, hfirstSpec_outbelow, hfirstSpec_outfresh, hfirstSpec_sound,
          hfirstSpec_complete⟩ :=
          seCmds_correct gconf p specs H_simple H_funcCall hspecs_cover hspecs_rets_cover vars { nextVarId := sconf.nextVarId }
            body hshaped symEnv hbelow hbody_pre firstSpec hfirstSpec_eq
        have hfirstDom := seCmds_domain_of_defined gconf { nextVarId := sconf.nextVarId } symEnv
          specs vars body hbody_pre firstSpec hfirstSpec_eq
        rw [← hfirstSpec_in] at hfirstSpec_sound hfirstSpec_complete
        have hrest_pre : ∀ id, id ∈ definedVarsCmds vars body → firstSpec.outSymEnv.contains id :=
          by
            intro id hid
            rw [← hfirstDom id]
            exact hbody_pre id hid
        cases hrestSpec_eq : seCmd gconf { sconf with nextVarId := firstSpec.nextVarId }
            firstSpec.outSymEnv specs (ComWithMD.mk md (Com.loop rep body)) with
        | error e => simp [seCmd, hfirstSpec_eq, hrestSpec_eq] at hspec_eq
        | ok restSpec =>
        obtain ⟨hrestSpec_in, hrestSpec_mono, hrestSpec_fresh,
          hrestSpec_below, hrestSpec_outbelow, hrestSpec_outfresh, hrestSpec_sound,
          hrestSpec_complete⟩ :=
          seCmd_correct gconf p specs H_simple H_funcCall hspecs_cover hspecs_rets_cover vars
            { sconf with nextVarId := firstSpec.nextVarId } md (Com.loop rep body) hshaped
            firstSpec.outSymEnv hfirstSpec_outbelow hrest_pre restSpec hrestSpec_eq
        rw [← hrestSpec_in] at hrestSpec_sound hrestSpec_complete hrestSpec_fresh hrestSpec_outfresh
        have hfirstSpec_sound' : ∀ env assignment, EnvMatches assignment firstSpec.inSymEnv env →
            ∀ env', evalCmds gconf p env body = Except.ok env' →
              ∃ assignment', agreesOnFF (symEnvVars firstSpec.inSymEnv) assignment assignment' ∧
                (∀ n, Var.ffv n ∉ specVars firstSpec → assignment'.ff n = assignment.ff n) ∧
                (∀ n, Var.boolv n ∉ specVars firstSpec → assignment'.bool n = assignment.bool n) ∧
                evalFormula gconf assignment' firstSpec.f (specs.map (·.f)) = Except.ok true ∧
                EnvMatches assignment' firstSpec.outSymEnv env' := by
          intro env assignment hmatch env' hc
          obtain ⟨a', hff, _hbool, hframeff, hframebool, heval, hmatch'⟩ :=
            hfirstSpec_sound env assignment hmatch env' hc
          exact ⟨a', hff, hframeff, hframebool, heval, hmatch'⟩
        have hrestSpec_sound' : ∀ env assignment, EnvMatches assignment restSpec.inSymEnv env →
            ∀ env', evalCmd gconf p env (ComWithMD.mk md (Com.loop rep body)) = Except.ok env' →
              ∃ assignment', agreesOnFF (symEnvVars restSpec.inSymEnv) assignment assignment' ∧
                (∀ n, Var.ffv n ∉ specVars restSpec → assignment'.ff n = assignment.ff n) ∧
                (∀ n, Var.boolv n ∉ specVars restSpec → assignment'.bool n = assignment.bool n) ∧
                evalFormula gconf assignment' restSpec.f (specs.map (·.f)) = Except.ok true ∧
                EnvMatches assignment' restSpec.outSymEnv env' := by
          intro env assignment hmatch env' hc
          obtain ⟨a', hff, _hbool, hframeff, hframebool, heval, hmatch'⟩ :=
            hrestSpec_sound env assignment hmatch env' hc
          exact ⟨a', hff, hframeff, hframebool, heval, hmatch'⟩
        have hconcrete : ∀ env, evalCmd gconf p env (ComWithMD.mk md (Com.loop (rep+1) body)) =
            (evalCmds gconf p env body).bind
              (fun env' => evalCmd gconf p env' (ComWithMD.mk md (Com.loop rep body))) := by
          intro env
          simp only [evalCmd, Except.bind]
          cases evalCmds gconf p env body <;> rfl
        have hspecComposed_eq :
            seqComposition gconf sconf (ComWithMD.mk md (Com.loop (rep+1) body)) firstSpec
              restSpec = Except.ok spec := by
          have h : seCmd gconf sconf symEnv specs (ComWithMD.mk md (Com.loop (rep+1) body)) =
              seqComposition gconf sconf (ComWithMD.mk md (Com.loop (rep+1) body)) firstSpec
                restSpec := by
            simp only [seCmd, hfirstSpec_eq, hrestSpec_eq]
          rw [← h]; exact hspec_eq
        exact seqComposition_correct gconf sconf specs (ComWithMD.mk md (Com.loop (rep+1) body))
          symEnv hbelow
          (fun env => evalCmds gconf p env body)
          (fun env => evalCmd gconf p env (ComWithMD.mk md (Com.loop rep body)))
          (fun env => evalCmd gconf p env (ComWithMD.mk md (Com.loop (rep+1) body)))
          hconcrete firstSpec hfirstSpec_in hfirstSpec_mono hfirstSpec_fresh hfirstSpec_below
          hfirstSpec_outfresh hfirstSpec_sound' hfirstSpec_complete restSpec hrestSpec_in
          hrestSpec_mono hrestSpec_fresh hrestSpec_below hrestSpec_outbelow hrestSpec_outfresh
          hrestSpec_sound' hrestSpec_complete spec hspecComposed_eq
    | .loop 0 _body, _hshaped =>
        intro symEnv hbelow _hdef spec hspec_eq
        obtain ⟨spec2, hspec2_eq, hin, hmono, hfresh, hbel, houtbel, houtfresh, hsound,
          hcomplete⟩ :=
          noop_spec_correct gconf specs sconf symEnv hbelow
            (fun env => evalCmd gconf p env (ComWithMD.mk md (Com.loop 0 _body)))
            (by intro env; simp only [evalCmd]; rfl)
            (fun symEnv' => seCmd gconf sconf symEnv' specs (ComWithMD.mk md (Com.loop 0 _body)))
            (by simp only [seCmd])
        have hspec2 : spec = spec2 := by injection (hspec_eq.symm.trans hspec2_eq)
        subst hspec2
        exact ⟨hin, hmono, hfresh, hbel, houtbel, houtfresh, hsound, hcomplete⟩
    | .func_call outs fname args, _hshaped =>
        have heq_c : (fun env => evalCmd gconf p env
              (ComWithMD.mk md (Com.func_call outs fname args)))
            = (fun env => evalFuncCallCmd gconf p fname args outs env) := by
          funext env; simp only [evalCmd, evalFuncCallCmd]; rfl
        have heq_s : (fun symEnv => seCmd gconf sconf symEnv specs
              (ComWithMD.mk md (Com.func_call outs fname args)))
            = (fun symEnv => seFuncCall gconf sconf symEnv specs fname args outs) := by
          funext symEnv; simp only [seCmd]
        rw [heq_c, heq_s]
        apply TranslatesCorrectlyGiven_of_TranslatesCorrectly
        intro symEnv hbelow spec hspec_eq
        have hspec_eq' := hspec_eq
        simp only [seFuncCall] at hspec_eq'
        cases hfetchSpec_eq : fetchFuncSpec specs fname with
        | error e => rw [hfetchSpec_eq] at hspec_eq'; simp at hspec_eq'
        | ok fspec =>
          have hmem_specs : fname ∈ specs.map (·.name) := by
            obtain ⟨hname_eq, hmem⟩ := fetchFuncSpec_sound specs fname fspec hfetchSpec_eq
            rw [← hname_eq]
            exact List.mem_map_of_mem hmem
          obtain ⟨md', func, p', hfetch⟩ :=
            fetchFunc_of_mem p fname (hspecs_cover fname hmem_specs)
          cases func with
          | mk fname' params rets body =>
              have hlen_fspec : outs.length = fspec.rets.length := by
                rw [hfetchSpec_eq] at hspec_eq'
                simp only [] at hspec_eq'
                cases hargSV : resolveSimpleExprsToSymValue symEnv args with
                | error e => rw [hargSV] at hspec_eq'; simp at hspec_eq'
                | ok argSymVals =>
                rw [hargSV] at hspec_eq'
                simp only [] at hspec_eq'
                cases hinputParams : flattenArgVals fspec.params argSymVals with
                | error e => rw [hinputParams] at hspec_eq'; simp at hspec_eq'
                | ok inputParams =>
                rw [hinputParams] at hspec_eq'
                simp only [] at hspec_eq'
                rcases hmintR : mintFreshRets (c := c) sconf.nextVarId fspec.rets with
                  ⟨nv1, outputParams, outVals⟩
                rcases hmintA : mintFreshAuxParams (c := c) nv1 fspec.numAuxFFVars
                  fspec.numAuxBoolVars with ⟨nv2, auxParams⟩
                rw [hmintR, hmintA] at hspec_eq'
                simp only [] at hspec_eq'
                cases hsv : setVars symEnv outs outVals with
                | error e => rw [hsv] at hspec_eq'; simp at hspec_eq'
                | ok outSymEnv' =>
                have houtVals_len : outVals.length = fspec.rets.length := by
                  have hh := mintFreshRets_outVals_length (c := c) sconf.nextVarId fspec.rets
                  rw [hmintR] at hh; exact hh
                rw [setVars_length_of_ok outs outVals symEnv outSymEnv' hsv, houtVals_len]
              have harity : outs.length = rets.length := by
                rw [hlen_fspec]
                exact hspecs_rets_cover fname fspec hfetchSpec_eq md'
                  (Func.mk fname' params rets body) p' hfetch
              exact H_funcCall sconf fname args outs md' (Func.mk fname' params rets body) p'
                hfetch harity symEnv hbelow spec hspec_eq
    | .assign out e, _hshaped =>
        have heq_c : (fun env => evalCmd gconf p env (ComWithMD.mk md (Com.assign out e)))
            = (fun env => evalSimpleCmd gconf env (ComWithMD.mk md (Com.assign out e))) := by
          funext env; simp only [evalCmd]
        have heq_s : (fun symEnv => seCmd gconf sconf symEnv specs
              (ComWithMD.mk md (Com.assign out e)))
            = (fun symEnv => seSimpleCmd gconf sconf symEnv specs
              (ComWithMD.mk md (Com.assign out e))) := by
          funext symEnv; simp only [seCmd]
        rw [heq_c, heq_s]
        exact TranslatesCorrectlyGiven_of_TranslatesCorrectly _ _ _ _ _ _
          (H_simple sconf (ComWithMD.mk md (Com.assign out e)))
    | .new_array out size, _hshaped =>
        have heq_c : (fun env => evalCmd gconf p env (ComWithMD.mk md (Com.new_array out size)))
            = (fun env => evalSimpleCmd gconf env (ComWithMD.mk md (Com.new_array out size))) := by
          funext env; simp only [evalCmd]
        have heq_s : (fun symEnv => seCmd gconf sconf symEnv specs
              (ComWithMD.mk md (Com.new_array out size)))
            = (fun symEnv => seSimpleCmd gconf sconf symEnv specs
              (ComWithMD.mk md (Com.new_array out size))) := by
          funext symEnv; simp only [seCmd]
        rw [heq_c, heq_s]
        exact TranslatesCorrectlyGiven_of_TranslatesCorrectly _ _ _ _ _ _
          (H_simple sconf (ComWithMD.mk md (Com.new_array out size)))
    | .read_array out arr idx, _hshaped =>
        have heq_c : (fun env => evalCmd gconf p env
              (ComWithMD.mk md (Com.read_array out arr idx)))
            = (fun env => evalSimpleCmd gconf env
              (ComWithMD.mk md (Com.read_array out arr idx))) := by
          funext env; simp only [evalCmd]
        have heq_s : (fun symEnv => seCmd gconf sconf symEnv specs
              (ComWithMD.mk md (Com.read_array out arr idx)))
            = (fun symEnv => seSimpleCmd gconf sconf symEnv specs
              (ComWithMD.mk md (Com.read_array out arr idx))) := by
          funext symEnv; simp only [seCmd]
        rw [heq_c, heq_s]
        exact TranslatesCorrectlyGiven_of_TranslatesCorrectly _ _ _ _ _ _
          (H_simple sconf (ComWithMD.mk md (Com.read_array out arr idx)))
    | .write_array arr idx value, _hshaped =>
        have heq_c : (fun env => evalCmd gconf p env
              (ComWithMD.mk md (Com.write_array arr idx value)))
            = (fun env => evalSimpleCmd gconf env
              (ComWithMD.mk md (Com.write_array arr idx value))) := by
          funext env; simp only [evalCmd]
        have heq_s : (fun symEnv => seCmd gconf sconf symEnv specs
              (ComWithMD.mk md (Com.write_array arr idx value)))
            = (fun symEnv => seSimpleCmd gconf sconf symEnv specs
              (ComWithMD.mk md (Com.write_array arr idx value))) := by
          funext symEnv; simp only [seCmd]
        rw [heq_c, heq_s]
        exact TranslatesCorrectlyGiven_of_TranslatesCorrectly _ _ _ _ _ _
          (H_simple sconf (ComWithMD.mk md (Com.write_array arr idx value)))
    | .copy_array out arr, _hshaped =>
        have heq_c : (fun env => evalCmd gconf p env (ComWithMD.mk md (Com.copy_array out arr)))
            = (fun env => evalSimpleCmd gconf env (ComWithMD.mk md (Com.copy_array out arr))) := by
          funext env; simp only [evalCmd]
        have heq_s : (fun symEnv => seCmd gconf sconf symEnv specs
              (ComWithMD.mk md (Com.copy_array out arr)))
            = (fun symEnv => seSimpleCmd gconf sconf symEnv specs
              (ComWithMD.mk md (Com.copy_array out arr))) := by
          funext symEnv; simp only [seCmd]
        rw [heq_c, heq_s]
        exact TranslatesCorrectlyGiven_of_TranslatesCorrectly _ _ _ _ _ _
          (H_simple sconf (ComWithMD.mk md (Com.copy_array out arr)))
termination_by (numOfLoopExpCom (ComWithMD.mk md cmd), sizeOfCom (ComWithMD.mk md cmd))
decreasing_by
  all_goals first
    | (simp only [numOfLoopExpCom]; apply Prod.Lex.left; grind)
    | (apply Prod.Lex.right; simp only [sizeOfCom]; grind)

theorem seCmds_correct {c : ZKConfig} (gconf : GlobalConfig c) (p : Prog c)
    (specs : List (FuncSpec c))
    (H_simple : ∀ (sconf : SymExecConfig c) (i : ComWithMD c),
      TranslatesCorrectly gconf sconf specs (fun env => evalSimpleCmd gconf env i)
        (fun symEnv => seSimpleCmd gconf sconf symEnv specs i))
    (H_funcCall : ∀ (sconf : SymExecConfig c) (fname : FName) (args : List (SimpleExpr c))
        (outs : List VarID) (md : FuncMD) (func : Func c) (p' : Prog c),
      fetchFunc p fname = Except.ok (FuncWithMD.mk md func, p') →
      (match func with | Func.mk _ _ rets _ => outs.length = rets.length) →
      TranslatesCorrectly gconf sconf specs
        (fun env => evalFuncCallCmd gconf p fname args outs env)
        (fun symEnv => seFuncCall gconf sconf symEnv specs fname args outs))
    (hspecs_cover : ∀ fname', fname' ∈ specs.map (·.name) → fname' ∈ p.map funcWithMDName)
    (hspecs_rets_cover : ∀ fname'' fspec, fetchFuncSpec specs fname'' = Except.ok fspec →
      ∀ md func p'', fetchFunc p fname'' = Except.ok (FuncWithMD.mk md func, p'') →
        match func with | Func.mk _ _ rets _ => fspec.rets.length = rets.length)
    (vars : VarIDSet)
    (sconf : SymExecConfig c) (cmds : List (ComWithMD c)) (hshaped : WellShapedCmds gconf p cmds) :
    TranslatesCorrectlyGiven gconf sconf specs
      (fun symEnv => ∀ id, id ∈ definedVarsCmds vars cmds → symEnv.contains id)
      (fun env => evalCmds gconf p env cmds)
      (fun symEnv => seCmds gconf sconf symEnv specs cmds) := by
  cases cmds with
  | nil =>
      intro symEnv hbelow _hdef spec hspec_eq
      obtain ⟨spec2, hspec2_eq, hin, hmono, hfresh, hbel, houtbel, houtfresh, hsound, hcomplete⟩ :=
        noop_spec_correct gconf specs sconf symEnv hbelow
          (fun env => evalCmds gconf p env [])
          (by intro env; simp only [evalCmds])
          (fun symEnv' => seCmds gconf sconf symEnv' specs [])
          (by simp only [seCmds]; rfl)
      have hspec2 : spec = spec2 := by injection (hspec_eq.symm.trans hspec2_eq)
      subst hspec2
      exact ⟨hin, hmono, hfresh, hbel, houtbel, houtfresh, hsound, hcomplete⟩
  | cons cmd rest =>
      cases cmd with
      | mk md cmd' =>
        simp only [WellShapedCmds] at hshaped
        obtain ⟨hshapedHead, hshapedRest⟩ := hshaped
        intro symEnv hbelow hdef spec hspec_eq
        have hcmd_pre : ∀ id, id ∈ definedVarsCom vars cmd' → symEnv.contains id :=
          fun id hid => hdef id (by
            simp only [definedVarsCmds]
            exact definedVarsCmds_mono rest (definedVarsCom vars cmd') id hid)
        cases hcmdSpec_eq : seCmd gconf sconf symEnv specs (ComWithMD.mk md cmd') with
        | error e => simp [seCmds, hcmdSpec_eq] at hspec_eq
        | ok cmdSpec =>
        obtain ⟨hcmdSpec_in, hcmdSpec_mono, hcmdSpec_fresh, hcmdSpec_below,
          hcmdSpec_outbelow, hcmdSpec_outfresh, hcmdSpec_sound, hcmdSpec_complete⟩ :=
          seCmd_correct gconf p specs H_simple H_funcCall hspecs_cover hspecs_rets_cover vars sconf md cmd'
            hshapedHead symEnv hbelow hcmd_pre cmdSpec hcmdSpec_eq
        have hcmdDom := seCmd_domain_of_defined gconf sconf symEnv specs vars md cmd' hcmd_pre
          cmdSpec hcmdSpec_eq
        rw [← hcmdSpec_in] at hcmdSpec_sound hcmdSpec_complete
        have hrest_pre : ∀ id, id ∈ definedVarsCmds vars rest → cmdSpec.outSymEnv.contains id := by
          intro id hid
          rw [← hcmdDom id]
          exact hdef id (by
            simp only [definedVarsCmds]
            exact definedVarsCmds_subset_mono rest vars (definedVarsCom vars cmd')
              (fun id' hid' => definedVarsCom_mono cmd' vars id' hid') id hid)
        cases hcmdsSpec_eq : seCmds gconf { sconf with nextVarId := cmdSpec.nextVarId }
            cmdSpec.outSymEnv specs rest with
        | error e => simp [seCmds, hcmdSpec_eq, hcmdsSpec_eq] at hspec_eq
        | ok cmdsSpec =>
        obtain ⟨hcmdsSpec_in, hcmdsSpec_mono, hcmdsSpec_fresh,
          hcmdsSpec_below, hcmdsSpec_outbelow, hcmdsSpec_outfresh, hcmdsSpec_sound,
          hcmdsSpec_complete⟩ :=
          seCmds_correct gconf p specs H_simple H_funcCall hspecs_cover hspecs_rets_cover vars
            { sconf with nextVarId := cmdSpec.nextVarId } rest hshapedRest
            cmdSpec.outSymEnv hcmdSpec_outbelow hrest_pre cmdsSpec hcmdsSpec_eq
        rw [← hcmdsSpec_in] at hcmdsSpec_sound hcmdsSpec_complete hcmdsSpec_fresh hcmdsSpec_outfresh
        have hcmdSpec_sound' : ∀ env assignment, EnvMatches assignment cmdSpec.inSymEnv env →
            ∀ env', evalCmd gconf p env (ComWithMD.mk md cmd') = Except.ok env' →
              ∃ assignment', agreesOnFF (symEnvVars cmdSpec.inSymEnv) assignment assignment' ∧
                (∀ n, Var.ffv n ∉ specVars cmdSpec → assignment'.ff n = assignment.ff n) ∧
                (∀ n, Var.boolv n ∉ specVars cmdSpec → assignment'.bool n = assignment.bool n) ∧
                evalFormula gconf assignment' cmdSpec.f (specs.map (·.f)) = Except.ok true ∧
                EnvMatches assignment' cmdSpec.outSymEnv env' := by
          intro env assignment hmatch env' hc
          obtain ⟨a', hff, _hbool, hframeff, hframebool, heval, hmatch'⟩ :=
            hcmdSpec_sound env assignment hmatch env' hc
          exact ⟨a', hff, hframeff, hframebool, heval, hmatch'⟩
        have hcmdsSpec_sound' : ∀ env assignment, EnvMatches assignment cmdsSpec.inSymEnv env →
            ∀ env', evalCmds gconf p env rest = Except.ok env' →
              ∃ assignment', agreesOnFF (symEnvVars cmdsSpec.inSymEnv) assignment assignment' ∧
                (∀ n, Var.ffv n ∉ specVars cmdsSpec → assignment'.ff n = assignment.ff n) ∧
                (∀ n, Var.boolv n ∉ specVars cmdsSpec → assignment'.bool n = assignment.bool n) ∧
                evalFormula gconf assignment' cmdsSpec.f (specs.map (·.f)) = Except.ok true ∧
                EnvMatches assignment' cmdsSpec.outSymEnv env' := by
          intro env assignment hmatch env' hc
          obtain ⟨a', hff, _hbool, hframeff, hframebool, heval, hmatch'⟩ :=
            hcmdsSpec_sound env assignment hmatch env' hc
          exact ⟨a', hff, hframeff, hframebool, heval, hmatch'⟩
        have hconcrete : ∀ env, evalCmds gconf p env (ComWithMD.mk md cmd' :: rest) =
            (evalCmd gconf p env (ComWithMD.mk md cmd')).bind
              (fun env' => evalCmds gconf p env' rest) := by
          intro env
          simp only [evalCmds, Except.bind]
          cases evalCmd gconf p env (ComWithMD.mk md cmd') <;> rfl
        have hspecComposed_eq :
            seqComposition gconf sconf (ComWithMD.mk md cmd') cmdSpec cmdsSpec =
              Except.ok spec := by
          have h : seCmds gconf sconf symEnv specs (ComWithMD.mk md cmd' :: rest) =
              seqComposition gconf sconf (ComWithMD.mk md cmd') cmdSpec cmdsSpec := by
            simp only [seCmds, hcmdSpec_eq, hcmdsSpec_eq]
          rw [← h]; exact hspec_eq
        exact seqComposition_correct gconf sconf specs (ComWithMD.mk md cmd') symEnv hbelow
          (fun env => evalCmd gconf p env (ComWithMD.mk md cmd'))
          (fun env => evalCmds gconf p env rest)
          (fun env => evalCmds gconf p env (ComWithMD.mk md cmd' :: rest))
          hconcrete cmdSpec hcmdSpec_in hcmdSpec_mono hcmdSpec_fresh hcmdSpec_below
          hcmdSpec_outfresh hcmdSpec_sound' hcmdSpec_complete cmdsSpec hcmdsSpec_in
          hcmdsSpec_mono hcmdsSpec_fresh hcmdsSpec_below hcmdsSpec_outbelow hcmdsSpec_outfresh
          hcmdsSpec_sound' hcmdsSpec_complete spec hspecComposed_eq
termination_by (numOfLoopExpComs cmds, sizeOfComs cmds)
decreasing_by
  -- cross-call into seCmd_correct, on the head `cmd'`
  · have hcmds_eq : cmds = ComWithMD.mk md cmd' :: rest := by
      rw [‹cmds = cmd :: rest›, ‹cmd = ComWithMD.mk md cmd'›]
    rw [hcmds_eq]
    have h1 : numOfLoopExpCom (ComWithMD.mk md cmd') ≤
        numOfLoopExpCom (ComWithMD.mk md cmd') + numOfLoopExpComs rest := by grind
    rcases Nat.lt_or_eq_of_le h1 with h_less | h_equal
    · apply Prod.Lex.left
      simp only [numOfLoopExpComs]
      exact h_less
    · simp only [numOfLoopExpComs]
      rw [← h_equal]
      apply Prod.Lex.right
      simp only [sizeOfComs]
      grind
  -- recursive call into seCmds_correct itself, on `rest`
  · have hcmds_eq : cmds = ComWithMD.mk md cmd' :: rest := by
      rw [‹cmds = cmd :: rest›, ‹cmd = ComWithMD.mk md cmd'›]
    have h1 : numOfLoopExpComs rest ≤
        numOfLoopExpCom (ComWithMD.mk md cmd') + numOfLoopExpComs rest := by grind
    rcases Nat.lt_or_eq_of_le h1 with h_less | h_equal
    · apply Prod.Lex.left
      rw [hcmds_eq]
      simp only [numOfLoopExpComs]
      exact h_less
    · rw [hcmds_eq]
      simp only [numOfLoopExpComs]
      rw [← h_equal]
      apply Prod.Lex.right
      simp only [sizeOfComs]
      grind

end


end Corellzk2smt.SymExec.PartialCorrectness.Correctness
