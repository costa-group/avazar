import Corellzk2smt.SymExec.Lemmas
import Corellzk2smt.Language.Core.Analysis.WellShaped

/- Shared machinery for `seCmd`/`seCmds`/`seIfStmt`/`seFuncCall` correctness: `evalFuncCallCmd`,
   the `_prepend_indep`/`_names_below` families (how symbolic execution's output/name-usage
   behaves under prepending a fresh, name-disjoint spec), `noop_spec_correct`, and
   `seqComposition_correct`. None of this is stated in terms of `TranslatesCorrectly` itself, so
   it's reused unchanged by both the (now-removed) unconditional formalization and the current
   conditional one in `SymExec/PartialCorrectness/Correctness.lean` -- see that file's header for
   the actual `seCmd_correct`/`seCmds_correct`/`seIfStmt_correct` theorems built on top of this.

   Every theorem below states its own parameters explicitly (`gconf`, `p`, `specs`, ...) rather
   than relying on a shared `variable` block -- matching `SymExec/Lemmas.lean`'s house style,
   and sidestepping `variable` auto-inclusion order subtleties across a `mutual` block. -/

namespace Corellzk2smt.SymExec.Correctness

open Corellzk2smt.Config
open Corellzk2smt.Language.Core.Syntax.AST
open Corellzk2smt.Language.Core.Semantics.Basic
open Corellzk2smt.Language.Core.Semantics.BigStep
open Corellzk2smt.Language.Core.Analysis.WellShaped
open Corellzk2smt.SymExec.Basic
open Corellzk2smt.SymExec.BigStep
open Corellzk2smt.FFConstraints.Basic
open Corellzk2smt.FFConstraints.Satisfiability
open Corellzk2smt.FFConstraints.Satisfiability_th
open Corellzk2smt.SymExec.Lemmas

/-- The concrete counterpart of `seFuncCall`: evaluate the arguments, call the function, bind
    the results into the outputs. Mirrors `evalCmd`'s `Com.func_call` case exactly (no monadic
    `.bind`, per house style). -/
def evalFuncCallCmd {c : ZKConfig} (gconf : GlobalConfig c) (p : Prog c) (fname : FName)
    (args : List (SimpleExpr c)) (outs : List VarID) (env : Env c) : Except String (Env c) :=
  match evalSimpleExprsToValue env args with
  | Except.error err => Except.error err
  | Except.ok argVals =>
    match evalFunCall gconf p fname argVals with
    | Except.error err => Except.error err
    | Except.ok outVals =>
      match setVars env outs outVals with
      | Except.error err => Except.error err
      | Except.ok vars_env => Except.ok vars_env

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

/-- The number of constraint-variable slots a single `.ff`/`.array size` type occupies: 1 for
    `.ff`, `size` for `.array size` -- matches `mintFreshParam`/`mintFreshRetWithEq`'s own
    var-minting counts (`mintFreshRetParam`/`flattenArgVal`, used at a *call site*, mint/consume
    exactly this many slots too). Shared between `FuncCorrectness.lean` and
    `FuncCallCorrectness.lean` (neither can import the other), hence living here. -/
def typeSize (t : VarType) : Nat := match t with | .ff => 1 | .array n => n

/-- `Param`-level convenience wrapper for `typeSize`. -/
def paramSize (p : Param) : Nat := typeSize p.type

/-- Total flattened constraint-variable count for a list of params (sum of each one's
    `paramSize`) -- what `mintFreshParams`/`mintFreshRetsWithEq`/`mintFreshRets`/`flattenArgVals`
    actually advance `nextVarId` by / how many flattened elements they produce or consume. -/
def totalParamSize (params : List Param) : Nat := (params.map paramSize).sum

@[simp] theorem totalParamSize_nil : totalParamSize ([] : List Param) = 0 := rfl

@[simp] theorem totalParamSize_cons (p : Param) (ps : List Param) :
    totalParamSize (p :: ps) = paramSize p + totalParamSize ps := by
  simp [totalParamSize]

/-- The fresh symbolic value a single `.ff`/`.array size` type gets minted, starting at
    `nextVarId` -- the shared closed form both `mintFreshParam` (`SymExec/BigStep.lean`, entry
    env for a function's own params/rets) and `mintFreshRetParam` (call-site fresh output vars)
    produce for a single param/ret, letting both be characterized against ONE definition instead
    of two independent ones. -/
def freshRetSymValue {c : ZKConfig} (nextVarId : Nat) (type : VarType) : SymValue c :=
  match type with
  | .ff => SymValue.simple (SimpleSymVal.ffvar { var := nextVarId, bits := none })
  | .array size => SymValue.array ((List.range size).map (fun i =>
      SimpleSymVal.ffvar { var := nextVarId + i, bits := none })).toArray

end Corellzk2smt.SymExec.Correctness
