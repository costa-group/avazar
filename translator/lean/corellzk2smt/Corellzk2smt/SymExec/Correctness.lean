import Corellzk2smt.SymExec.Lemmas
import Corellzk2smt.Language.Core.Analysis.WellShaped

/- Step 4/5 of the `seCmd`/`seCmds`/`seIfStmt` correctness plan (see the session's design
   discussion): `seSimpleCmd`/`seFuncCall` stay abstract (they need encoding-specific machinery
   not yet designed), so their correctness is taken as a hypothesis (`H_simple`/`H_funcCall`,
   `TranslatesCorrectly`-shaped) rather than proven. Everything else -- `seCmd`, `seCmds`,
   `seIfStmt` -- is proven correct from those hypotheses plus the generic composition lemmas
   already built (`seqComposition_sound`/`_complete`, `mergeIfBranches_sound`/`_complete`).

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

/-- If `fspec_new.name` isn't reachable from `p` at all (`fetchFunc` fails on it), then within
    any `WellShapedCom`/`WellShapedCmds`-checked command tree against `p` (which requires every
    `func_call` site to have `fetchFunc p fname` actually succeed), no `func_call`'s own `fname`
    can ever equal `fspec_new.name` -- the two facts would force `fetchFunc p fspec_new.name` to
    both succeed and fail. -/
theorem funcCall_name_ne_of_unreachable {c : ZKConfig} (p : Prog c) (fspec_new : FuncSpec c)
    (hunreach : ∀ r, fetchFunc p fspec_new.name ≠ Except.ok r)
    (fname : FName) (md : FuncMD) (func : Func c) (p' : Prog c)
    (hfetch : fetchFunc p fname = Except.ok (FuncWithMD.mk md func, p')) :
    fspec_new.name ≠ fname := by
  intro heq
  exact hunreach (FuncWithMD.mk md func, p') (heq ▸ hfetch)

mutual
theorem seIfStmt_prepend_indep {c : ZKConfig} (gconf : GlobalConfig c) (p : Prog c)
    (fspec_new : FuncSpec c) (hunreach : ∀ r, fetchFunc p fspec_new.name ≠ Except.ok r)
    (sconf : SymExecConfig c) (symEnv : SymEnv c) (specs : List (FuncSpec c))
    (md : CmdMD) (cond : Cond c) (tb eb : List (ComWithMD c))
    (hshaped : WellShapedCom gconf p (Com.if_stmt cond tb eb)) :
    seIfStmt gconf sconf symEnv (fspec_new :: specs) md cond tb eb =
      seIfStmt gconf sconf symEnv specs md cond tb eb := by
  obtain ⟨_hcond, hshapedTb, hshapedEb, _hshapeAgree⟩ := hshaped
  have ihTb := seCmds_prepend_indep gconf p fspec_new hunreach sconf symEnv specs tb hshapedTb
  have ihEb := seCmds_prepend_indep gconf p fspec_new hunreach sconf symEnv specs eb hshapedEb
  simp only [seIfStmt, ihTb, ihEb, mergeIfBranches]
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

theorem seCmd_prepend_indep {c : ZKConfig} (gconf : GlobalConfig c) (p : Prog c)
    (fspec_new : FuncSpec c) (hunreach : ∀ r, fetchFunc p fspec_new.name ≠ Except.ok r)
    (sconf : SymExecConfig c) (symEnv : SymEnv c) (specs : List (FuncSpec c))
    (i : ComWithMD c) (hshaped : WellShapedCom gconf p (match i with | .mk _ cmd => cmd)) :
    seCmd gconf sconf symEnv (fspec_new :: specs) i = seCmd gconf sconf symEnv specs i := by
  match i, hshaped with
  | .mk md cmd, hshaped =>
    match cmd, hshaped with
    | .if_stmt cond tb eb, hshaped =>
        simp only [seCmd]
        exact seIfStmt_prepend_indep gconf p fspec_new hunreach sconf symEnv specs md cond tb eb
          hshaped
    | .loop_exp repSExp body, hshaped =>
        have hshapedBody : WellShapedCmds gconf p body := hshaped.2
        simp only [seCmd]
        cases tryEvalSimpleExprToFFValue symEnv repSExp with
        | error e => rfl
        | ok rep =>
            exact seCmd_prepend_indep gconf p fspec_new hunreach sconf symEnv specs
              (ComWithMD.mk md (Com.loop rep.val body)) hshapedBody
    | .loop (rep + 1) body, hshaped =>
        have hshapedBody : WellShapedCmds gconf p body := hshaped
        simp only [seCmd]
        have ihBody := seCmds_prepend_indep gconf p fspec_new hunreach sconf symEnv specs body
          hshapedBody
        rw [ihBody]
        cases seCmds gconf sconf symEnv specs body with
        | error e => rfl
        | ok specFirstIter =>
            have ihRest := seCmd_prepend_indep gconf p fspec_new hunreach
              { sconf with nextVarId := specFirstIter.nextVarId } specFirstIter.outSymEnv specs
              (ComWithMD.mk md (Com.loop rep body)) hshapedBody
            simp only [seqComposition]
            rw [ihRest]
    | .loop 0 _body, _hshaped => simp only [seCmd]
    | .func_call outs fname args, hshaped =>
        obtain ⟨md', func, p', hfetch, _⟩ := hshaped
        have hne : fspec_new.name ≠ fname :=
          funcCall_name_ne_of_unreachable p fspec_new hunreach fname md' func p' hfetch
        simp only [seCmd]
        exact seFuncCall_prepend_indep gconf sconf symEnv fspec_new specs fname args outs hne
    | .assign _ _, _hshaped => simp only [seCmd, seSimpleCmd]
    | .new_array _ _, _hshaped => simp only [seCmd, seSimpleCmd]
    | .read_array _ _ _, _hshaped => simp only [seCmd, seSimpleCmd]
    | .write_array _ _ _, _hshaped => simp only [seCmd, seSimpleCmd]
    | .copy_array _ _, _hshaped => simp only [seCmd, seSimpleCmd]
termination_by (numOfLoopExpCom i, sizeOfCom i)
decreasing_by
  -- recursive call seIfStmt_prepend_indep
  · simp only [numOfLoopExpCom]
    apply Prod.Lex.right
    simp only [sizeOfCom]
    grind
  -- the case of loop_exp
  · simp only [numOfLoopExpCom]
    apply Prod.Lex.left
    grind
  -- the case of loop with concrete repetitions -- first iteration
  · simp only [numOfLoopExpCom]
    apply Prod.Lex.right
    simp only [sizeOfCom]
    grind
  -- the case of loop with concrete repetitions -- rest of iterations
  · simp only [numOfLoopExpCom]
    apply Prod.Lex.right
    simp only [sizeOfCom]
    grind

theorem seCmds_prepend_indep {c : ZKConfig} (gconf : GlobalConfig c) (p : Prog c)
    (fspec_new : FuncSpec c) (hunreach : ∀ r, fetchFunc p fspec_new.name ≠ Except.ok r)
    (sconf : SymExecConfig c) (symEnv : SymEnv c) (specs : List (FuncSpec c))
    (cmds : List (ComWithMD c)) (hshaped : WellShapedCmds gconf p cmds) :
    seCmds gconf sconf symEnv (fspec_new :: specs) cmds = seCmds gconf sconf symEnv specs cmds := by
  match cmds, hshaped with
  | [], _hshaped => simp only [seCmds]
  | cmd :: rest, hshaped =>
    match cmd, hshaped with
    | ComWithMD.mk md cmd', hshaped =>
      obtain ⟨hshapedCmd, hshapedRest⟩ := hshaped
      have ihCmd := seCmd_prepend_indep gconf p fspec_new hunreach sconf symEnv specs
        (ComWithMD.mk md cmd') hshapedCmd
      simp only [seCmds]
      rw [ihCmd]
      cases seCmd gconf sconf symEnv specs (ComWithMD.mk md cmd') with
      | error e => rfl
      | ok cmdSpec =>
          have ihRest := seCmds_prepend_indep gconf p fspec_new hunreach
            { sconf with nextVarId := cmdSpec.nextVarId } cmdSpec.outSymEnv specs rest hshapedRest
          simp only [seqComposition]
          rw [ihRest]
termination_by (numOfLoopExpComs cmds, sizeOfComs cmds)
decreasing_by
  -- recursive call on cmd
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
  -- recursive call on rest
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
    (md : CmdMD) (cond : Cond c) (tb eb : List (ComWithMD c))
    (hshaped : WellShapedCom gconf p (Com.if_stmt cond tb eb))
    (spec : CmdsSpec c) (hspec_eq : seIfStmt gconf sconf symEnv specs md cond tb eb = Except.ok spec) :
    FormulaNamesBelow spec.f badName := by
  obtain ⟨_hcond, hshapedTb, hshapedEb, _hshapeAgree⟩ := hshaped
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
                hspecs_wf tb hshapedTb tbSpec htb
              have ihEb := seCmds_names_below gconf p badName hunreach sconf symEnv specs
                hspecs_wf eb hshapedEb ebSpec heb
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
          exact seCmds_names_below gconf p badName hunreach sconf symEnv specs hspecs_wf tb
            hshapedTb spec hspec_eq
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hspec_eq
          exact seCmds_names_below gconf p badName hunreach sconf symEnv specs hspecs_wf eb
            hshapedEb spec hspec_eq
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
    (i : ComWithMD c) (hshaped : WellShapedCom gconf p (match i with | .mk _ cmd => cmd))
    (spec : CmdsSpec c) (hspec_eq : seCmd gconf sconf symEnv specs i = Except.ok spec) :
    FormulaNamesBelow spec.f badName := by
  match i, hshaped with
  | .mk md cmd, hshaped =>
    match cmd, hshaped with
    | .if_stmt cond tb eb, hshaped =>
        simp only [seCmd] at hspec_eq
        exact seIfStmt_names_below gconf p badName hunreach sconf symEnv specs hspecs_wf md cond
          tb eb hshaped spec hspec_eq
    | .loop_exp repSExp body, hshaped =>
        have hshapedBody : WellShapedCmds gconf p body := hshaped.2
        simp only [seCmd] at hspec_eq
        cases hrep : tryEvalSimpleExprToFFValue symEnv repSExp with
        | error e => rw [hrep] at hspec_eq; simp at hspec_eq
        | ok rep =>
            rw [hrep] at hspec_eq
            simp only [] at hspec_eq
            exact seCmd_names_below gconf p badName hunreach sconf symEnv specs hspecs_wf
              (ComWithMD.mk md (Com.loop rep.val body)) hshapedBody spec hspec_eq
    | .loop (rep + 1) body, hshaped =>
        have hshapedBody : WellShapedCmds gconf p body := hshaped
        simp only [seCmd] at hspec_eq
        cases hfirst : seCmds gconf sconf symEnv specs body with
        | error msg => rw [hfirst] at hspec_eq; simp at hspec_eq
        | ok specFirstIter =>
            rw [hfirst] at hspec_eq
            simp only [] at hspec_eq
            have ihFirst := seCmds_names_below gconf p badName hunreach sconf symEnv specs
              hspecs_wf body hshapedBody specFirstIter hfirst
            cases hrest : seCmd gconf { sconf with nextVarId := specFirstIter.nextVarId }
                specFirstIter.outSymEnv specs (ComWithMD.mk md (Com.loop rep body)) with
            | error msg => rw [hrest] at hspec_eq; simp at hspec_eq
            | ok specRestIter =>
                rw [hrest] at hspec_eq
                simp only [] at hspec_eq
                have ihRest := seCmd_names_below gconf p badName hunreach
                  { sconf with nextVarId := specFirstIter.nextVarId } specFirstIter.outSymEnv specs
                  hspecs_wf (ComWithMD.mk md (Com.loop rep body)) hshapedBody specRestIter hrest
                simp only [seqComposition] at hspec_eq
                injection hspec_eq with hspec_eq
                simp only [FormulaNamesBelow, ← hspec_eq]
                exact ⟨ihFirst, ihRest⟩
    | .loop 0 _body, _hshaped =>
        simp only [seCmd] at hspec_eq
        injection hspec_eq with hspec_eq
        rw [← hspec_eq]
        exact default_names_below badName
    | .func_call outs fname args, hshaped =>
        obtain ⟨md', func, p', hfetch, _⟩ := hshaped
        have hne : badName ≠ fname := by
          intro heq
          exact hunreach (FuncWithMD.mk md' func, p') (heq ▸ hfetch)
        simp only [seCmd] at hspec_eq
        simp only [seFuncCall] at hspec_eq
        cases hfetchSpec : fetchFuncSpec specs fname with
        | error e => rw [hfetchSpec] at hspec_eq; simp at hspec_eq
        | ok fspec =>
            rw [hfetchSpec] at hspec_eq
            simp only [] at hspec_eq
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
                        obtain ⟨hspecname, hspecmem⟩ :=
                          fetchFuncSpec_sound specs fname fspec hfetchSpec
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
            (ComWithMD.mk md cmd') hshapedCmd cmdSpec hcmd
          cases hrest : seCmds gconf { sconf with nextVarId := cmdSpec.nextVarId }
              cmdSpec.outSymEnv specs rest with
          | error e => rw [hrest] at hspec_eq; simp at hspec_eq
          | ok cmdsSpec =>
              rw [hrest] at hspec_eq
              simp only [] at hspec_eq
              have ihRest := seCmds_names_below gconf p badName hunreach
                { sconf with nextVarId := cmdSpec.nextVarId } cmdSpec.outSymEnv specs hspecs_wf
                rest hshapedRest cmdsSpec hrest
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
-- Lifting `TranslatesCorrectly` across prepending one more (name-disjoint) spec
-- ---------------------------------------------------------------------------

/-- If `concrete`/`symbolic` translate correctly against `specs`, they still do against
    `fspec_new :: specs`, given `fspec_new`'s name is disjoint from every spec already in
    `specs`, and every formula `symbolic` can ever produce never directly calls
    `fspec_new.f.name` (`hnb` -- established, for the actual `symbolic := fun symEnv => seCmds
    gconf sconf symEnv specs body` instances this gets applied to, by `seCmds_names_below`).
    The two `TranslatesCorrectly` clauses that mention `specs` at all (`hsound`/`hcomplete`,
    via `evalFormula _ _ _ (specs.map (·.f))`) are the only place this matters: soundness only
    ever needs the *forward* direction (`evalFormula_prepend_indep`, small list succeeds ⇒ big
    list succeeds), while completeness needs the *reverse* direction, which only holds thanks to
    `hnb` (`evalFormula_names_below_indep`). Every other clause is `specs`-independent and
    carries over unchanged. -/
theorem TranslatesCorrectly_prepend {c : ZKConfig} (gconf : GlobalConfig c)
    (sconf : SymExecConfig c) (specs : List (FuncSpec c)) (fspec_new : FuncSpec c)
    (hne : ∀ spec ∈ specs, fspec_new.f.name ≠ spec.f.name)
    (concrete : Env c → Except String (Env c))
    (symbolic : SymEnv c → Except String (CmdsSpec c))
    (hnb : ∀ (symEnv : SymEnv c) (spec : CmdsSpec c), symbolic symEnv = Except.ok spec →
      FormulaNamesBelow spec.f fspec_new.f.name)
    (h : TranslatesCorrectly gconf sconf specs concrete symbolic) :
    TranslatesCorrectly gconf sconf (fspec_new :: specs) concrete symbolic := by
  intro symEnv hvarSetBelow
  obtain ⟨spec, hsym, hin, hnext, hspecVars1, hspecVars2, houtVars1, houtVars2, hsound,
    hcomplete⟩ := h symEnv hvarSetBelow
  have hnb_spec := hnb symEnv spec hsym
  have hmap : ((fspec_new :: specs).map (·.f) : List (FFMacro c)) =
      fspec_new.f :: specs.map (·.f) := List.map_cons ..
  refine ⟨spec, hsym, hin, hnext, hspecVars1, hspecVars2, houtVars1, houtVars2, ?_, ?_⟩
  · intro env assignment hmatch env' hconcrete
    obtain ⟨assignment', hagreeFF, hagreeBool, hffout, hboolout, hformula, hmatch'⟩ :=
      hsound env assignment hmatch env' hconcrete
    refine ⟨assignment', hagreeFF, hagreeBool, hffout, hboolout, ?_, hmatch'⟩
    rw [hmap]
    exact evalFormula_prepend_indep gconf [fspec_new.f] assignment' spec.f (specs.map (·.f)) true
      (fun m hm m' hm' => by
        simp only [List.mem_singleton] at hm
        obtain ⟨spec', hspec'mem, hspec'eq⟩ := List.mem_map.mp hm'
        exact hspec'eq ▸ (hm ▸ hne spec' hspec'mem))
      hformula
  · intro env assignment hmatch assignment' hagreeFF hformula
    rw [hmap] at hformula
    exact hcomplete env assignment hmatch assignment'
      hagreeFF (evalFormula_names_below_indep gconf fspec_new.f (specs.map (·.f)) assignment'
        spec.f true hnb_spec hformula)

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

mutual

theorem seIfStmt_correct {c : ZKConfig} (gconf : GlobalConfig c) (p : Prog c)
    (specs : List (FuncSpec c))
    (H_simple : ∀ (sconf : SymExecConfig c) (i : ComWithMD c),
      TranslatesCorrectly gconf sconf specs (fun env => evalSimpleCmd gconf env i)
        (fun symEnv => seSimpleCmd gconf sconf symEnv specs i))
    (H_funcCall : ∀ (sconf : SymExecConfig c) (fname : FName) (args : List (SimpleExpr c))
        (outs : List VarID) (md : FuncMD) (func : Func c) (p' : Prog c),
      fetchFunc p fname = Except.ok (FuncWithMD.mk md func, p') →
      (match func with | Func.mk _ params _ _ => args.length = params.length) →
      (match func with | Func.mk _ _ rets _ => outs.length = rets.length) → outs.Nodup →
      (∀ (env : Env c), ∃ vs : List (Value c), evalSimpleExprsToValue env args = Except.ok vs ∧
        ValuesMatchParams vs (match func with | Func.mk _ params _ _ => params)) →
      TranslatesCorrectly gconf sconf specs
        (fun env => evalFuncCallCmd gconf p fname args outs env)
        (fun symEnv => seFuncCall gconf sconf symEnv specs fname args outs))
    (H_domain : ∀ (sconf' : SymExecConfig c) (symEnv' : SymEnv c) (cmds : List (ComWithMD c))
        (spec : CmdsSpec c),
      seCmds gconf sconf' symEnv' specs cmds = Except.ok spec →
      ∀ id, symEnv'.contains id ↔ spec.outSymEnv.contains id)
    (H_shape : ∀ (sconf' : SymExecConfig c) (symEnv' : SymEnv c) (tb' eb' : List (ComWithMD c))
        (tbSpec' ebSpec' : CmdsSpec c),
      seCmds gconf sconf' symEnv' specs tb' = Except.ok tbSpec' →
      seCmds gconf sconf' symEnv' specs eb' = Except.ok ebSpec' →
      ∀ id svTb svEb, tbSpec'.outSymEnv.get? id = some svTb →
        ebSpec'.outSymEnv.get? id = some svEb → sameShape svTb svEb)
    (sconf : SymExecConfig c) (md : CmdMD) (cond : Cond c)
    (tb eb : List (ComWithMD c)) (hshaped : WellShapedCom gconf p (Com.if_stmt cond tb eb)) :
    TranslatesCorrectly gconf sconf specs
      (fun env => evalIfStmt gconf p env md cond tb eb)
      (fun symEnv => seIfStmt gconf sconf symEnv specs md cond tb eb) := by
  obtain ⟨hcond_defined, hshapedTb, hshapedEb, _hshapeAgree⟩ := hshaped
  intro symEnv hbelow
  obtain ⟨tbSpec, htbSpec_eq, htbSpec_in, htbSpec_mono, htbSpec_fresh, htbSpec_below,
    htbSpec_outbelow, htbSpec_outfresh, htbSpec_sound, htbSpec_complete⟩ :=
    seCmds_correct gconf p specs H_simple H_funcCall H_domain H_shape sconf tb hshapedTb symEnv
      hbelow
  obtain ⟨ebSpec, hebSpec_eq, hebSpec_in, hebSpec_mono, hebSpec_fresh, hebSpec_below,
    hebSpec_outbelow, hebSpec_outfresh, hebSpec_sound, hebSpec_complete⟩ :=
    seCmds_correct gconf p specs H_simple H_funcCall H_domain H_shape sconf eb hshapedEb symEnv
      hbelow
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
  cases htry : tryEvalCondToConcreteValue gconf sconf symEnv md cond with
  | ok condVal =>
      cases condVal with
      | true =>
          refine ⟨tbSpec, ?_, htbSpec_in, htbSpec_mono, htbSpec_fresh, htbSpec_below,
            htbSpec_outbelow, htbSpec_outfresh, ?_, ?_⟩
          · simp only [seIfStmt, htry, if_true]; exact htbSpec_eq
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
          refine ⟨ebSpec, ?_, hebSpec_in, hebSpec_mono, hebSpec_fresh, hebSpec_below,
            hebSpec_outbelow, hebSpec_outfresh, ?_, ?_⟩
          · simp only [seIfStmt, htry, if_false]; exact hebSpec_eq
          · intro env assignment hmatch env' hc
            have hcond : evalCond env cond = Except.ok false :=
              tryEvalCondToConcreteValue_correct gconf sconf symEnv md cond env assignment false
                hmatch htry
            simp only [evalIfStmt, hcond, if_false] at hc
            exact hebSpec_sound env assignment hmatch env' hc
          · intro env assignment hmatch assignment' hagree heval
            obtain ⟨env', hc, hmatch'⟩ :=
              hebSpec_complete env assignment hmatch assignment' hagree heval
            refine ⟨env', ?_, hmatch'⟩
            have hcond : evalCond env cond = Except.ok false :=
              tryEvalCondToConcreteValue_correct gconf sconf symEnv md cond env assignment false
                hmatch htry
            simp only [evalIfStmt, hcond, if_false]
            exact hc
  | error e =>
      obtain ⟨g, hg⟩ := encodeCond_defined symEnv cond hcond_defined
      have hdom_contains : ∀ id, tbSpec.outSymEnv.contains id ↔ ebSpec.outSymEnv.contains id :=
        fun id => (H_domain sconf symEnv tb tbSpec htbSpec_eq id).symm.trans
          (H_domain sconf symEnv eb ebSpec hebSpec_eq id)
      have hdom : ∀ id, (∃ sv, tbSpec.outSymEnv.get? id = some sv) ↔
          (∃ sv, ebSpec.outSymEnv.get? id = some sv) :=
        fun id => (contains_iff_get?_isSome tbSpec.outSymEnv id).symm.trans
          ((hdom_contains id).trans (contains_iff_get?_isSome ebSpec.outSymEnv id))
      have hshape := H_shape sconf symEnv tb eb tbSpec ebSpec htbSpec_eq hebSpec_eq
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
      refine ⟨mergedSpec, ?_, hCompIn, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [seIfStmt, htry, htbSpec_eq, hebSpec_eq]; exact hmergedSpec_eq
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
        have heqSpec : mergedSpec' = mergedSpec := by
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
            mergedSpec hmergedSpec_eq htbSpec_complete hebSpec_complete env assignment hmatch
            assignment' hagree heval
        exact ⟨env', hc, hmatch'⟩
termination_by (numOfLoopExpComs tb + numOfLoopExpComs eb, sizeOfComs tb + sizeOfComs eb)
decreasing_by
  -- recursive call into seCmds_correct, on `tb`
  · have h1 : numOfLoopExpComs tb ≤ numOfLoopExpComs tb + numOfLoopExpComs eb := by grind
    rcases Nat.lt_or_eq_of_le h1 with h_less | h_equal
    · apply Prod.Lex.left
      exact h_less
    · rw [← h_equal]
      apply Prod.Lex.right
      exact sizeOfComs_a_lt_a_plus_b tb eb
  -- recursive call into seCmds_correct, on `eb`
  · have h1 : numOfLoopExpComs eb ≤ numOfLoopExpComs tb + numOfLoopExpComs eb := by grind
    rcases Nat.lt_or_eq_of_le h1 with h_less | h_equal
    · apply Prod.Lex.left
      exact h_less
    · rw [← h_equal]
      apply Prod.Lex.right
      rw [← Nat.add_comm]
      exact sizeOfComs_a_lt_a_plus_b eb tb

theorem seCmd_correct {c : ZKConfig} (gconf : GlobalConfig c) (p : Prog c)
    (specs : List (FuncSpec c))
    (H_simple : ∀ (sconf : SymExecConfig c) (i : ComWithMD c),
      TranslatesCorrectly gconf sconf specs (fun env => evalSimpleCmd gconf env i)
        (fun symEnv => seSimpleCmd gconf sconf symEnv specs i))
    (H_funcCall : ∀ (sconf : SymExecConfig c) (fname : FName) (args : List (SimpleExpr c))
        (outs : List VarID) (md : FuncMD) (func : Func c) (p' : Prog c),
      fetchFunc p fname = Except.ok (FuncWithMD.mk md func, p') →
      (match func with | Func.mk _ params _ _ => args.length = params.length) →
      (match func with | Func.mk _ _ rets _ => outs.length = rets.length) → outs.Nodup →
      (∀ (env : Env c), ∃ vs : List (Value c), evalSimpleExprsToValue env args = Except.ok vs ∧
        ValuesMatchParams vs (match func with | Func.mk _ params _ _ => params)) →
      TranslatesCorrectly gconf sconf specs
        (fun env => evalFuncCallCmd gconf p fname args outs env)
        (fun symEnv => seFuncCall gconf sconf symEnv specs fname args outs))
    (H_domain : ∀ (sconf' : SymExecConfig c) (symEnv' : SymEnv c) (cmds : List (ComWithMD c))
        (spec : CmdsSpec c),
      seCmds gconf sconf' symEnv' specs cmds = Except.ok spec →
      ∀ id, symEnv'.contains id ↔ spec.outSymEnv.contains id)
    (H_shape : ∀ (sconf' : SymExecConfig c) (symEnv' : SymEnv c) (tb' eb' : List (ComWithMD c))
        (tbSpec' ebSpec' : CmdsSpec c),
      seCmds gconf sconf' symEnv' specs tb' = Except.ok tbSpec' →
      seCmds gconf sconf' symEnv' specs eb' = Except.ok ebSpec' →
      ∀ id svTb svEb, tbSpec'.outSymEnv.get? id = some svTb →
        ebSpec'.outSymEnv.get? id = some svEb → sameShape svTb svEb)
    (sconf : SymExecConfig c) (md : CmdMD) (cmd : Com c) (hshaped : WellShapedCom gconf p cmd) :
    TranslatesCorrectly gconf sconf specs (fun env => evalCmd gconf p env (ComWithMD.mk md cmd))
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
        exact seIfStmt_correct gconf p specs H_simple H_funcCall H_domain H_shape sconf md cond tb eb hshaped
    | .loop_exp repSExp body, hshaped =>
        obtain ⟨⟨v, hv⟩, hshapedBody⟩ := hshaped
        subst hv
        have heq_c : (fun env => evalCmd gconf p env (ComWithMD.mk md (Com.loop_exp (.val v) body)))
            = (fun env => evalCmd gconf p env (ComWithMD.mk md (Com.loop v.val body))) := by
          funext env; simp only [evalCmd, evalSimpleExprToFFValue]
        have heq_s : (fun symEnv => seCmd gconf sconf symEnv specs
              (ComWithMD.mk md (Com.loop_exp (.val v) body)))
            = (fun symEnv => seCmd gconf sconf symEnv specs (ComWithMD.mk md (Com.loop v.val body))) := by
          funext symEnv; simp only [seCmd, tryEvalSimpleExprToFFValue]
        rw [heq_c, heq_s]
        exact seCmd_correct gconf p specs H_simple H_funcCall H_domain H_shape sconf md (Com.loop v.val body)
          hshapedBody
    | .loop (rep+1) body, hshaped =>
        intro symEnv hbelow
        obtain ⟨firstSpec, hfirstSpec_eq, hfirstSpec_in, hfirstSpec_mono, hfirstSpec_fresh,
          hfirstSpec_below, hfirstSpec_outbelow, hfirstSpec_outfresh, hfirstSpec_sound,
          hfirstSpec_complete⟩ :=
          seCmds_correct gconf p specs H_simple H_funcCall H_domain H_shape sconf body hshaped symEnv hbelow
        rw [← hfirstSpec_in] at hfirstSpec_sound hfirstSpec_complete
        obtain ⟨restSpec, hrestSpec_eq, hrestSpec_in, hrestSpec_mono, hrestSpec_fresh,
          hrestSpec_below, hrestSpec_outbelow, hrestSpec_outfresh, hrestSpec_sound,
          hrestSpec_complete⟩ :=
          seCmd_correct gconf p specs H_simple H_funcCall H_domain H_shape
            { sconf with nextVarId := firstSpec.nextVarId } md (Com.loop rep body) hshaped
            firstSpec.outSymEnv hfirstSpec_outbelow
        rw [← hrestSpec_in] at hrestSpec_sound hrestSpec_complete hrestSpec_fresh hrestSpec_outfresh
        obtain ⟨specComposed, heq⟩ :
            ∃ s, seqComposition gconf sconf (ComWithMD.mk md (Com.loop (rep+1) body))
              firstSpec restSpec = Except.ok s :=
          ⟨_, rfl⟩
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
        have hsymbolicEq : seCmd gconf sconf symEnv specs
              (ComWithMD.mk md (Com.loop (rep+1) body)) = Except.ok specComposed := by
          simp only [seCmd, hfirstSpec_eq, hrestSpec_eq]
          exact heq
        refine ⟨specComposed, hsymbolicEq,
          seqComposition_correct gconf sconf specs (ComWithMD.mk md (Com.loop (rep+1) body))
            symEnv hbelow
            (fun env => evalCmds gconf p env body)
            (fun env => evalCmd gconf p env (ComWithMD.mk md (Com.loop rep body)))
            (fun env => evalCmd gconf p env (ComWithMD.mk md (Com.loop (rep+1) body)))
            hconcrete firstSpec hfirstSpec_in hfirstSpec_mono hfirstSpec_fresh hfirstSpec_below
            hfirstSpec_outfresh hfirstSpec_sound' hfirstSpec_complete restSpec hrestSpec_in
            hrestSpec_mono hrestSpec_fresh hrestSpec_below hrestSpec_outbelow hrestSpec_outfresh
            hrestSpec_sound' hrestSpec_complete specComposed heq⟩
    | .loop 0 _body, _hshaped =>
        intro symEnv hbelow
        apply noop_spec_correct gconf specs sconf symEnv hbelow
        · intro env; simp only [evalCmd]; rfl
        · simp only [seCmd]
    | .func_call outs fname args, hshaped =>
        have heq_c : (fun env => evalCmd gconf p env (ComWithMD.mk md (Com.func_call outs fname args)))
            = (fun env => evalFuncCallCmd gconf p fname args outs env) := by
          funext env; simp only [evalCmd, evalFuncCallCmd]; rfl
        have heq_s : (fun symEnv => seCmd gconf sconf symEnv specs
              (ComWithMD.mk md (Com.func_call outs fname args)))
            = (fun symEnv => seFuncCall gconf sconf symEnv specs fname args outs) := by
          funext symEnv; simp only [seCmd]
        rw [heq_c, heq_s]
        obtain ⟨md', func, p', hfetch, hshaped'⟩ := hshaped
        cases func with
        | mk fname' params rets body =>
            simp only at hshaped'
            obtain ⟨hargs_len, houts_len, houts_nodup, hargs_defined⟩ := hshaped'
            exact H_funcCall sconf fname args outs md' (Func.mk fname' params rets body) p'
              hfetch hargs_len houts_len houts_nodup hargs_defined
    | .assign out e, _hshaped =>
        have heq_c : (fun env => evalCmd gconf p env (ComWithMD.mk md (Com.assign out e)))
            = (fun env => evalSimpleCmd gconf env (ComWithMD.mk md (Com.assign out e))) := by
          funext env; simp only [evalCmd]
        have heq_s : (fun symEnv => seCmd gconf sconf symEnv specs (ComWithMD.mk md (Com.assign out e)))
            = (fun symEnv => seSimpleCmd gconf sconf symEnv specs (ComWithMD.mk md (Com.assign out e))) := by
          funext symEnv; simp only [seCmd]
        rw [heq_c, heq_s]
        exact H_simple sconf (ComWithMD.mk md (Com.assign out e))
    | .new_array out size, _hshaped =>
        have heq_c : (fun env => evalCmd gconf p env (ComWithMD.mk md (Com.new_array out size)))
            = (fun env => evalSimpleCmd gconf env (ComWithMD.mk md (Com.new_array out size))) := by
          funext env; simp only [evalCmd]
        have heq_s : (fun symEnv => seCmd gconf sconf symEnv specs (ComWithMD.mk md (Com.new_array out size)))
            = (fun symEnv => seSimpleCmd gconf sconf symEnv specs (ComWithMD.mk md (Com.new_array out size))) := by
          funext symEnv; simp only [seCmd]
        rw [heq_c, heq_s]
        exact H_simple sconf (ComWithMD.mk md (Com.new_array out size))
    | .read_array out arr idx, _hshaped =>
        have heq_c : (fun env => evalCmd gconf p env (ComWithMD.mk md (Com.read_array out arr idx)))
            = (fun env => evalSimpleCmd gconf env (ComWithMD.mk md (Com.read_array out arr idx))) := by
          funext env; simp only [evalCmd]
        have heq_s : (fun symEnv => seCmd gconf sconf symEnv specs (ComWithMD.mk md (Com.read_array out arr idx)))
            = (fun symEnv => seSimpleCmd gconf sconf symEnv specs (ComWithMD.mk md (Com.read_array out arr idx))) := by
          funext symEnv; simp only [seCmd]
        rw [heq_c, heq_s]
        exact H_simple sconf (ComWithMD.mk md (Com.read_array out arr idx))
    | .write_array arr idx value, _hshaped =>
        have heq_c : (fun env => evalCmd gconf p env (ComWithMD.mk md (Com.write_array arr idx value)))
            = (fun env => evalSimpleCmd gconf env (ComWithMD.mk md (Com.write_array arr idx value))) := by
          funext env; simp only [evalCmd]
        have heq_s : (fun symEnv => seCmd gconf sconf symEnv specs (ComWithMD.mk md (Com.write_array arr idx value)))
            = (fun symEnv => seSimpleCmd gconf sconf symEnv specs (ComWithMD.mk md (Com.write_array arr idx value))) := by
          funext symEnv; simp only [seCmd]
        rw [heq_c, heq_s]
        exact H_simple sconf (ComWithMD.mk md (Com.write_array arr idx value))
    | .copy_array out arr, _hshaped =>
        have heq_c : (fun env => evalCmd gconf p env (ComWithMD.mk md (Com.copy_array out arr)))
            = (fun env => evalSimpleCmd gconf env (ComWithMD.mk md (Com.copy_array out arr))) := by
          funext env; simp only [evalCmd]
        have heq_s : (fun symEnv => seCmd gconf sconf symEnv specs (ComWithMD.mk md (Com.copy_array out arr)))
            = (fun symEnv => seSimpleCmd gconf sconf symEnv specs (ComWithMD.mk md (Com.copy_array out arr))) := by
          funext symEnv; simp only [seCmd]
        rw [heq_c, heq_s]
        exact H_simple sconf (ComWithMD.mk md (Com.copy_array out arr))
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
      (match func with | Func.mk _ params _ _ => args.length = params.length) →
      (match func with | Func.mk _ _ rets _ => outs.length = rets.length) → outs.Nodup →
      (∀ (env : Env c), ∃ vs : List (Value c), evalSimpleExprsToValue env args = Except.ok vs ∧
        ValuesMatchParams vs (match func with | Func.mk _ params _ _ => params)) →
      TranslatesCorrectly gconf sconf specs
        (fun env => evalFuncCallCmd gconf p fname args outs env)
        (fun symEnv => seFuncCall gconf sconf symEnv specs fname args outs))
    (H_domain : ∀ (sconf' : SymExecConfig c) (symEnv' : SymEnv c) (cmds : List (ComWithMD c))
        (spec : CmdsSpec c),
      seCmds gconf sconf' symEnv' specs cmds = Except.ok spec →
      ∀ id, symEnv'.contains id ↔ spec.outSymEnv.contains id)
    (H_shape : ∀ (sconf' : SymExecConfig c) (symEnv' : SymEnv c) (tb' eb' : List (ComWithMD c))
        (tbSpec' ebSpec' : CmdsSpec c),
      seCmds gconf sconf' symEnv' specs tb' = Except.ok tbSpec' →
      seCmds gconf sconf' symEnv' specs eb' = Except.ok ebSpec' →
      ∀ id svTb svEb, tbSpec'.outSymEnv.get? id = some svTb →
        ebSpec'.outSymEnv.get? id = some svEb → sameShape svTb svEb)
    (sconf : SymExecConfig c) (cmds : List (ComWithMD c)) (hshaped : WellShapedCmds gconf p cmds) :
    TranslatesCorrectly gconf sconf specs (fun env => evalCmds gconf p env cmds)
      (fun symEnv => seCmds gconf sconf symEnv specs cmds) := by
  cases cmds with
  | nil =>
      intro symEnv hbelow
      apply noop_spec_correct gconf specs sconf symEnv hbelow
      · intro env; simp only [evalCmds]
      · simp only [seCmds]; rfl
  | cons cmd rest =>
      cases cmd with
      | mk md cmd' =>
        simp only [WellShapedCmds] at hshaped
        obtain ⟨hshapedHead, hshapedRest⟩ := hshaped
        intro symEnv hbelow
        obtain ⟨cmdSpec, hcmdSpec_eq, hcmdSpec_in, hcmdSpec_mono, hcmdSpec_fresh, hcmdSpec_below,
          hcmdSpec_outbelow, hcmdSpec_outfresh, hcmdSpec_sound, hcmdSpec_complete⟩ :=
          seCmd_correct gconf p specs H_simple H_funcCall H_domain H_shape sconf md cmd' hshapedHead symEnv hbelow
        rw [← hcmdSpec_in] at hcmdSpec_sound hcmdSpec_complete
        obtain ⟨cmdsSpec, hcmdsSpec_eq, hcmdsSpec_in, hcmdsSpec_mono, hcmdsSpec_fresh,
          hcmdsSpec_below, hcmdsSpec_outbelow, hcmdsSpec_outfresh, hcmdsSpec_sound,
          hcmdsSpec_complete⟩ :=
          seCmds_correct gconf p specs H_simple H_funcCall H_domain H_shape
            { sconf with nextVarId := cmdSpec.nextVarId } rest hshapedRest
            cmdSpec.outSymEnv hcmdSpec_outbelow
        rw [← hcmdsSpec_in] at hcmdsSpec_sound hcmdsSpec_complete hcmdsSpec_fresh hcmdsSpec_outfresh
        obtain ⟨specComposed, heq⟩ :
            ∃ s, seqComposition gconf sconf (ComWithMD.mk md cmd') cmdSpec cmdsSpec = Except.ok s :=
          ⟨_, rfl⟩
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
        have hsymbolicEq : seCmds gconf sconf symEnv specs (ComWithMD.mk md cmd' :: rest) =
            Except.ok specComposed := by
          simp only [seCmds, hcmdSpec_eq, hcmdsSpec_eq]
          exact heq
        refine ⟨specComposed, hsymbolicEq,
          seqComposition_correct gconf sconf specs (ComWithMD.mk md cmd') symEnv hbelow
            (fun env => evalCmd gconf p env (ComWithMD.mk md cmd'))
            (fun env => evalCmds gconf p env rest)
            (fun env => evalCmds gconf p env (ComWithMD.mk md cmd' :: rest))
            hconcrete cmdSpec hcmdSpec_in hcmdSpec_mono hcmdSpec_fresh hcmdSpec_below
            hcmdSpec_outfresh hcmdSpec_sound' hcmdSpec_complete cmdsSpec hcmdsSpec_in
            hcmdsSpec_mono hcmdsSpec_fresh hcmdsSpec_below hcmdsSpec_outbelow hcmdsSpec_outfresh
            hcmdsSpec_sound' hcmdsSpec_complete specComposed heq⟩
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
    have h1 : numOfLoopExpComs rest ≤ numOfLoopExpCom (ComWithMD.mk md cmd') + numOfLoopExpComs rest := by
      grind
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
