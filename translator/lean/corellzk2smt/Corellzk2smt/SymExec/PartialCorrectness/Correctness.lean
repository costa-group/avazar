import Corellzk2smt.SymExec.PartialCorrectness.Lemmas
import Corellzk2smt.SymExec.Correctness

/-
Partial-correctness analogues of `seIfStmt_correct`/`seCmd_correct`/`seCmds_correct`
(`SymExec/Correctness.lean`). See `PartialCorrectness/Lemmas.lean`'s header for the overall
design; the short version is that every one of these now takes the produced `spec` and the
success witness `symbolic symEnv = Except.ok spec` as *given* (via the new `TranslatesCorrectly`),
rather than proving `symbolic` always succeeds and producing `spec` as an existential witness.

Everything genuinely combinatorial -- `seqComposition_correct`, `noop_spec_correct`,
`mergeIfBranches_sound`/`mergeIfBranches_complete`, the `mergeSymEnv_*` family,
`tryEvalCondToConcreteValue_correct`, `encodeCond_vars_subset` -- is reused
unchanged from `SymExec/Correctness.lean` via import: none of it is stated in terms of
`TranslatesCorrectly` at all, just explicit hypotheses about specific `CmdsSpec`s, so it doesn't
care whether the wrapping `TranslatesCorrectly` is the old (unconditional) or new (conditional)
version. Only the three theorems that *construct* `TranslatesCorrectly`'s existential/conditional
form change, and the change is mechanical: everywhere the old proof did
`obtain ⟨spec, hspec_eq, ...⟩ := someRecursiveCall ...` (destructuring an existential), the new
proof instead does `cases hspec_eq : someComputation ... with | error e => ... | ok spec => ...`
(case-splitting on the actual computation) and then applies the recursive correctness fact to the
*discovered* `spec`/`hspec_eq` -- the `error` branch is dismissed by unfolding the *caller's* own
`hspec_eq` (the given success witness) far enough to see it would also have to be `Except.error`,
contradiction.

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
-/
namespace Corellzk2smt.SymExec.PartialCorrectness.Correctness

open Corellzk2smt.Config (GlobalConfig)
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
open Corellzk2smt.SymExec.Correctness
open Corellzk2smt.SymExec.PartialCorrectness.Lemmas

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
    (vars : VarIDSet)
    (sconf : SymExecConfig c) (md : CmdMD) (cond : Cond c)
    (tb eb : List (ComWithMD c)) (hshaped : WellShapedCom gconf p (Com.if_stmt cond tb eb)) :
    TranslatesCorrectlyGiven gconf sconf specs
      (fun symEnv => ∀ id, id ∈ definedVarsCmds (definedVarsCmds vars tb) eb → symEnv.contains id)
      (fun env => evalIfStmt gconf p env md cond tb eb)
      (fun symEnv => seIfStmt gconf sconf symEnv specs md cond tb eb) := by
  obtain ⟨hshapedTb, hshapedEb, hshapeAgree⟩ := hshaped
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
            seCmds_correct gconf p specs H_simple H_funcCall vars sconf tb hshapedTb
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
            seCmds_correct gconf p specs H_simple H_funcCall vars sconf eb hshapedEb
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
        seCmds_correct gconf p specs H_simple H_funcCall vars sconf tb hshapedTb
          symEnv hbelow htb_pre tbSpec htbSpec_eq
      obtain ⟨hebSpec_in, hebSpec_mono, hebSpec_fresh, hebSpec_below,
        hebSpec_outbelow, hebSpec_outfresh, hebSpec_sound, hebSpec_complete⟩ :=
        seCmds_correct gconf p specs H_simple H_funcCall vars sconf eb hshapedEb
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
        intro id svTb svEb hsvTb hsvEb
        have hmatch0 : EnvMatches (default : Assignment c) symEnv (decodeSymEnv default symEnv) :=
          EnvMatches_decodeSymEnv default symEnv
        obtain ⟨envTb, envEb, hevalTb, hevalEb, hshapeAgree⟩ :=
          hshapeAgree (decodeSymEnv default symEnv)
        obtain ⟨assignTb, _, _, _, _, hmatchTb⟩ :=
          htbSpec_sound' (decodeSymEnv default symEnv) default hmatch0 envTb hevalTb
        obtain ⟨assignEb, _, _, _, _, hmatchEb⟩ :=
          hebSpec_sound' (decodeSymEnv default symEnv) default hmatch0 envEb hevalEb
        obtain ⟨v1, hv1, hm1⟩ := hmatchTb.2 id svTb hsvTb
        obtain ⟨v2, hv2, hm2⟩ := hmatchEb.2 id svEb hsvEb
        exact sameShape_of_symValMatches assignTb assignEb svTb svEb v1 v2 hm1 hm2
          (hshapeAgree id v1 v2 hv1 hv2)
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
        exact seIfStmt_correct gconf p specs H_simple H_funcCall vars sconf md cond
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
              seCmd_correct gconf p specs H_simple H_funcCall vars sconf md
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
          seCmds_correct gconf p specs H_simple H_funcCall vars { nextVarId := sconf.nextVarId }
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
          seCmd_correct gconf p specs H_simple H_funcCall vars
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
    | .func_call outs fname args, hshaped =>
        have heq_c : (fun env => evalCmd gconf p env
              (ComWithMD.mk md (Com.func_call outs fname args)))
            = (fun env => evalFuncCallCmd gconf p fname args outs env) := by
          funext env; simp only [evalCmd, evalFuncCallCmd]; rfl
        have heq_s : (fun symEnv => seCmd gconf sconf symEnv specs
              (ComWithMD.mk md (Com.func_call outs fname args)))
            = (fun symEnv => seFuncCall gconf sconf symEnv specs fname args outs) := by
          funext symEnv; simp only [seCmd]
        rw [heq_c, heq_s]
        obtain ⟨md', func, p', hfetch, hshaped'⟩ := hshaped
        apply TranslatesCorrectlyGiven_of_TranslatesCorrectly
        cases func with
        | mk fname' params rets body =>
            simp only at hshaped'
            exact H_funcCall sconf fname args outs md' (Func.mk fname' params rets body) p'
              hfetch hshaped'
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
          seCmd_correct gconf p specs H_simple H_funcCall vars sconf md cmd'
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
          seCmds_correct gconf p specs H_simple H_funcCall vars
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
