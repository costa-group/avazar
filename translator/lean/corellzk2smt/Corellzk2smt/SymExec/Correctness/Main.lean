import Corellzk2smt.SymExec.Correctness.ProgCorrectness

/-!
This file exists so an outsider can see the one theorem the whole `SymExec/Correctness/`
development was building toward, without wading through the rest of `ProgCorrectness.lean`'s
supporting lemmas. `seExecProg_call_correct` itself lives here; everything it depends on stays in
`ProgCorrectness.lean`.
-/

namespace Corellzk2smt.SymExec.Correctness.Main

open Corellzk2smt.Config
open Corellzk2smt.Language.Core.Syntax.AST
open Corellzk2smt.Language.Core.Semantics.Basic
open Corellzk2smt.Language.Core.Semantics.BigStep
open Corellzk2smt.Language.Core.Analysis.DefinedVars
open Corellzk2smt.SymExec.Basic
open Corellzk2smt.SymExec.BigStep
open Corellzk2smt.FFConstraints.Basic
open Corellzk2smt.FFConstraints.Satisfiability
open Corellzk2smt.FFConstraints.Lemmas
open Corellzk2smt.SymExec.Correctness.Lemmas
open Corellzk2smt.SymExec.Correctness.FuncCorrectness
open Corellzk2smt.SymExec.Correctness.FuncCallCorrectness
open Corellzk2smt.SymExec.Correctness.ProgCorrectness

/-- The theorem this whole development was building toward: for *any* macro in the constraint
    system `cs` produced by `seExecProg`, a call to it with its own formal parameters as arguments
    (`mainFormula`'s own shape -- the solver is free to pick both inputs and outputs) relates to
    concrete execution both ways, and each direction *names* how the assignment and the concrete
    values correspond -- not just "some assignment/execution exists" unconnected to the other side
    (that would be true, but far too weak to call a translation-correctness theorem: it wouldn't
    rule out, say, the formula being satisfiable only by assignments whose param/ret readout has
    nothing to do with any real execution). Concretely:
    - *Soundness*: any assignment satisfying the call already **is** a witness for its own
      readout -- `argVals`/`retVals` in the conclusion are literally
      `reconstructValues assign.ff fspec.{params,rets} _`, i.e. exactly what `assign` itself
      assigns at those parameter positions.
    - *Completeness*: any concrete execution has **some** assignment realizing it, and that
      assignment's own readout is (again) exactly the given `argVals`/`retVals` --
      `seExecProg_call_complete`'s `buildAssign` witness, tied back via
      `reconstructValues_eq_of_matches`.
    Stated as a conjunction of two implications (over a shared `retsOffset`, the offset at which
    the callee's return-value variables start) rather than a single `∀ assign, ... ↔ ...`, because
    a combined iff over one *fixed* assignment is actually false: an assignment can satisfy the
    param/ret positions of a valid execution while its own (unconstrained-in-general) auxiliary
    positions don't hold a genuine witness -- soundness and completeness produce/consume
    *different* assignments in general, not the same one, so they can't be phrased as two
    directions of one iff without either being false or reintroducing the aux-witness plumbing
    this split was meant to avoid exposing. -/
theorem seExecProg_call_correct {c : ZKConfig} (gconf : GlobalConfig c) (p : ProgWithMD c)
    (funcs : Prog c) (hp : p = ProgWithMD.mk (match p with | ProgWithMD.mk pmd _ => pmd) funcs)
    (mainFuncName : FName) (cs : FFConstraintSystem c)
    (hcs_eq : seExecProg gconf p mainFuncName = Except.ok cs) :
    ∃ specs : List (FuncSpec c),
      cs = { macros := specs.map (·.f), main := mainFuncName } ∧
      (∀ spec ∈ specs, spec.f.name = spec.name) ∧
      specs.map (·.name) = funcs.map funcWithMDName ∧
      ∀ (fname : FName), fname ∈ specs.map (·.name) →
        ∃ (md' : FuncMD) (func' : Func c) (p'' : Prog c) (fspec : FuncSpec c) (retsOffset : Nat),
          fetchFunc funcs fname = Except.ok (FuncWithMD.mk md' func', p'') ∧
          fetchFuncSpec specs fname = Except.ok fspec ∧
          (∀ (assign : Assignment c),
              evalFormula gconf assign
                (FFFormula.call fspec.f.name (fspec.f.params.map (fun v => MacroCallParam.var v)))
                cs.macros = Except.ok true →
              ∃ (argVals retVals : List (Value c)),
                ValuesMatchParams argVals fspec.params ∧ ValuesMatchParams retVals fspec.rets ∧
                evalFunCall gconf funcs fname argVals = Except.ok retVals ∧
                argVals = reconstructValues assign.ff fspec.params 0 ∧
                retVals = reconstructValues assign.ff fspec.rets retsOffset) ∧
          (∀ (argVals retVals : List (Value c)),
              ValuesMatchParams argVals fspec.params → ValuesMatchParams retVals fspec.rets →
              evalFunCall gconf funcs fname argVals = Except.ok retVals →
              ∃ (assign : Assignment c),
                evalFormula gconf assign
                  (FFFormula.call fspec.f.name (fspec.f.params.map (fun v => MacroCallParam.var v)))
                  cs.macros = Except.ok true ∧
                argVals = reconstructValues assign.ff fspec.params 0 ∧
                retVals = reconstructValues assign.ff fspec.rets retsOffset) := by
  rw [hp] at hcs_eq
  simp only [seExecProg] at hcs_eq
  cases hfuncSpecs : seExecFuncs gconf funcs with
  | error e =>
      rw [hfuncSpecs] at hcs_eq
      simp only [Bind.bind, Except.bind] at hcs_eq
      exact absurd hcs_eq (by simp)
  | ok specs =>
      rw [hfuncSpecs] at hcs_eq
      simp only [Bind.bind, Except.bind, pure, Except.pure] at hcs_eq
      injection hcs_eq with hcs_eq
      obtain ⟨hspecs_wf, hnames_corr, _hHfc, hSpecC⟩ :=
        seExecFuncs_correct gconf funcs specs hfuncSpecs
      have hnodup : hasDupFuncNames funcs = false := by
        cases hh : hasDupFuncNames funcs with
        | true => simp [seExecFuncs, hh] at hfuncSpecs
        | false => rfl
      refine ⟨specs, hcs_eq.symm, hspecs_wf, hnames_corr, ?_⟩
      intro fname hmem
      obtain ⟨md', func', p'', hfetch⟩ :=
        fetchFunc_of_mem funcs fname (by rw [← hnames_corr]; exact hmem)
      obtain ⟨fspec, hspec_eq⟩ := fetchFuncSpec_of_mem specs fname hmem
      have hcs_macros : cs.macros = specs.map (·.f) := by rw [← hcs_eq]
      obtain ⟨⟨retsOffset, auxVarsList, hsplit_eq, hparams_le_rets, hauxFF_len, hauxBool_len,
          hsorted, hauxDisjoint⟩, hspec_retsShape, H_specCorrect⟩ :=
        hSpecC fname md' func' p'' hfetch fspec hspec_eq
      refine ⟨md', func', p'', fspec, retsOffset, hfetch, hspec_eq, ?_, ?_⟩
      · rw [hcs_macros]
        intro assign hLHS
        exact seExecProg_call_sound gconf funcs fname fspec (specs.map (·.f)) retsOffset
          auxVarsList hsplit_eq hsorted hauxFF_len hauxBool_len H_specCorrect assign hLHS
      · intro argVals retVals hshape_arg hshape_ret hevalFC
        obtain ⟨assign, hLHS, heq1, heq2⟩ := seExecProg_call_complete gconf funcs fname fspec
          (specs.map (·.f)) retsOffset auxVarsList hsplit_eq hparams_le_rets hsorted hauxFF_len
          hauxBool_len hauxDisjoint H_specCorrect argVals hshape_arg retVals hevalFC
        exact ⟨assign, hcs_macros ▸ hLHS, heq1, heq2⟩

end Corellzk2smt.SymExec.Correctness.Main
