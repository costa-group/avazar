import Corellzk2smt.SymExec.Correctness.Lemmas

/-!
`H_simple`'s conditional-form statement, given its own file so the project's one genuine open gap
(`seSimpleCmd` is currently a permanent `"TBD"` stub) is easy to find without wading through
`ProgCorrectness.lean`'s whole-program induction.
-/

namespace Corellzk2smt.SymExec.Correctness.SimpleCmdCorrectness

open Corellzk2smt.Config
open Corellzk2smt.Language.Core.Syntax.AST
open Corellzk2smt.Language.Core.Semantics.Basic
open Corellzk2smt.Language.Core.Semantics.BigStep
open Corellzk2smt.SymExec.Basic
open Corellzk2smt.SymExec.BigStep
open Corellzk2smt.SymExec.Correctness.Lemmas

/-- `H_simple`'s conditional-form statement, kept as a theorem (not an assumed parameter) so every
    consumer calls it by name rather than ever unfolding `seSimpleCmd` directly. Genuinely open:
    `seSimpleCmd` is currently a permanent `"TBD"` stub, under which this would be vacuously
    provable (the success hypothesis inside `TranslatesCorrectly` can never fire) -- but that
    proves the wrong thing, so it's left as an honest `sorry` instead. Once `seSimpleCmd` is
    actually implemented, this is the one place that needs a real proof; nothing else in the
    development should need to change. -/
theorem H_simple_holds {c : ZKConfig} (gconf : GlobalConfig c) (specs : List (FuncSpec c))
    (sconf : SymExecConfig c) (i : ComWithMD c) :
    TranslatesCorrectly gconf sconf specs (fun env => evalSimpleCmd gconf env i)
      (fun symEnv => seSimpleCmd gconf sconf symEnv specs i) := by
  sorry

end Corellzk2smt.SymExec.Correctness.SimpleCmdCorrectness
