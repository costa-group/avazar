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
   well-shaped.

   Kept around (rather than deleted, and every call site's `hshaped`/`hwsp` parameter along with
   them) for a purely practical reason: the mutual, well-founded-recursive proofs in
   `SymExec/Correctness/Correctness.lean` (`seIfStmt_correct`/`seCmd_correct`/
   `seCmds_correct`) turn out to be extremely sensitive to their own case-split/parameter shape --
   removing the `hshaped` parameter and its `match cmd, hshaped with`-style destructuring from
   those specific proofs (confirmed via careful bisection against the git history) made Lean's
   elaborator dramatically slower (tens of minutes instead of under a minute for that one file),
   almost certainly due to how the equation compiler's auto-generated match/split lemmas interact
   with the shared `termination_by`/`decreasing_by` block once the case-split shape changes.
   Rather than risk that regression for a purely cosmetic win, those three theorems (and the
   `_names_below`/`_prepend_indep`-style family in `SymExec/Correctness.lean`) keep their
   `hshaped`/`WellShapedCom`/`WellShapedCmds` parameters completely unchanged. What's actually
   removed is the *assumption burden* on every caller: every external call site (in
   `SymExec/Correctness/FuncCorrectness.lean` and `ProgCorrectness.lean`) now manufactures
   the (trivially provable) witness on the spot via `trivialWSCom`/`trivialWSCmds` below, instead
   of requiring a caller-supplied proof threaded all the way from the top of the program. -/

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

mutual

/-- `WellShapedCom` is trivially satisfied by every command, for every program -- manufactures a
    witness on the spot so no caller needs one threaded down from outside. -/
theorem trivialWSCom {c : ZKConfig} (gconf : GlobalConfig c) (p : Prog c) (cmd : Com c) :
    WellShapedCom gconf p cmd := by
  cases cmd <;> first
    | trivial
    | exact ⟨trivialWSCmds gconf p _, trivialWSCmds gconf p _⟩
    | exact trivialWSCmds gconf p _

/-- `WellShapedCmds` counterpart of `trivialWSCom`. -/
theorem trivialWSCmds {c : ZKConfig} (gconf : GlobalConfig c) (p : Prog c)
    (cmds : List (ComWithMD c)) : WellShapedCmds gconf p cmds := by
  cases cmds with
  | nil => trivial
  | cons i rest =>
    cases i with
    | mk _ cmd => exact ⟨trivialWSCom gconf p cmd, trivialWSCmds gconf p rest⟩

end

end Corellzk2smt.Language.Core.Analysis.WellShaped
