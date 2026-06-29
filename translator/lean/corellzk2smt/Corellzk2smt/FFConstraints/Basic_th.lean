import Corellzk2smt.FFConstraints.Basic
import Corellzk2smt.Config

/- This module defines the syntax of constraint systems over finite fields
   and boolean variables -/

namespace Corellzk2smt.FFConstraints.Basic_th
open Corellzk2smt.FFConstraints.Basic

/- fetchMacro returns a smaller list of macros -/
theorem fetchMacroLT {c : ZKConfig} (gconf : GlobalConfig c) (ms ms' : List (FFMacro c))
    (name : String) (m : FFMacro c) :
  fetchMacro gconf ms name = Except.ok (m, ms') → ms'.length < ms.length := by
  cases ms with
  | nil => simp [fetchMacro]
  | cons head tail =>
      simp only [fetchMacro]
      by_cases h : head.name = name
      · simp only [h, BEq.rfl, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq, List.length_cons,
        Order.lt_add_one_iff, and_imp] at *
        intro  h1 h2
        rw [h2]
      · simp only [h, not_false_eq_true, beq_iff_eq, ↓reduceIte, List.length_cons,
        Order.lt_add_one_iff] at *
        intro h1
        have h2 := fetchMacroLT gconf tail ms' name m h1
        grind

end Corellzk2smt.FFConstraints.Basic_th
