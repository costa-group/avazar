import Llzk.Basic
import Llzk.Language.Core.Syntax
import Llzk.Language.Core.Semantics.Basic


namespace Llzk.Language.Core.Semantics.BigStep

open Llzk.Language.Core


/- An executable Big-Step Semantics for progrmas.

   It executes a program `p` starting from environment `env`,
   returning the final environment after executing all commands in `p`.

   Returns:
    - Except.error: Runtime error (e.g., variable not found)
    - Except.ok env': Final environment after executing the program

   Note: the use of match for a single command is done to avoid mutual recursion
-/
def exec_prog {c : ZKConfig} (env : Env c) (p : Prog c) : Except String (Env c) := do
  match p with
  | [] => return env
  | cmd::cmds => do
      let env' ← match cmd with -- for simple commands we use the functions defined above
                 | Com.skip _ => exec_skip env
                 | Com.add _ out a1 a2 => exec_add env out a1 a2
                 | Com.sub _ out a1 a2 => exec_sub env out a1 a2
                 | Com.mul _ out a1 a2 => exec_mul env out a1 a2
                 | Com.div _ out a1 a2 => exec_div env out a1 a2
                 | Com.shl _ out a bits => exec_shl env out a bits
                 | Com.assign _ out a => exec_assign env out a
                 | Com.ifst _ cond tb eb => -- branching command handled here
                     let condVal ← get_var env cond
                     if condVal != 0 then
                       exec_prog env tb -- true branch, when condVal is not zero
                     else
                       exec_prog env eb -- false branch , when condVal is zero
      exec_prog env' cmds -- continue with the rest of the program

/- A convenience wrapper to first initialize the environment and then call exec_prog.
-/
def run_prog {c : ZKConfig}
    (prog : Prog c) (f : Oracle c) : Except String (Env c) :=
  do
  let vars_set := collect_prog_vars prog
  let vars := vars_set.toList
  let env := vars.foldl (init := (emptyEnv c)) (fun env name => set_var env name (f name))
  exec_prog env prog


/- Inductive/Declarative Big-Step Semantics

   `BigStep cmd s s'` means that executing `cmd` in state `s` successfully results in state `s'`.

   It is basically equivalent to exec_prog, but defined inductively for reasoning purposes.
-/
inductive BigStepProg {c : ZKConfig} : Prog c → Env c → Env c → Prop where
  | empty_prog {s} :
      BigStepProg [] s s
  | Com.skip {md s p s' s''} :
      exec_skip s = Except.ok s' →
      BigStepProg p s' s'' →
      BigStepProg ((Com.skip md)::p) s s''
  | Com.add {md out a1 a2 s p s' s''} :
      exec_add s out a1 a2 = Except.ok s' →
      BigStepProg p s' s'' →
      BigStepProg ((Com.add md out a1 a2)::p) s s''
  | Com.sub {md out a1 a2 s p s' s''} :
      exec_sub s out a1 a2 = Except.ok s' →
      BigStepProg p s' s'' →
      BigStepProg ((Com.sub md out a1 a2)::p) s s''
  | Com.mul {md out a1 a2 s p s' s''} :
      exec_mul s out a1 a2 = Except.ok s' →
      BigStepProg p s' s'' →
      BigStepProg ((Com.mul md out a1 a2)::p) s s''
  | Com.div {md out a1 a2 s p s' s''}:
      exec_div s out a1 a2 = Except.ok s' →
      BigStepProg p s' s'' →
      BigStepProg ((Com.div md out a1 a2)::p) s s''
  | Com.shl {md out a bits s p s' s''} :
      exec_shl s out a bits = Except.ok s' →
      BigStepProg p s' s'' →
      BigStepProg ((Com.shl md out a bits)::p) s s''
  | Com.assign {md out a s p s' s''} :
      exec_assign s out a = Except.ok s' →
      BigStepProg p s' s'' →
      BigStepProg ((Com.assign md out a)::p) s s''
  | Com.if_true {md cond tb eb s v p s' s''} :
      get_var s cond = Except.ok v →
      v ≠ 0 →
      BigStepProg tb s s' →
      BigStepProg p s' s'' →
      BigStepProg ((Com.ifst md cond tb eb)::p) s s''
  | Com.if_false {md cond tb eb s v p s' s''} :
      get_var s cond = Except.ok v →
      v = 0 →
      BigStepProg eb s s' →
      BigStepProg p s' s'' →
      BigStepProg ((Com.ifst md cond tb eb)::p) s s''


/- The following theorem prove equivalnce between the executable and
   inductive Big-Step semantics
-/

/- A tactic to solve each case of the `exec_prog_implies_big_step_prog` theorem below

   exec:   The execution function call (e.g., exec_skip s)
   constr: The BigStep constructor (e.g., BigStepProg.Com.skip)
   h:      The hypothesis name (e.g., h)
   ih:     The induction hypothesis name (e.g., ih)
-/
local macro "solve_exec_case"
  exec:term "," constr:ident "," h:ident "," ih:ident : tactic =>
  `(tactic| (
    -- 1. Unfold and simplify
    simp [exec_prog, Bind.bind, Except.bind] at $h:ident
    -- 2. Case analysis on the result of the instruction
    cases h_exec : $exec with
    | error msg =>
      -- Error case: contradiction
      rw [h_exec] at $h:ident
      contradiction
    | ok s'' =>
      -- Success case: apply constructor + IH
      rw [h_exec] at $h:ident
      dsimp at $h:ident
      -- Apply the constructor. We let Lean infer the arguments to 'ih' using (_)
      exact $constr h_exec ($ih _ _ $h)
  ))

/- If the Big-Step semantics holds for program `p`, starting from environment `s`
   resulting in environment `s'`, then executing `p` from `s` results in `s'`.
-/
theorem big_step_prog_implies_exec_prog {c : ZKConfig} (p : Prog c) (s s' : Env c) :
  BigStepProg p s s' → exec_prog s p = Except.ok s' := by
  intro h
  induction h with
  | empty_prog =>
    simp only [exec_prog, pure, Except.pure]
  | @Com.skip
  | @Com.add
  | @Com.sub
  | @Com.mul
  | @Com.div
  | @Com.shl
  | @Com.assign
  | @Com.if_true
  | @Com.if_false =>
    simp [exec_prog, Bind.bind, Except.bind]
    simp [*]
-- qed

/- If executing a program `p` from environment `s` results in `s'`,
   then  `BigStep cmd s s'` holds
-/
theorem exec_prog_implies_big_step_prog {c : ZKConfig} (p : Prog c) (s s' : Env c) :
  exec_prog s p = Except.ok s' → BigStepProg p s s' := by
  -- We use a 'decreases_by' tactic implicitly by structuring it this way
  intro h
  match p with
  | [] =>
    simp only [exec_prog, pure, Except.pure, Except.ok.injEq] at h
    rw [h]
    exact BigStepProg.empty_prog
  | cmd :: cmds =>
    have ih := exec_prog_implies_big_step_prog cmds
    cases cmd with
    | skip md =>
      solve_exec_case (exec_skip s), BigStepProg.Com.skip, h, ih
    | add md out a1 a2 =>
      solve_exec_case (exec_add s out a1 a2), BigStepProg.Com.add, h, ih
    | sub md out a1 a2 =>
      solve_exec_case (exec_sub s out a1 a2), BigStepProg.Com.sub, h, ih
    | mul md out a1 a2 =>
      solve_exec_case (exec_mul s out a1 a2), BigStepProg.Com.mul, h, ih
    | div md out a1 a2 =>
      solve_exec_case (exec_div s out a1 a2), BigStepProg.Com.div, h, ih
    | shl md out a bits =>
      solve_exec_case (exec_shl s out a bits), BigStepProg.Com.shl, h, ih
    | assign md out a =>
      solve_exec_case (exec_assign s out a), BigStepProg.Com.assign, h, ih
    | ifst md cond tb eb =>
        have ih_then := exec_prog_implies_big_step_prog tb
        have ih_else := exec_prog_implies_big_step_prog eb
        -- Evaluate the condition
        simp only [exec_prog, bind, Except.bind, bne_iff_ne, ne_eq, ite_not] at h
        cases h_cond : get_var s cond with
        | error msg =>
          rw [h_cond] at h
          contradiction
        | ok v =>
          rw [h_cond] at h
          dsimp at h
          by_cases h_cond_val : v = 0
          · -- False branch
            simp only [h_cond_val, ↓reduceIte] at h
            cases h_exec_eb: exec_prog s eb with
            | error msg =>
              rw [h_exec_eb] at h
              contradiction
            | ok s'' =>
              rw [h_exec_eb] at h
              dsimp at h
              let bs_eb := ih_else s s'' h_exec_eb
              exact BigStepProg.Com.if_false h_cond h_cond_val bs_eb (ih s'' s' h)
          · -- True branch, very similar to the false branch, maybe can be refactored
            simp only [h_cond_val, ↓reduceIte] at h
            cases h_exec_tb: exec_prog s tb with
            | error msg =>
              rw [h_exec_tb] at h
              contradiction
            | ok s'' =>
              rw [h_exec_tb] at h
              dsimp at h
              let bs_tb := ih_then s s'' h_exec_tb
              exact BigStepProg.Com.if_true h_cond h_cond_val bs_tb (ih s'' s' h)
-- qed


/- Using the above theorems, we establish equivalence between the executable and
   inductive Big-Step semantics
-/
theorem big_step_prog_iff_exec_prog {c : ZKConfig} (p : Prog c) (s s' : Env c) :
  BigStepProg p s s' ↔ exec_prog s p = Except.ok s' := by
  apply Iff.intro -- it is like constructor for ↔
  · apply big_step_prog_implies_exec_prog
  · apply exec_prog_implies_big_step_prog
-- qed


end Llzk.Language.Core.Semantics.BigStep
