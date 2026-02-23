import Llzk.Basic
import Llzk.SymExec.Basic
import Llzk.FFConstraints.Basic
import Llzk.Language.Core.Syntax.AST
import Llzk.Language.Core.Semantics.BigStep

namespace Llzk.SymExec.BigStep


open Llzk.Language.Core.Syntax.AST
open Llzk.SymExec.Basic


mutual

def evalCmd {c : ZKConfig}
    (p : Prog c) (i : ComWithMD c) : Except String (CmdsSpec c) := do
  match i with
   | .mk md cmd =>
      match cmd with
      | Com.skip => return {}
      | Com.assign _id _e => return {}
      | Com.new_array _id _size => return {}
      | Com.read_array _out _a _index => return {}
      | Com.write_array _a _index _value => return {}
      | Com.copy_array _out _a => return {}
      | Com.if_stmt _cond tb eb =>
          let _ ← evalCmds p tb
          let _ ← evalCmds p eb
          return {}
      | Com.loop_exp _rep body =>
          let loop := (ComWithMD.mk md (Com.loop 1 body))
          evalCmd p loop
      | Com.loop (rep+1) body =>
          let _ ← evalCmds p body --
          evalCmd p (ComWithMD.mk md (Com.loop rep body))
      | Com.loop 0 _body =>
          return {}
      | Com.func_call _outs fname _args =>
          let _ ← evalFun p fname
          return {}
termination_by (p.length, numOfLoopExpCom i, sizeOfCom i)
decreasing_by
    all_goals -- in all recursive calls the program remain the same
      apply Prod.Lex.right
    -- recursive call with then-branch
    · have h1 : numOfLoopExpComs tb ≤ numOfLoopExpComs tb + numOfLoopExpComs eb := by grind
      rcases Nat.lt_or_eq_of_le h1 with h_less | h_equal
      · apply Prod.Lex.left
        simp only [numOfLoopExpCom]
        exact h_less
      · simp only [numOfLoopExpCom]
        rw [← h_equal]
        apply Prod.Lex.right
        simp only [sizeOfCom]
        grind
    -- recursive call with else-branch
    · have h1 : numOfLoopExpComs eb ≤ numOfLoopExpComs tb + numOfLoopExpComs eb := by grind
      rcases Nat.lt_or_eq_of_le h1 with h_less | h_equal
      · apply Prod.Lex.left
        simp only [numOfLoopExpCom]
        exact h_less
      · simp only [numOfLoopExpCom]
        rw [← h_equal]
        apply Prod.Lex.right
        simp only [sizeOfCom]
        grind
    -- the case of loop_exp
    · simp only [numOfLoopExpCom]
      apply Prod.Lex.left
      grind
    -- the 1st iteration of loop
    · simp only [numOfLoopExpCom]
      apply Prod.Lex.right
      simp only [sizeOfCom]
      grind
    -- the rest of iterations of loop
    · simp only [numOfLoopExpCom]
      apply Prod.Lex.right
      simp only [sizeOfCom]
      grind
    -- function call
    · simp only [numOfLoopExpCom]
      apply Prod.Lex.right
      simp only [sizeOfCom]
      grind


def evalCmds {c : ZKConfig}
    (p : Prog c)  (cmds : List (ComWithMD c)) : Except String (CmdsSpec c) := do
  match cmds with
  | [] => return {}
  | cmd :: rest => do
    let _ ← evalCmd p cmd
    let _ ← evalCmds p rest
    return {}
termination_by (p.length, numOfLoopExpComs cmds, sizeOfComs cmds)
decreasing_by
  -- recursive call on cmd
  · apply Prod.Lex.right
    have h1 : numOfLoopExpCom cmd ≤ numOfLoopExpCom cmd + numOfLoopExpComs rest := by
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
  · apply Prod.Lex.right
    have h1 : numOfLoopExpComs rest ≤ numOfLoopExpCom cmd + numOfLoopExpComs rest := by
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

def evalFun {c : ZKConfig} (p : Prog c) (fname : FName) : Except String (CmdsSpec c) := do
    match _h_fetch: fetchFunc p fname with
    | Except.error e => Except.error e
    | Except.ok (f, p') =>
      match f with
      | .mk _ func =>
      match func with
       | Func.mk _ _params _rets body =>
           let _ ← evalCmds p'  body
           return {}
termination_by (p.length, 0 ,0)
decreasing_by
    apply Prod.Lex.left
    apply fetchLT p fname f p'
    assumption

end


end Llzk.SymExec.BigStep
