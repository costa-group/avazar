import Llzk.Basic
import Llzk.SymExec.Basic
import Llzk.FFConstraints.Basic
import Llzk.Language.Core.Syntax.AST
import Llzk.Language.Core.Semantics.BigStep

namespace Llzk.SymExec.BigStep


open Llzk.Language.Core.Syntax.AST
open Llzk.SymExec.Basic


mutual

def seCmd {c : ZKConfig}
    (cfg : SymExecConfig c)
    (symEnv : SymEnv c)
    (p : Prog c) (i : ComWithMD c) : Except String (CmdsSpec c) := do
  match i with
   | .mk md cmd =>
      match cmd with
      | Com.skip => seSkip cfg md symEnv
      | Com.assign id e => seAssignment cfg md symEnv id e
      | Com.new_array id size => seNewArray cfg md symEnv id size
      | Com.read_array out a idx => seArrayRead cfg md symEnv out a idx
      | Com.write_array a idx value => seArrayWrite cfg md symEnv a idx value
      | Com.copy_array out a => seArrayCopy cfg md symEnv out a
      | Com.if_stmt _cond tb eb =>
          let _ ← seCmds cfg symEnv p tb
          let _ ← seCmds cfg symEnv p eb
          return {}
      | Com.loop_exp _rep body =>
          let loop := (ComWithMD.mk md (Com.loop 1 body))
          seCmd cfg symEnv p loop
      | Com.loop (rep+1) body =>
          let _ ← seCmds cfg symEnv p body --
          seCmd cfg symEnv p (ComWithMD.mk md (Com.loop rep body))
      | Com.loop 0 _body =>
          return {}
      | Com.func_call _outs fname _args =>
          let _ ← seFuncCall cfg symEnv p fname
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


def seCmds {c : ZKConfig}
  (cfg : SymExecConfig c)
  (symEnv : SymEnv c) (p : Prog c)  (cmds : List (ComWithMD c)) : Except String (CmdsSpec c) := do
  match cmds with
  | [] => return {}
  | cmd :: rest => do
    let _ ← seCmd cfg symEnv p cmd
    let _ ← seCmds cfg symEnv p rest
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

def seFuncCall {c : ZKConfig}
    (cfg : SymExecConfig c)
    (symEnv : SymEnv c) (p : Prog c) (fname : FName) : Except String (CmdsSpec c) := do
    match _h_fetch: fetchFunc p fname with
    | Except.error e => Except.error e
    | Except.ok (f, p') =>
      match f with
      | .mk _ func =>
      match func with
       | Func.mk _ _params _rets body =>
           let _ ← seCmds cfg symEnv p'  body
           return {}
termination_by (p.length, 0 ,0)
decreasing_by
    apply Prod.Lex.left
    apply fetchLT p fname f p'
    assumption

end


end Llzk.SymExec.BigStep
