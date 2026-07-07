import Corellzk2smt.Basic
import Corellzk2smt.Config
import Corellzk2smt.Language.Core.Syntax.AST
import Corellzk2smt.Language.Core.Syntax.Printer
import Corellzk2smt.Language.Core.Semantics.Basic

namespace Corellzk2smt.Language.Core.Semantics.BigStep

open Corellzk2smt.Config
open Corellzk2smt.Language.Core.Syntax.AST
open Corellzk2smt.Language.Core.Semantics.Basic





def evalSimpleCmd {c : ZKConfig} (gconf : GlobalConfig c)
  (st : State c) (i : ComWithMD c) : Except String (State c) := do
  match i with
   | .mk md cmd =>
      match cmd with
      | Com.assign id e => evalAssign md gconf st id e
      | Com.new_array id size => evalNewArray md gconf st id size
      | Com.read_array out a index => evalReadArray md gconf st out a index
      | Com.write_array a index value => evalWriteArray md gconf st a index value
      | Com.copy_array out a => evalCopyArray md gconf st out a
      -- In principle, this should be unreachable, since the caller should have already
      -- filtered out non-simple commands. However, we keep it here for safety.
      | _ => Except.error s!"evalSimpleCmd: command '{i}' is not a simple command"



mutual

def evalCmd {c : ZKConfig} (gconf : GlobalConfig c)
    (p : Prog c) (st : State c) (i : ComWithMD c) : Except String (State c) :=
  match i with
   | .mk md cmd =>
      match cmd with
      | Com.if_stmt cond tb eb =>
          match evalCond st cond with
          | Except.error err => Except.error err
          | Except.ok condVal =>
            if condVal then evalCmds gconf p st tb else evalCmds gconf p st eb
      | Com.loop_exp rep body =>
          match evalSimpleExprToFF st rep with
          | Except.error err => Except.error err
          | Except.ok repVal =>
            let loop := (ComWithMD.mk md (Com.loop repVal.val body))
            evalCmd gconf p st loop
      | Com.loop (rep+1) body =>
          match evalCmds gconf p st body with -- evaluate loop body (1 iteration)
          | Except.error err => Except.error err
          | Except.ok st' =>
            -- evaluate the rest iterations of loop
            evalCmd gconf p st' (ComWithMD.mk md (Com.loop rep body))
      | Com.loop 0 _body =>
          return st
      | Com.func_call outs fname args =>
        match evalSimpleExprsToValue st args with
        | Except.error err => Except.error err
        | Except.ok argVals =>
          match evalFunCall gconf p fname argVals with
          | Except.error err => Except.error err
          | Except.ok outVals =>
            match setVars st.vars outs outVals with
            | Except.error err => Except.error err
            | Except.ok vars_env =>
              let st' := { st with vars := vars_env }
              Except.ok st'
      | _ => evalSimpleCmd gconf st i
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


def evalCmds {c : ZKConfig} (gconf : GlobalConfig c)
    (p : Prog c) (st : State c) (cmds : List (ComWithMD c)) : Except String (State c) :=
  match cmds with
  | [] => Except.ok st
  | cmd :: rest => do
    match evalCmd gconf p st cmd with
    | Except.error err => Except.error err
    | Except.ok st' => evalCmds gconf p st' rest
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

def evalFunCall {c : ZKConfig} (gconf : GlobalConfig c)
    (p : Prog c) (fname : FName) (args : List (Value c))
    : Except String (List (Value c)) := do
    match _h_fetch: fetchFunc p fname with
    | Except.error e => Except.error e
    | Except.ok (f, p') =>
      match f with
      | .mk _ func =>
      match func with
       | Func.mk _ params rets body =>
           let vars_env ← bindInParams (emptyEnv c) params args
           let st := ⟨vars_env⟩
           let st' ← evalCmds gconf p' st body
           let rets ← bindOutParams st'.vars rets
           Except.ok rets
termination_by (p.length, 0 ,0)
decreasing_by
    apply Prod.Lex.left
    apply fetchLT p fname f p'
    assumption

end -- mutual

end Corellzk2smt.Language.Core.Semantics.BigStep
