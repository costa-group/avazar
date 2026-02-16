import Llzk.Basic
import Llzk.Language.Core.Syntax.AST
import Llzk.Language.Core.Semantics.Basic

namespace Llzk.Language.Core.Semantics.BigStep

open Llzk.Language.Core.Syntax.AST
open Llzk.Language.Core.Semantics.Basic

mutual

def evalCmd {c : ZKConfig} (cfg : SemConfig c)
    (p : Prog c) (st : State c) (cmd : Com c) : Except String (State c) := do
  match cmd with
  | Com.skip _ => evalSkip st
  | Com.assign _ id e => evalAssign st id e
  | Com.new_array _ id size => evalNewArray st id size
  | Com.read_array _ out a index => evalReadArray st out a index
  | Com.write_array _ a index value => evalWriteArray st a index value
  | Com.copy_array _ out a => evalCopyArray st out a
  | Com.if_stmt _ cond tb eb =>
      let condVal ← evalCond st cond
      if condVal then evalCmds cfg p st tb else evalCmds cfg p st eb
  | Com.with_const _ out e body =>
      ensureNotDefinedCVar st.cvars out -- ensure the constant variable is not already defined
      let constVal ← evalConstExpr st e
      let st' := { st with cvars := st.cvars.insert out constVal }
      let st'' ← evalCmds cfg p st' body
      let st''' := { st'' with cvars := st''.cvars.erase out }  -- remove constant variable after
      return st'''
  | Com.loop_exp md idx start rep step body =>
      let startVal ← evalConstExpr st start
      let repVal ← evalConstExpr st rep
      let stepVal ← evalConstExpr st step
      let loop := Com.loop md idx startVal repVal.val stepVal body
      evalCmd cfg p st loop
  | Com.loop  md idx start (rep+1) step body =>
      ensureNotDefinedCVar st.cvars idx -- ensure loop constant variable is not already defined
      let st' := { st with cvars := st.cvars.insert idx start } -- insert loop variable into cvars
      let st'' ← evalCmds cfg p st' body -- evaluate loop body (1 iteration)
      let st''' := { st'' with cvars := st''.cvars.erase idx }  -- remove loop variable
      evalCmd cfg p st''' (Com.loop md idx (start+step) rep step body) -- evaluate the rest
  | Com.loop  _md _idx _start 0 _step _body =>
      return st
  | Com.func_call _ outs fname args =>
    let argVals ← evalSimpleExprsToValue st args
    let outVals ← evalFun cfg p fname argVals
    let vars_env ← setVars st.vars outs outVals
    let st' := { st with vars := vars_env }
    return st'
termination_by (p.length, numOfLoopExpCom cmd, sizeOfCom cmd)
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
    -- recursive call in with_const
    ·  simp only [numOfLoopExpCom]
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


def evalCmds {c : ZKConfig} (cfg : SemConfig c)
    (p : Prog c) (st : State c) (cmds : List (Com c)) : Except String (State c) := do
  match cmds with
  | [] => Except.ok st
  | cmd :: rest => do
    let st' ← evalCmd cfg p st cmd
    evalCmds cfg p st' rest
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

def evalFun {c : ZKConfig} (cfg : SemConfig c)
    (p : Prog c) (fname : FName) (args : List (Value c))
    : Except String (List (Value c)) := do
    match _h_fetch: fetchFunc p fname with
    | Except.error e => Except.error e
    | Except.ok (f, p') =>
        let vars_env ← bindInParams (emptyEnv c) f.params args
        let st := ⟨vars_env, emptyCEnv c⟩
        let st' ← evalCmds cfg p' st f.body
        let rets ← bindOutParams st'.vars f.rets
        Except.ok rets
termination_by (p.length, 0 ,0)
decreasing_by
    apply Prod.Lex.left
    apply fetchLT p fname f p'
    assumption

end -- mutual

end Llzk.Language.Core.Semantics.BigStep
