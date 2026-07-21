import Corellzk2smt.Basic
import Corellzk2smt.Config
import Corellzk2smt.Language.Core.Syntax.AST
import Corellzk2smt.Language.Core.Syntax.Printer
import Corellzk2smt.Language.Core.Semantics.Basic
import Corellzk2smt.Language.Core.Analysis.DefinedVars

namespace Corellzk2smt.Language.Core.Semantics.BigStep

open Corellzk2smt.Config
open Corellzk2smt.Language.Core.Syntax.AST
open Corellzk2smt.Language.Core.Semantics.Basic
open Corellzk2smt.Language.Core.Analysis.DefinedVars





def evalSimpleCmd {c : ZKConfig}
  (gconf : GlobalConfig c)
  (env : Env c)
  (i : ComWithMD c)
  : Except String (Env c) := do
  match i with
   | .mk md cmd =>
      match cmd with
      | Com.assign id e => evalAssign md gconf env id e
      | Com.new_array id size => evalNewArray md gconf env id size
      | Com.read_array out a index => evalReadArray md gconf env out a index
      | Com.write_array a index value => evalWriteArray md gconf env a index value
      | Com.copy_array out a => evalCopyArray md gconf env out a
      -- In principle, this should be unreachable, since the caller should have already
      -- filtered out non-simple commands. However, we keep it here for safety.
      | _ => Except.error s!"evalSimpleCmd: command '{i}' is not a simple command"

mutual

def evalIfStmt {c : ZKConfig}
    (gconf : GlobalConfig c)
    (p : Prog c)
    (env : Env c)
    (_md : CmdMD)
    (cond : Cond c)
    (tb : List (ComWithMD c))
    (eb : List (ComWithMD c))
    : Except String (Env c) :=
    match evalCond env cond with
    | Except.error err => Except.error err
    | Except.ok condVal =>
        if condVal then
          evalCmds gconf p env tb
        else
          evalCmds gconf p env eb
termination_by (p.length, numOfLoopExpComs tb + numOfLoopExpComs eb, sizeOfComs tb + sizeOfComs eb)
decreasing_by
    all_goals -- in all recursive calls the program remain the same
      apply Prod.Lex.right
    -- recursive call with then-branch
    · have h1 : numOfLoopExpComs tb ≤ numOfLoopExpComs tb + numOfLoopExpComs eb := by grind
      rcases Nat.lt_or_eq_of_le h1 with h_less | h_equal
      · apply Prod.Lex.left
        exact h_less
      · rw [← h_equal]
        apply Prod.Lex.right
        exact sizeOfComs_a_lt_a_plus_b tb eb
    -- recursive call with else-branch
    · have h1 : numOfLoopExpComs eb ≤ numOfLoopExpComs tb + numOfLoopExpComs eb := by grind
      rcases Nat.lt_or_eq_of_le h1 with h_less | h_equal
      · apply Prod.Lex.left
        exact h_less
      · rw [← h_equal]
        apply Prod.Lex.right
        rw [← Nat.add_comm]
        exact sizeOfComs_a_lt_a_plus_b eb tb

def evalCmd {c : ZKConfig}
    (gconf : GlobalConfig c)
    (p : Prog c)
    (env : Env c)
    (i : ComWithMD c)
    : Except String (Env c) :=
  match i with
   | .mk md cmd =>
      match cmd with
      | Com.if_stmt cond tb eb =>
        evalIfStmt gconf p env md cond tb eb
      | Com.loop_exp rep body =>
          match evalSimpleExprToFFValue env rep with
          | Except.error err => Except.error err
          | Except.ok repVal =>
            let loop := (ComWithMD.mk md (Com.loop repVal.val body))
            evalCmd gconf p env loop
      | Com.loop (rep+1) body =>
          match evalCmds gconf p env body with -- evaluate loop body (1 iteration)
          | Except.error err => Except.error err
          | Except.ok env' =>
            -- evaluate the rest iterations of loop
            evalCmd gconf p env' (ComWithMD.mk md (Com.loop rep body))
      | Com.loop 0 _body =>
          return env
      | Com.func_call outs fname args =>
        match evalSimpleExprsToValue env args with
        | Except.error err => Except.error err
        | Except.ok argVals =>
          match evalFunCall gconf p fname argVals with
          | Except.error err => Except.error err
          | Except.ok outVals =>
            match setVars env outs outVals with
            | Except.error err => Except.error err
            | Except.ok vars_env =>
              Except.ok vars_env
      | _ => evalSimpleCmd gconf env i
termination_by (p.length, numOfLoopExpCom i, sizeOfCom i)
decreasing_by
    all_goals -- in all recursive calls the program remain the same
      apply Prod.Lex.right
    -- recursive call evalIfStmt
    · simp only [numOfLoopExpCom]
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
    (p : Prog c) (env : Env c) (cmds : List (ComWithMD c)) : Except String (Env c) :=
  match cmds with
  | [] => Except.ok env
  | cmd :: rest =>
    match evalCmd gconf p env cmd with
    | Except.error err => Except.error err
    | Except.ok env' => evalCmds gconf p env' rest
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
    : Except String (List (Value c)) :=
  if hasDupFuncNames p then
    Except.error "Program has two functions with the same name"
  else
    match _h_fetch: fetchFunc p fname with
    | Except.error e => Except.error e
    | Except.ok (f, p') =>
      match f with
      | .mk _ func =>
      match func with
       | Func.mk _ params rets body =>
         if hasDupNames (params.map (·.name)) || hasDupNames (rets.map (·.name)) then
           Except.error s!"Function '{fname}' has a duplicate parameter name or a duplicate return name"
         else
           match bindInParams (zeroInitEnv (definedVarsOfFunc func)) params args with
           | Except.error err => Except.error err
           | Except.ok vars_env =>
               let env := vars_env
               match evalCmds gconf p' env body with
              | Except.error err => Except.error err
              | Except.ok env' =>
                  match getOutParamsValues env' rets with
                  | Except.error err => Except.error err
                  | Except.ok rets => Except.ok rets
termination_by (p.length, 0 ,0)
decreasing_by
    apply Prod.Lex.left
    apply fetchLT p fname f p'
    assumption

end -- mutual

end Corellzk2smt.Language.Core.Semantics.BigStep
