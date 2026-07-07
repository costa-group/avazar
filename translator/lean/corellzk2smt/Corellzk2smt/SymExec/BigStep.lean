import Corellzk2smt.Basic
import Corellzk2smt.Config
import Corellzk2smt.SymExec.Basic
import Corellzk2smt.SymExec.Common
import Corellzk2smt.FFConstraints.Basic
import Corellzk2smt.Language.Core.Syntax.AST


namespace Corellzk2smt.SymExec.BigStep


open Corellzk2smt.Config (GlobalConfig)
open Corellzk2smt.Language.Core.Syntax.AST
open Corellzk2smt.SymExec.Basic
open Corellzk2smt.FFConstraints.Basic



def seSimpleCmd {c : ZKConfig}
    (_gconf : GlobalConfig c)
    (_sconf : SymExecConfig c)
    (_symEnv : SymEnv c)
    (_specs : List (FuncSpec c))
    (_i : ComWithMD c)
    : Except String (CmdsSpec c) :=
    Except.error "TBD"

def seFuncCall {c : ZKConfig}
    (_gconf : GlobalConfig c)
    (_sconf : SymExecConfig c)
    (_symEnv : SymEnv c)
    (_specs : List (FuncSpec c))
    (_fname : FName)
    (_args : List (SimpleExpr c))
    (_outs : List VarID)
    : Except String (CmdsSpec c) :=
    Except.error "TBD"

def tryEvalCondToConcreteValue {c : ZKConfig}
    (_gconf : GlobalConfig c)
    (_sconf : SymExecConfig c)
    (_symEnv : SymEnv c)
    (_md : CmdMD)
    (_cond : Cond c)
    : Except String Bool :=
    Except.error "TBD"

def mergeIfBranches {c : ZKConfig}
    (_gconf : GlobalConfig c)
    (_sconf : SymExecConfig c)
    (_symEnv : SymEnv c)
    (_specs : List (FuncSpec c))
    (_md : CmdMD)
    (_tbSpec : CmdsSpec c)
    (_ebSpec : CmdsSpec c)
    (_cond : Cond c)
    : Except String (CmdsSpec c) :=
    Except.error "TBD"

def seqComposition {c : ZKConfig}
    (_gconf : GlobalConfig c)
    (_sconf : SymExecConfig c)
    (_cmdSpec1 : CmdsSpec c)
    (_cmdsSpec2 : CmdsSpec c)
    : Except String (CmdsSpec c) :=
    Except.error "TBD"

mutual

def seIfStmt {c : ZKConfig}
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (md : CmdMD)
    (cond : Cond c)
    (tb : List (ComWithMD c))
    (eb : List (ComWithMD c))
    : Except String (CmdsSpec c) :=
    match tryEvalCondToConcreteValue gconf sconf symEnv md cond with
    | Except.error _e =>
        match seCmds gconf sconf symEnv specs tb with
        | Except.error msg => Except.error msg
        | Except.ok tbSpec =>
            match seCmds gconf sconf tbSpec.outSymEnv specs eb with
            | Except.error msg => Except.error msg
            | Except.ok ebSpec =>
                mergeIfBranches gconf sconf symEnv specs md tbSpec ebSpec cond
    | Except.ok condVal =>
        if condVal then
          seCmds gconf sconf symEnv specs tb
        else
          seCmds gconf sconf symEnv specs eb
termination_by (numOfLoopExpComs tb + numOfLoopExpComs eb, sizeOfComs tb + sizeOfComs eb)
decreasing_by
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

def seCmd {c : ZKConfig}
    (gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (i : ComWithMD c)
    : Except String (CmdsSpec c) :=
  match i with
   | .mk md cmd =>
      match cmd with
      -- if statement
      | Com.if_stmt cond tb eb =>
        seIfStmt gconf sconf symEnv specs md cond tb eb
      -- Loop with a simple expression as the number of iterations.
      -- Reduced to loop with concrete repetitions.
      | Com.loop_exp repSExp body =>
          match tryEvalSimpleExprToFFValue symEnv repSExp with
          | Except.error msg => Except.error msg
          | Except.ok rep =>
            let loop := (ComWithMD.mk md (Com.loop rep.val body))
            seCmd gconf sconf symEnv specs loop
      -- Loop with a concrete number of iterations.
      | Com.loop (rep+1) body =>
        match seCmds gconf sconf symEnv specs body with
        | Except.error msg => Except.error msg
        | Except.ok specFirstIter =>
            let sconf' := { sconf with nextVarId := specFirstIter.nextVarId }
            let i' := ComWithMD.mk md (Com.loop rep body)
            match seCmd gconf sconf' specFirstIter.outSymEnv specs i' with
            | Except.error msg => Except.error msg
            | Except.ok specRestIter =>
              seqComposition gconf sconf specFirstIter specRestIter
      -- Loop with 0 iterations.
      | Com.loop 0 _body =>
          Except.ok {
            inSymEnv := symEnv,
            outSymEnv := symEnv,
            f := default
            nextVarId := sconf.nextVarId
          }
      | Com.func_call outs fname args =>
        seFuncCall gconf sconf symEnv specs fname args outs
      | _ => -- All other commands are simple commands
        seSimpleCmd gconf sconf symEnv specs i
termination_by (numOfLoopExpCom i, sizeOfCom i)
decreasing_by
  -- recursive call evalIfStmt
  · simp only [numOfLoopExpCom]
    apply Prod.Lex.right
    simp only [sizeOfCom]
    grind
  -- the case of loop_exp
  · simp only [numOfLoopExpCom]
    apply Prod.Lex.left
    grind
  -- the case of loop with concrete repetitions -- first iteration
  · simp only [numOfLoopExpCom]
    apply Prod.Lex.right
    simp only [sizeOfCom]
    grind
  -- the case of loop with concrete repetitions -- rest of iterations
  · simp only [numOfLoopExpCom]
    apply Prod.Lex.right
    simp only [sizeOfCom]
    grind

def seCmds {c : ZKConfig}
  (gconf : GlobalConfig c)
  (sconf : SymExecConfig c)
  (symEnv : SymEnv c)
  (specs : List (FuncSpec c))
  (cmds : List (ComWithMD c))
  : Except String (CmdsSpec c) :=
  match cmds with
  | [] => return {
      inSymEnv := symEnv,
      outSymEnv := symEnv,
      f := default,
      nextVarId := sconf.nextVarId,
  }
  | cmd :: rest =>
    match seCmd gconf sconf symEnv specs cmd with
    | Except.error msg => Except.error msg
    | Except.ok cmdSpec =>
      let sconf' := { sconf with nextVarId := cmdSpec.nextVarId }
      match seCmds gconf sconf' cmdSpec.outSymEnv specs rest with
      | Except.error msg => Except.error msg
      | Except.ok cmdsSpec =>
        seqComposition gconf sconf cmdSpec cmdsSpec

termination_by (numOfLoopExpComs cmds, sizeOfComs cmds)
decreasing_by
  -- recursive call on cmd
  · have h1 : numOfLoopExpCom cmd ≤ numOfLoopExpCom cmd + numOfLoopExpComs rest := by
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
  · have h1 : numOfLoopExpComs rest ≤ numOfLoopExpCom cmd + numOfLoopExpComs rest := by
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

end


end Corellzk2smt.SymExec.BigStep
