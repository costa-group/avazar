import Llzk.Basic
import Llzk.Language.Core.Syntax.AST
import Llzk.Language.Core.Analysis.Liveness
import Std.Data.TreeSet.Basic

/- EXPERIMENTAL VARIANT -- not wired into the CLI's main flags.

   This is a copy of `Useless_commands.lean` with exactly one change: the loop
   cases of `removeUselessCmd` no longer call the checked, general fixpoint
   `loopFixedPointOut` (which iterates until `out' == out` or a `fuel` bound
   is exhausted). Instead they compute the loop's live-out boundary the same
   way `Liveness.addLivenessCmd`'s `.loop_exp`/`.loop` cases do it for pure
   annotation: exactly "2 iterations" -- one application of the (deletion-
   free) body liveness function, unioned with `out`, and used directly with
   no equality check and no fuel/termination argument at all.

   This file exists purely to empirically compare the two approaches on test
   programs (see the conversation/README for `p7.txt`): does hard-coding "2
   iterations" here, the way `Liveness.lean` does for annotation, produce the
   same removeUseless output as the checked fixpoint in `Useless_commands.lean`? -/

namespace Llzk.Language.Core.Analysis.Useless_commands_2iter

open Llzk.Language.Core.Syntax.AST


def addUsedVarsSimpleExpr {c : ZKConfig} (vars : VarIDSet) (s : SimpleExpr c) : VarIDSet :=
    match s with
    | SimpleExpr.var id => vars.insert id
    | _ => vars

def addUsedVarsSimpleExprs {c : ZKConfig} (vars : VarIDSet) (ss : List (SimpleExpr c)) : VarIDSet :=
    match ss with
    | [] => vars
    | s :: rest => addUsedVarsSimpleExprs (addUsedVarsSimpleExpr vars s) rest

def addUsedVarsExpr {c : ZKConfig} (vars : VarIDSet) (e : Expr c) : VarIDSet :=
    match e with
    | .bop _ s1 s2 =>
        addUsedVarsSimpleExpr (addUsedVarsSimpleExpr vars s1) s2
    | .uop _ s =>
        addUsedVarsSimpleExpr vars s
    | .id s => addUsedVarsSimpleExpr vars s

def addUsedVarsCond {c : ZKConfig} (vars : VarIDSet) (cond : Cond c) : VarIDSet :=
    match cond with
    | .eq s1 s2 => addUsedVarsSimpleExpr (addUsedVarsSimpleExpr vars s1) s2

def getCmdsLiveIn {c : ZKConfig}
    (cmds : List (ComWithMD c)) (default : VarIDSet := emptyVarIDSet) : VarIDSet :=
    match cmds with
    | [] => default
    | i :: _ =>
        match i with
        | .mk md _ => md.liveness.live_in

def eraseVars (vars : VarIDSet) (varsToErase : List VarID) : VarIDSet :=
    match varsToErase with
    | [] => vars
    | v :: rest => eraseVars (vars.erase v) rest

def addParams (vars : VarIDSet) (params : List Param) : VarIDSet :=
    match params with
    | [] => vars
    | p :: rest => addParams (vars.insert p.name) rest

def eraseParams (vars : VarIDSet) (params : List Param) : VarIDSet :=
    match params with
    | [] => vars
    | p :: rest => eraseParams (vars.erase p.name) rest

def listToSet (l : List VarID) : VarIDSet :=
    match l with
    | [] => emptyVarIDSet
    | v :: rest => (listToSet rest).insert v

/-- The live-in set of `body` when its live-out set is `out`, without deleting
    any commands (pure liveness propagation). Same helper as in
    `Useless_commands.lean`. -/
def liveInOfBody {c : ZKConfig} (body : List (ComWithMD c)) (out : VarIDSet) : VarIDSet :=
    getCmdsLiveIn (Llzk.Language.Core.Analysis.Liveness.addLivenessCmds body out) out

/-- Hard-coded "2 iterations", mirroring `Liveness.addLivenessCmd`'s
    `.loop_exp`/`.loop` cases exactly: one application of `liveInOfBody`,
    unioned with `out`. No equality check, no fuel, no termination argument --
    this is used as-is, whatever it computes. -/
def twoIterationsOut {c : ZKConfig} (body : List (ComWithMD c)) (out : VarIDSet) : VarIDSet :=
    out.union (liveInOfBody body out)

mutual

/- Computes the liveness information for a single command,
   adds it to the meta data, and discard the command if it is useless
   (i.e., if it assigns to a variable that is not in the out set) -/
def removeUselessCmd {c : ZKConfig} (i : ComWithMD c) (out : VarIDSet)
  : Option (ComWithMD c) :=
    match i with
    | .mk md cmd =>
        match cmd with
        | .skip =>
          some (ComWithMD.mk { md with liveness := { live_in := out, live_out := out } } cmd)
        | .assign id e =>
          -- live_in = live_out \ {id} ∪ usedVars(e)
          let out' := out.erase id
          let liveIn := addUsedVarsExpr out' e
          match out.contains id with
          | true =>
              some (ComWithMD.mk
                { md with liveness := { live_in := liveIn, live_out := out } } cmd)
          | false => none
        | .if_stmt cond tb eb =>
          -- live_in = (live_in_then ∪ live_in_else) ∪ usedVars(cond)
          -- the if-the-else is useless if both branches are useless
          match removeUselessCmds tb out, removeUselessCmds eb out with
          | [], [] => none
          | tb', eb' => let liveInThen := getCmdsLiveIn tb' out
                        let liveInElse := getCmdsLiveIn eb' out
                        let liveIn := addUsedVarsCond (liveInThen.union liveInElse) cond
                        let cmd' := Com.if_stmt cond tb' eb'
                        some (ComWithMD.mk
                          { md with liveness := { live_in := liveIn, live_out := out } } cmd')
        | .loop_exp  rep body =>
          -- live_in = live_in of (body;body), computed with the hard-coded
          -- "2 iterations" `twoIterationsOut` instead of a checked fixpoint.
          let outFix := twoIterationsOut body out
          let body' := removeUselessCmds body outFix
          -- the loop is useless if the body is empty after removing
          -- useless commands
          match body' with
          | [] => none
          | _ =>
              let liveIn := addUsedVarsSimpleExpr (getCmdsLiveIn body' outFix) rep
              let cmd' := Com.loop_exp rep body'
              some (ComWithMD.mk
                { md with liveness := { live_in := liveIn, live_out := out } } cmd')
        | .loop rep body =>
          -- live_in = live_in of (body;body), computed with the hard-coded
          -- "2 iterations" `twoIterationsOut` instead of a checked fixpoint.
          let outFix := twoIterationsOut body out
          let body' := removeUselessCmds body outFix
          match body' with
          | [] => none
          | _ =>
              let liveIn := getCmdsLiveIn body' outFix
              let cmd' := Com.loop rep body'
              some (ComWithMD.mk
                { md with liveness := { live_in := liveIn, live_out := out } } cmd')
        | .new_array id _size =>
          -- live_in = live_out \ {id}
          -- the new_array is useless if the array is not used later
          let liveIn := out.erase id
          match out.contains id with
          | true =>
              some (ComWithMD.mk
                { md with liveness := { live_in := liveIn, live_out := out } } cmd)
          | false => none
        | .read_array id arr idx => -- id := arr[idx]
          -- live_in = (live_out \ {id}) ∪ {arr} ∪ usedVars(idx)
          -- the read_array is useless if that value is not used later
          let out' := out.erase id
          let liveIn := out'.insert arr
          let liveIn' := addUsedVarsSimpleExpr liveIn idx
          match out.contains id with
          | true =>
              some (ComWithMD.mk
                { md with liveness := { live_in := liveIn', live_out := out } } cmd)
          | false => none
        | .write_array arr idx val => -- arr[idx] := val
            -- live_in = live_out ∪ {arr} ∪ usedVars(idx) ∪ usedVars(val)
            -- the write_array is useless if the array is not used later
            let liveIn := out.insert arr
            let liveIn' := addUsedVarsSimpleExpr liveIn idx
            let liveIn'' := addUsedVarsSimpleExpr liveIn' val
            match out.contains arr with
            | true  =>
                some (ComWithMD.mk
                  { md with liveness := { live_in := liveIn'', live_out := out } } cmd)
            | false => none
        | .copy_array dst src =>
          -- live_in = (live_out \ {dst}) ∪ {src}
          -- the copy_array is useless if the destination array is not used later
          let liveIn := out.erase dst
          let liveIn' := liveIn.insert src
          match out.contains dst with
          | true =>
              some (ComWithMD.mk
                { md with liveness := { live_in := liveIn', live_out := out } } cmd)
          | false => none
        | .func_call rets _id args =>
          -- live_in = (live_out \ rets) ∪ usedVars(args)
          -- the func_call is useless if none of the return values are used later
          let out' := eraseVars out rets
          let liveIn := addUsedVarsSimpleExprs out' args
          let intersection := out.inter (listToSet rets)
          match intersection.isEmpty with
          | true => none
          | false =>
              some (ComWithMD.mk
                { md with liveness := { live_in := liveIn, live_out := out } } cmd)

/-- Computes the liveness information for a list of commands and
    removes useless commands -/
def removeUselessCmds {c : ZKConfig} (cmds : List (ComWithMD c)) (out : VarIDSet)
  : List (ComWithMD c) :=
    match cmds with
    | [] => []
    | i :: rest =>
        let rest' := removeUselessCmds rest out
        let out' := getCmdsLiveIn rest' out -- for empty list we get 'out' as default
        match removeUselessCmd i out' with
        | none => rest'
        | some i' => i' :: rest'

end

/-- Computes the liveness information for a function, adds it to the
    meta data, and and remove useless commands -/
def removeUselessFunc {c : ZKConfig} (f : FuncWithMD c) : FuncWithMD c :=
    match f with
    | .mk md func =>
    match func with
     | Func.mk name params rets body =>
     let out := addParams emptyVarIDSet rets
     let body' := removeUselessCmds body out
     let liveIn := getCmdsLiveIn body' out
     let func' := Func.mk name params rets body'
     FuncWithMD.mk { md with liveness := { live_in := liveIn, live_out := out } } func'

/-- Computes the liveness information for a list of functions and
    remove useless commands -/
def removeUselessFuncs {c : ZKConfig} (funcs : List (FuncWithMD c)) : List (FuncWithMD c) :=
    match funcs with
    | [] => []
    | f :: rest => removeUselessFunc f :: removeUselessFuncs rest

/-- Computes the liveness information for a program and remove useless
    commands -/
def removeUselessProg {c : ZKConfig} (p : ProgWithMD c) : ProgWithMD c :=
    match p with
    | .mk md funcs =>
        let funcs' := removeUselessFuncs funcs
        ProgWithMD.mk md funcs'

end Llzk.Language.Core.Analysis.Useless_commands_2iter
