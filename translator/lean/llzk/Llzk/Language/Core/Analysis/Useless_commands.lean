import Llzk.Basic
import Llzk.Language.Core.Syntax.AST
import Llzk.Language.Core.Analysis.Liveness
import Std.Data.TreeSet.Basic

/- This module implements liveness analysis for the core language. The liveness information
   is stored in the metadata of each command and function.

   The main function is `addLivenessProg` which takes a program and returns a new program
   with liveness information added to each function. The liveness information of each function
   is computed by traversing the commands in reverse order and keeping track of the live
   variables at each point.

   Traversing in reverse order is done for now with recursion, we should consider
   reversing the list and use tail-recursion.
-/

namespace Llzk.Language.Core.Analysis.Useless_commands

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

/- Computing which commands are useless inside a loop body is a backward
   dataflow problem with a back-edge (the body's own live_in feeds back into
   its live_out, since the loop may execute the body again). A single pass
   (as used for straight-line code and if-statements, which have no back-edge)
   is not enough: it can under-estimate liveness and cause `removeUselessCmd`
   to delete commands that are in fact needed by a later iteration of the
   loop. `loopFixedPointOut` iterates the (deletion-free) liveness
   computation from `Liveness.addLivenessCmds` until the live-out set of the
   loop stops growing, so that the final call to `removeUselessCmds` below
   uses a sound approximation of liveness. -/

/-- The live-in set of `body` when its live-out set is `out`, without deleting
    any commands (pure liveness propagation, reusable across fixed-point
    iterations). -/
def liveInOfBody {c : ZKConfig} (body : List (ComWithMD c)) (out : VarIDSet) : VarIDSet :=
    getCmdsLiveIn (Llzk.Language.Core.Analysis.Liveness.addLivenessCmds body out) out

/-- Iterates `liveInOfBody` starting from `out`, growing the live-out set on
    each round, until it stabilizes or `fuel` runs out. The live-out set is
    monotonically non-decreasing and bounded by the (finite) set of variables
    mentioned in `body`, so it is safe (if imprecise) to under-run the fuel:
    the caller should pick `fuel` at least as large as the number of commands
    in `body`, since each additional round of propagation can extend the
    liveness chain through at most one more command. -/
def loopFixedPointOut {c : ZKConfig}
    (fuel : Nat) (body : List (ComWithMD c)) (out : VarIDSet) : VarIDSet :=
    match fuel with
    | 0 => out
    | fuel + 1 => loopFixedPointOut fuel body ((liveInOfBody body out).union out)

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
          | tb', eb' => let liveInThen := getCmdsLiveIn tb'
                        let liveInElse := getCmdsLiveIn eb'
                        let liveIn := addUsedVarsCond (liveInThen.union liveInElse) cond
                        let cmd' := Com.if_stmt cond tb' eb'
                        some (ComWithMD.mk
                          { md with liveness := { live_in := liveIn, live_out := out } } cmd')
        | .loop_exp  rep body =>
          -- live_in = live_in of (body;body), computed at a genuine fixed
          -- point since a loop may re-execute its body arbitrarily many
          -- times (see `loopFixedPointOut`). None of the expressions are
          -- considered since they are supposed to be constant expressions.
          let fuel := sizeOfComs body + 1
          let outFix := loopFixedPointOut fuel body out
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
          -- live_in = live_in of (body;body), computed at a genuine fixed
          -- point (see `loopFixedPointOut`).
          let fuel := sizeOfComs body + 1
          let outFix := loopFixedPointOut fuel body out
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
          -- We do not consider size since it is supposed to be a constant expression.
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
            -- Note that 'arr' is considered live-in since it is an array access
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

end Llzk.Language.Core.Analysis.Useless_commands
