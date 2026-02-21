import Llzk.Basic
import Llzk.Language.Core.Syntax.AST
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

namespace Llzk.Language.Core.Analysis.Liveness

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
    | .id s => addUsedVarsSimpleExpr vars s
    | .neg s => addUsedVarsSimpleExpr vars s
    | .add s1 s2 => addUsedVarsSimpleExpr (addUsedVarsSimpleExpr vars s1) s2
    | .sub s1 s2 => addUsedVarsSimpleExpr (addUsedVarsSimpleExpr vars s1) s2
    | .mul s1 s2 => addUsedVarsSimpleExpr (addUsedVarsSimpleExpr vars s1) s2
    | .div s1 s2 => addUsedVarsSimpleExpr (addUsedVarsSimpleExpr vars s1) s2
    | .shl s1 s2 => addUsedVarsSimpleExpr (addUsedVarsSimpleExpr vars s1) s2
    | .shr s1 s2 => addUsedVarsSimpleExpr (addUsedVarsSimpleExpr vars s1) s2
    | .and s1 s2 => addUsedVarsSimpleExpr (addUsedVarsSimpleExpr vars s1) s2
    | .or s1 s2 => addUsedVarsSimpleExpr (addUsedVarsSimpleExpr vars s1) s2
    | .xor s1 s2 => addUsedVarsSimpleExpr (addUsedVarsSimpleExpr vars s1) s2
    | .not s => addUsedVarsSimpleExpr vars s
    | .True => vars
    | .False => vars
    | .eq s1 s2 => addUsedVarsSimpleExpr (addUsedVarsSimpleExpr vars s1) s2
    | .neq s1 s2 => addUsedVarsSimpleExpr (addUsedVarsSimpleExpr vars s1) s2
    | .lt s1 s2 => addUsedVarsSimpleExpr (addUsedVarsSimpleExpr vars s1) s2
    | .gt s1 s2 => addUsedVarsSimpleExpr (addUsedVarsSimpleExpr vars s1) s2
    | .le s1 s2 => addUsedVarsSimpleExpr (addUsedVarsSimpleExpr vars s1) s2
    | .ge s1 s2 => addUsedVarsSimpleExpr (addUsedVarsSimpleExpr vars s1) s2
    | .bor s1 s2 => addUsedVarsSimpleExpr (addUsedVarsSimpleExpr vars s1) s2
    | .band s1 s2 => addUsedVarsSimpleExpr (addUsedVarsSimpleExpr vars s1) s2
    | .bneg s => addUsedVarsSimpleExpr vars s

def addUsedVarsCond {c : ZKConfig} (vars : VarIDSet) (cond : Cond c) : VarIDSet :=
    match cond with
    | .eq s1 s2 => addUsedVarsSimpleExpr (addUsedVarsSimpleExpr vars s1) s2
    | .neq s1 s2 => addUsedVarsSimpleExpr (addUsedVarsSimpleExpr vars s1) s2


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

mutual

/- Computes the liveness information for a single command,
   and adds it to the meta data -/
def addLivenessCmd {c : ZKConfig} (i : ComWithMD c) (out : VarIDSet) :=
    match i with
    | .mk md cmd =>
        match cmd with
        | .skip =>
          ComWithMD.mk { md with liveness := { live_in := out, live_out := out } } cmd
        | .assign id e =>
          -- live_in = live_out \ {id} ∪ usedVars(e)
          let out' := out.erase id
          let liveIn := addUsedVarsExpr out' e
          ComWithMD.mk { md with liveness := { live_in := liveIn, live_out := out } } cmd
        | .if_stmt cond tb eb =>
          -- live_in = (live_in_then ∪ live_in_else) ∪ usedVars(cond)
          let tb' := addLivenessCmds tb out
          let eb' := addLivenessCmds eb out
          let liveInThen := getCmdsLiveIn tb'
          let liveInElse := getCmdsLiveIn eb'
          let liveIn := addUsedVarsCond (liveInThen.union liveInElse) cond
          let cmd' := Com.if_stmt cond tb' eb'
          ComWithMD.mk { md with liveness := { live_in := liveIn, live_out := out } } cmd'
        | .loop_exp  rep body =>
          -- live_in = live_in of (body;body)
          -- None of the expressions are considered since they are supposed to be constant
          -- expressions. Also the loop variable 'idx' is not considered since it is a
          -- constant variable. We need to iterate the loop twice to get the fixed point of the
          -- live variables. 2 iteration are enough.
          let body' := addLivenessCmds body out
          let liveIn := getCmdsLiveIn body'
          let body'' := addLivenessCmds body (liveIn.union out)
          let liveIn' := getCmdsLiveIn body''
          let liveIn'' := addUsedVarsSimpleExpr liveIn' rep
          let cmd' := Com.loop_exp rep body''
          ComWithMD.mk { md with liveness := { live_in := liveIn'', live_out := out } } cmd'
        | .loop _rep body =>
          -- live_in = live_in of (body;body)
          -- The loop variable 'idx' is not considered since it is a constant variable.
          -- We need to iterate the loop twice to get the fixed point of the live variables.
          let body' := addLivenessCmds body out
          let liveIn := getCmdsLiveIn body'
          let body'' := addLivenessCmds body (liveIn.union out)
          let liveIn' := getCmdsLiveIn body''
          let cmd' := Com.loop _rep body''
          ComWithMD.mk { md with liveness := { live_in := liveIn', live_out := out } } cmd'
        | .new_array id _size =>
          -- live_in = live_out \ {id}
          -- We do not consider size since it is supposed to be a constant expression.
          let liveIn := out.erase id
          ComWithMD.mk { md with liveness := { live_in := liveIn, live_out := out } } cmd
        | .read_array id arr idx => -- id := arr[idx]
          -- live_in = (live_out \ {id}) ∪ {arr} ∪ usedVars(idx)
          let out' := out.erase id
          let liveIn := out'.insert arr
          let liveIn' := addUsedVarsSimpleExpr liveIn idx
          ComWithMD.mk { md with liveness := { live_in := liveIn', live_out := out } } cmd
        | .write_array arr idx val => -- arr[idx] := val
            -- live_in = live_out ∪ {arr} ∪ usedVars(idx) ∪ usedVars(val)
            -- Note that 'arr' is considered live-in since it is an array access
            let liveIn := out.insert arr
            let liveIn' := addUsedVarsSimpleExpr liveIn idx
            let liveIn'' := addUsedVarsSimpleExpr liveIn' val
            ComWithMD.mk { md with liveness := { live_in := liveIn'', live_out := out } } cmd
        | .copy_array dst src =>
          -- live_in = (live_out \ {dst}) ∪ {src}
          let liveIn := out.erase dst
          let liveIn' := liveIn.insert src
          ComWithMD.mk { md with liveness := { live_in := liveIn', live_out := out } } cmd
        | .func_call rets _id args =>
          -- live_in = (live_out \ rets) ∪ usedVars(args)
          let out' := eraseVars out rets
          let liveIn := addUsedVarsSimpleExprs out' args
          ComWithMD.mk { md with liveness := { live_in := liveIn, live_out := out } } cmd

/-- Computes the liveness information for a list of commands -/
def addLivenessCmds {c : ZKConfig} (cmds : List (ComWithMD c)) (out : VarIDSet) :=
    match cmds with
    | [] => []
    | i :: rest =>
        let rest' := addLivenessCmds rest out
        let out' := getCmdsLiveIn rest' out -- for empty list we get 'out' as default
        let i' := addLivenessCmd i out'
        i' :: rest'

end


/-- Computes the liveness information for a function, and adds it to the
    meta data -/
def addLivenessFunc {c : ZKConfig} (f : FuncWithMD c) : FuncWithMD c :=
    match f with
    | .mk md func =>
    match func with
     | Func.mk name params rets body =>
     let out := addParams emptyVarIDSet rets
     let body' := addLivenessCmds body out
     let liveIn := getCmdsLiveIn body' out
     let func' := Func.mk name params rets body'
     FuncWithMD.mk { md with liveness := { live_in := liveIn, live_out := out } } func'

/-- Computes the liveness information for a list of functions -/
def addLivenessFuncs {c : ZKConfig} (funcs : List (FuncWithMD c)) : List (FuncWithMD c) :=
    match funcs with
    | [] => []
    | f :: rest => addLivenessFunc f :: addLivenessFuncs rest

/-- Computes the liveness information for a program -/
def addLivenessProg {c : ZKConfig} (p : ProgWithMD c) : ProgWithMD c :=
    match p with
    | .mk md funcs =>
        let funcs' := addLivenessFuncs funcs
        ProgWithMD.mk md funcs'

end Llzk.Language.Core.Analysis.Liveness
