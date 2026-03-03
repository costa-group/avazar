import Llzk.Basic
import Llzk.SymExec.Basic
import Llzk.FFConstraints.Basic
import Llzk.Language.Core.Syntax.AST
import Llzk.Language.Core.Semantics.BigStep
import Llzk.FFConstraints.Basic
namespace Llzk.SymExec.BigStep


open Llzk.Language.Core.Syntax.AST
open Llzk.SymExec.Basic
open Llzk.FFConstraints.Basic


def addArrayVarInfo {c : ZKConfig}
    (cfg : SymExecConfig c)
    (md : CmdMD)
    (id : VarID)
    (v1 v2 : SymFFArray c)
    (inSymEnv _tbSymEnv _ebSymEnv : SymEnv c)
    (tbF ebF : FFFormula c)
    (symEnv : SymEnv c) -- this is the one for the exit of the if-stmt
    : Except String (IfSpec c) := do
    if (v1.size != v2.size) then
      throw s!"Array size mismatch for variable {id} in then-branch and else-branch"
    else
      let arr : SymFFArray c := (List.replicate v1.size (.const 0)).toArray -- initialize with zeros
      let rec loop
              (idx : Nat)
              (arr : SymFFArray c)
              (nextId : Nat)
              (ffVarSet : FFVarSet)
              (tbF ebF : FFFormula c)
              : Except String (IfSpec c) := do
        if h1: idx < v1.size then
          if h2: idx < v2.size then
            if h3: idx < arr.size then
              let v1AtIdx := v1[idx]'h1
              let v2AtIdx := v2[idx]'h2
              let v1Term := symVarToTerm v1AtIdx
              let v2Term := symVarToTerm v2AtIdx
              let newId := idx
              let md' := FFVarMetaData.mk (s!"{id}_{idx}") md.src_info
              let newVar := FFVar.mk newId md'
              let eqTb' : FFFormula c := (.and tbF (.eq (.var newVar) v1Term))
              let eqEb' : FFFormula c := (.and ebF (.eq (.var newVar) v2Term))
              let arr' := Array.set arr idx (.var newVar) h3
              loop (idx + 1) arr' (nextId+1) (ffVarSet.insert newVar)  eqTb' eqEb'
            else
              throw s!"This is not supposed to happen"
          else
            throw s!"This is not supposed to happen"
        else
          let symEnv' := setVar symEnv id (.ffArray arr)
          return {
            inSymEnv := inSymEnv,
            outSymEnv := symEnv',
            tbF := tbF,
            ebF := ebF,
            nextId := nextId,
            newFFVars := ffVarSet,
            newBoolVars := emptyBoolVarSet
          }
      loop 0 arr cfg.nextId emptyFFVarSet tbF ebF

def addFFVarInfo {c : ZKConfig}
    (cfg : SymExecConfig c)
    (md : CmdMD)
    (id : VarID)
    (v1 v2 : SymFFVar c)
    (inSymEnv _tbSymEnv _ebSymEnv : SymEnv c)
    (tbF ebF : FFFormula c)
    (symEnv : SymEnv c) -- this is the one for the exit of the if-stmt
    : Except String (IfSpec c) := do
    let newId := cfg.nextId --  a new
    let md' := FFVarMetaData.mk (s!"{id}") md.src_info
    let newVar := FFVar.mk newId md'
    let symEnv' := setVar symEnv id (.ffVar (.var newVar))
    let v1Term := symVarToTerm v1
    let v2Term := symVarToTerm v2
    let eqTb := .eq (.var newVar) v1Term
    let eqEb := .eq (.var newVar) v2Term
    return {
      inSymEnv := inSymEnv,
      outSymEnv := symEnv',
      tbF := .and tbF eqTb,
      ebF := .and ebF eqEb,
      nextId := cfg.nextId + 1,
      newFFVars := {newVar},
      newBoolVars := emptyBoolVarSet
    }

def addVarInfo {c : ZKConfig}
    (cfg : SymExecConfig c)
    (md : CmdMD)
    (id : VarID)
    (inSymEnv tbSymEnv ebSymEnv : SymEnv c)
    (tbF ebF : FFFormula c)
    (symEnv : SymEnv c) -- this is the one for the exit of the if-stmt
    : Except String (IfSpec c) := do
    let tbVarInfo ← getVar tbSymEnv id -- lookup the variable info in then-branch
    let ebVarInfo ← getVar ebSymEnv id -- lookup the variable info in else-branch
    if (ebVarInfo == tbVarInfo) then
      let symEnv' := setVar symEnv id tbVarInfo
      -- the variable has the same info in both branches, we can keep it as is
      return {
        inSymEnv := inSymEnv,
        outSymEnv := symEnv',
        tbF := tbF,
        ebF := ebF,
        nextId := cfg.nextId,
        newFFVars := emptyFFVarSet,
        newBoolVars := emptyBoolVarSet
      }
    else
      match tbVarInfo, ebVarInfo with
      | .ffVar v1, .ffVar v2 =>
        addFFVarInfo cfg md id v1 v2 inSymEnv tbSymEnv ebSymEnv tbF ebF symEnv
      | .ffArray v1, .ffArray v2 =>
        addArrayVarInfo cfg md id v1 v2 inSymEnv tbSymEnv ebSymEnv tbF ebF symEnv
      | _, _ => throw s!"Type mismatch for variable {id} in then-branch and else-branch"

def mergeIfBranches' {c : ZKConfig}
    (cfg : SymExecConfig c)
    (md : CmdMD)
    (inSymEnv tbSymEnv ebSymEnv : SymEnv c)
    (tbF ebF : FFFormula c)
    (liveVars : List VarID)
    (symEnv : SymEnv c) -- this is the one for the exit of the if-stmt
    : Except String (IfSpec c) := do
    match liveVars with
    | [] =>
        return {
          inSymEnv := symEnv,
          outSymEnv := symEnv,
          tbF := tbF,
          ebF := ebF,
          nextId := cfg.nextId,
          newFFVars := emptyFFVarSet,
          newBoolVars := emptyBoolVarSet
        }
    | varId :: rest =>
      -- handle one variable
      let ifSpecP ← addVarInfo cfg md varId inSymEnv tbSymEnv ebSymEnv tbF ebF symEnv
      let cfg' := { cfg with nextId := ifSpecP.nextId }
      -- handle the rest of variables
      let ifSpec' ← mergeIfBranches' cfg' md inSymEnv tbSymEnv ebSymEnv
                                     ifSpecP.tbF ifSpecP.ebF rest ifSpecP.outSymEnv
      return {
        inSymEnv := inSymEnv,
        outSymEnv := ifSpec'.outSymEnv,
        tbF := ifSpec'.tbF,
        ebF := ifSpec'.ebF,
        nextId := ifSpec'.nextId,
        newFFVars := ifSpecP.newFFVars ∪ ifSpec'.newFFVars,
        newBoolVars := ifSpecP.newBoolVars ∪ ifSpec'.newBoolVars
      }

def mergeIfBranches {c : ZKConfig}
    (cfg : SymExecConfig c)
    (md : CmdMD)
    (inSymEnv tbSymEnv ebSymEnv : SymEnv c)
    (tbF ebF : FFFormula c)
    (cond : Cond c)
    : Except String (CmdsSpec c) := do
    let condSpec ← sEvalCond cfg md inSymEnv cond
    let cfg' := { cfg with nextId := condSpec.nextId }
    let ifSpec ← mergeIfBranches' cfg' md inSymEnv tbSymEnv ebSymEnv
                                  tbF ebF md.liveness.live_out.toList emptySymEnv
    return {
      inSymEnv := ifSpec.inSymEnv,
      outSymEnv := ifSpec.outSymEnv,
      f := .ite (condSpec.f) ifSpec.tbF ifSpec.ebF,
      nextId := ifSpec.nextId,
      newFFVars := condSpec.newFFVars ∪ ifSpec.newFFVars,
      newBoolVars := condSpec.newBoolVars ∪ ifSpec.newBoolVars
    }



def fetchFuncSpec {c : ZKConfig}
  (specs : List (FuncSpec c)) (fname : FName) : Except String (FuncSpec c) :=
  match specs with
  | [] => Except.error s!"Spec for function {fname} not found"
  | spec :: specs' =>
      if spec.name == fname then
        Except.ok spec
      else
        fetchFuncSpec specs' fname

def symValueToMacroParam {c : ZKConfig}
  (acc : List (MacroCallParam c)) (sv : SymValue c)
  : List (MacroCallParam c) :=
  match sv with
  | .ffVar v =>
    match v with
    | .var ffVar => (.var (.inl ffVar)) :: acc
    | .const c => (.ff c) :: acc
  | .ffArray arr =>
    arr.toList.foldl (fun acc' elem =>
      match elem with
      | .var ffVar => (.var (.inl ffVar)) :: acc'
      | .const c => (.ff c) :: acc'
    ) acc

def simplExpsToMacroParams' {c : ZKConfig}
  (symEnv : SymEnv c) (acc : List (MacroCallParam c)) (exps : List (SimpleExpr c))
  : Except String (List (MacroCallParam c)) := do
  match exps with
  | [] => Except.ok acc
  | exp :: exps' =>
     let accm' ← match exp with
                     | SimpleExpr.var id =>
                       let param ← getVar symEnv id
                       pure (symValueToMacroParam acc param)
                     | SimpleExpr.val c => pure ((.ff c)::acc)
     simplExpsToMacroParams' symEnv accm' exps'

def simplExpsToMacroParams {c : ZKConfig}
  (symEnv : SymEnv c) (exps : List (SimpleExpr c)) : Except String (List (MacroCallParam c)) := do
  let ps ← simplExpsToMacroParams' symEnv [] exps
  return ps.reverse

def varsToMacroParams {c : ZKConfig}
  (cfg : SymExecConfig c)
  (md : CmdMD)
  (formalRets : List Param) -- there are the return types
  (actualRets : List VarID) -- there are the return variables in the caller
  (newFFVars : FFVarSet) -- the new finite field variables introduce for return variables
  (symEnv : SymEnv c) -- the symbolic environment in the caller
  (acc : List (MacroCallParam c))
  :
  Except String (RetVarsSpec c) := do
  match formalRets, actualRets with
  | [], [] => Except.ok {
      outSymEnv := symEnv,
      newFFVars := newFFVars,
      nextId := cfg.nextId,
      actRetsVars := acc.reverse
    }
  | (formalRet :: formalRets'), (actualRet :: actualRets') =>
      match formalRet.type with
      | VarType.ff =>
          let newId := cfg.nextId
          let md' := FFVarMetaData.mk actualRet md.src_info
          let newVar := FFVar.mk newId md'
          let symEnv' := setVar symEnv actualRet (.ffVar (.var newVar))
          let newFFVars' := newFFVars.insert newVar
          let cfg' := { cfg with nextId := cfg.nextId + 1 }
          let acc' := (.var (.inl newVar)) :: acc
          varsToMacroParams cfg' md formalRets' actualRets' newFFVars' symEnv' acc'
      | VarType.array size =>
          let newIds := List.range size -- new variable ids for array elements
          let ffVars := newIds.map
                         (fun id => FFVar.mk
                                      (id+cfg.nextId)
                                      (FFVarMetaData.mk s!"{actualRet}_at_{id}" md.src_info))
          let symVals := ffVars.map (fun v => (SymFFVar.var v))
          let newArray := symVals.toArray
          let symEnv' := setVar symEnv actualRet (.ffArray newArray)
          let newFFVars' := ffVars.foldl (fun s var => s.insert var) newFFVars
          let cfg' := { cfg with nextId := cfg.nextId + size }
          let acc' := ffVars.foldl (fun acc var => (.var (.inl var)) :: acc) acc
          varsToMacroParams cfg' md formalRets' actualRets' newFFVars' symEnv' acc'
  | _, _ => Except.error "Mismatch in the number of formal and actual parameters"



def seFuncCall {c : ZKConfig}
    (cfg : SymExecConfig c)
    (md : CmdMD)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (fname : FName)
    (args : List (SimpleExpr c))
    (outs : List VarID)
    : Except String (CmdsSpec c) := do
  let spec ← fetchFuncSpec specs fname
  let argParams ← simplExpsToMacroParams symEnv args
  let retVarsSpec ← varsToMacroParams cfg md spec.rets outs emptyFFVarSet symEnv []
  let ffAuxVars := List.range spec.numAuxFFVars
  let ffAuxVarParams : List (MacroCallParam c) :=
      ffAuxVars.map (fun id =>
         (.var (.inl (FFVar.mk
                         (id + retVarsSpec.nextId)
                         (FFVarMetaData.mk s!"{fname}_aux_{id}" md.src_info))))
      )
  let boolAuxVars := List.range spec.numAuxBoolVars
  let boolAuxVarParams : List (MacroCallParam c) :=
      boolAuxVars.map (fun id =>
         (.var (.inr (BoolVar.mk
                        (id + spec.numAuxFFVars + retVarsSpec.nextId)
                        (BoolVarMetaData.mk s!"{fname}_aux_{id}" md.src_info))))
      )
  let params := argParams ++ retVarsSpec.actRetsVars ++ ffAuxVarParams ++ boolAuxVarParams
  return {
    inSymEnv := symEnv,
    outSymEnv := retVarsSpec.outSymEnv,
    f := .call fname params,
    nextId := retVarsSpec.nextId + spec.numAuxFFVars + spec.numAuxBoolVars,
    newFFVars := retVarsSpec.newFFVars ∪ (ffAuxVarParams.foldl (fun s param =>
                      match param with
                      | .var (.inl ffVar) => s.insert ffVar
                      | _ => s) emptyFFVarSet),
    newBoolVars := boolAuxVarParams.foldl (fun s param =>
                      match param with
                      | .var (.inr boolVar) => s.insert boolVar
                      | _ => s) emptyBoolVarSet
  }



mutual


def seCmd {c : ZKConfig}
    (cfg : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c)) (i : ComWithMD c)
    : Except String (CmdsSpec c) := do
  match i with
   | .mk md cmd =>
      match cmd with
      | Com.skip => seSkip cfg md symEnv
      | Com.assign id e => seAssignment cfg md symEnv id e
      | Com.new_array id size => seNewArray cfg md symEnv id size
      | Com.read_array out a idx => seArrayRead cfg md symEnv out a idx
      | Com.write_array a idx value => seArrayWrite cfg md symEnv a idx value
      | Com.copy_array out a => seArrayCopy cfg md symEnv out a
      | Com.if_stmt cond tb eb =>
          match evalCond cfg md symEnv cond with
          | Except.error _e =>
              let tbSpec ← seCmds cfg symEnv specs tb
              let ebSpec ← seCmds cfg symEnv specs eb
              let cfg' := { cfg with nextId := max tbSpec.nextId ebSpec.nextId }
              mergeIfBranches
                 cfg' md
                symEnv tbSpec.outSymEnv ebSpec.outSymEnv tbSpec.f ebSpec.f cond
          | Except.ok condVal =>
              if condVal then
                let tb ← seCmds cfg symEnv specs tb
                return {
                  inSymEnv := tb.inSymEnv,
                  outSymEnv := tb.outSymEnv,
                  f := tb.f,
                  nextId := tb.nextId,
                  newFFVars := tb.newFFVars,
                  newBoolVars := tb.newBoolVars
                  }
              else
                let eb ← seCmds cfg symEnv specs eb
                return {
                  inSymEnv := eb.inSymEnv,
                  outSymEnv := eb.outSymEnv,
                  f := eb.f,
                  nextId := eb.nextId,
                  newFFVars := eb.newFFVars,
                  newBoolVars := eb.newBoolVars
                }
      | Com.loop_exp repExp body =>
          let rep ← simpleExprToFF symEnv repExp
          let loop := (ComWithMD.mk md (Com.loop rep.val body))
          seCmd cfg symEnv specs loop
      | Com.loop (rep+1) body =>
          let specFirstIter ← seCmds cfg symEnv specs body -- first iteration
          let cfg' := { cfg with nextId := specFirstIter.nextId }
          let specRestIter ←
                seCmd cfg' specFirstIter.outSymEnv specs (ComWithMD.mk md (Com.loop rep body))
          return {
            inSymEnv := symEnv,
            outSymEnv := specRestIter.outSymEnv,
            f := .and specFirstIter.f specRestIter.f,
            nextId := specRestIter.nextId,
            newFFVars := specFirstIter.newFFVars ∪ specRestIter.newFFVars,
            newBoolVars := specFirstIter.newBoolVars ∪ specRestIter.newBoolVars
          }
      | Com.loop 0 _body =>
          return {
            inSymEnv := symEnv,
            outSymEnv := symEnv,
            f := .true,
            nextId := cfg.nextId,
            newFFVars := emptyFFVarSet,
            newBoolVars := emptyBoolVarSet
          }

      | Com.func_call outs fname args =>
          seFuncCall cfg md symEnv specs fname args outs
termination_by (numOfLoopExpCom i, sizeOfCom i)
decreasing_by
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


def seCmds {c : ZKConfig}
  (cfg : SymExecConfig c)
  (symEnv : SymEnv c) (specs : List (FuncSpec c))  (cmds : List (ComWithMD c))
  : Except String (CmdsSpec c) := do
  match cmds with
  | [] => return {
      inSymEnv := symEnv,
      outSymEnv := symEnv,
      f := .true,
      nextId := cfg.nextId,
      newFFVars := emptyFFVarSet,
      newBoolVars := emptyBoolVarSet
  }
  | cmd :: rest => do
    let cmdSpec ← seCmd cfg symEnv specs cmd
    let cfg' := { cfg with nextId := cmdSpec.nextId }
    let cmdsSpec ← seCmds cfg' cmdSpec.outSymEnv specs rest
    return {
      inSymEnv := symEnv,
      outSymEnv := cmdsSpec.outSymEnv,
      f := .and cmdSpec.f cmdsSpec.f,
      nextId := cmdsSpec.nextId,
      newFFVars := cmdSpec.newFFVars ∪ cmdsSpec.newFFVars,
      newBoolVars := cmdSpec.newBoolVars ∪ cmdsSpec.newBoolVars
    }
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


def genInitialSymEnv {c : ZKConfig}
  (md : FuncMD) (args : List Param)
  : Except String (Nat × List FFVar × SymEnv c) := do
  let symEnv := emptySymEnv
  let rec loop (symEnv : SymEnv c) (args : List Param) (nextId : Nat) (acc : List FFVar)
    : Except String (Nat × List FFVar × SymEnv c) :=
    match args with
    | [] => Except.ok (nextId, acc.reverse, symEnv)
    | arg :: args' =>
        match arg.type with
        | VarType.ff =>
            let md := FFVarMetaData.mk s!"{arg.name}" md.src_info
            let newVar := FFVar.mk nextId md
            let symEnv' := setVar symEnv arg.name (.ffVar (.var newVar))
            loop symEnv' args' (nextId + 1) (newVar :: acc)
        | VarType.array size =>
            let newIds := List.range size -- new variable ids for array elements
            let ffVars := newIds.map
                         (fun id => FFVar.mk
                                      (id+nextId)
                                      (FFVarMetaData.mk s!"{arg.name}_at_{id}" md.src_info))
            let symVals := ffVars.map (fun v => (SymFFVar.var v))
            let newArray := symVals.toArray
            let symEnv' := setVar symEnv arg.name (.ffArray newArray)
            let accm' := ffVars.foldl (fun acc var => var :: acc) acc
            loop symEnv' args' (nextId + size) accm'
  loop symEnv args 0 []

def genRetsBinding {c : ZKConfig}
    (cfg : SymExecConfig c) (md : FuncMD)
    (rets : List Param)
    (bodySpecOutSymEnv : SymEnv c)
    (bodySpecF : FFFormula c)
    : Except String (Nat × (List FFVar) × (FFFormula c)) :=
  let rec loop (rets : List Param) (nextId : Nat) (acc : List FFVar) (bodySpecF : FFFormula c)
    : Except String (Nat × (List FFVar) × (FFFormula c)) := do
    match rets with
    | [] => Except.ok (nextId, acc.reverse, bodySpecF)
    | ret :: rets' =>
        let symVal ← getVar bodySpecOutSymEnv ret.name
        match symVal with
        | .ffVar v =>
          let t := symVarToTerm v
          let ffVar := FFVar.mk cfg.nextId (FFVarMetaData.mk s!"ret_{ret.name}" md.src_info)
          let f := .eq (FFTerm.var ffVar) t
          loop rets' (nextId + 1) (ffVar :: acc) (.and bodySpecF f)
        | .ffArray arr =>
          let ts := arr.toList.map symVarToTerm
          let (_,nextId',acc',bodySpecF') :=
              ts.foldl (fun (s : Nat × Nat × List FFVar × FFFormula c) (v : FFTerm c) =>
                  let (idx, nextId, acc, f) := s
                  let ffVar := FFVar.mk
                                 nextId
                                 (FFVarMetaData.mk s!"ret_{ret.name}_at_{idx}" md.src_info)
                  let eq := .eq (FFTerm.var ffVar) v
                  (idx + 1, nextId + 1, ffVar :: acc, .and f eq))
                (0, cfg.nextId, [], bodySpecF)
          loop rets' nextId' acc' bodySpecF'
  loop rets cfg.nextId [] bodySpecF


def seExecFunc {c : ZKConfig}
    (cfg : SymExecConfig c) (md : FuncMD)
    (f : Func c) (specs : List (FuncSpec c))
    : Except String (FuncSpec c) := do
  match f with
  | .mk name params rets body =>
    let (nextId, inVars, symEnv) ← genInitialSymEnv md params
    let cfg := { cfg with nextId := nextId }
    let bodySpec ← seCmds cfg symEnv specs body
    let (nextId, retVars, bodySpecF) ← genRetsBinding cfg md rets bodySpec.outSymEnv bodySpec.f
    let boolAuxVars : List Var := bodySpec.newBoolVars.toList.map (fun v => .inr v)
    let ffAuxVars : List Var := bodySpec.newFFVars.toList.map (fun v => .inl v)
    let auxVars := ffAuxVars ++ boolAuxVars
    let allVars := inVars.map (.inl ·) ++ retVars.map (.inl ·) ++ auxVars
    return {
      name := name,
      inSymEnv := symEnv,
      outSymEnv := bodySpec.outSymEnv,
      params := params,
      rets := rets,
      f := {name := name, params := allVars, body := bodySpecF},
      nextId := nextId,
      numAuxFFVars := ffAuxVars.length,
      numAuxBoolVars := boolAuxVars.length,
      }


def seExecFuncs {c : ZKConfig}
    (cfg : SymExecConfig c) (p : List (FuncWithMD c)) :=
  let rec loop (funcs : List (FuncWithMD c)) (specs : List (FuncSpec c))
    : Except String (List (FuncSpec c)) := do
    match funcs with
    | [] => Except.ok specs
    | func :: funcs' =>
        match func with
        | .mk md func =>
          let spec ← seExecFunc cfg md func specs
          loop funcs' (spec :: specs)
  loop p.reverse []

def seExecProg {c : ZKConfig}
    (cfg : SymExecConfig c)
    (p : ProgWithMD c)
    (mainFuncName : FName)
    : Except String (FFConstraintSystem c) := do
    match p with
    | .mk _ funcs =>
    let funcSpecs ← seExecFuncs cfg funcs
    let macros := funcSpecs.map (fun spec => spec.f)
    return {
      macros := macros,
      main := mainFuncName
    }

end Llzk.SymExec.BigStep
