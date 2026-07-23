import Corellzk2smt.Basic
import Corellzk2smt.Config
import Corellzk2smt.SymExec.Basic
import Corellzk2smt.SymExec.Common
import Corellzk2smt.FFConstraints.Basic
import Corellzk2smt.Language.Core.Syntax.AST
import Corellzk2smt.Language.Core.Analysis.DefinedVars


namespace Corellzk2smt.SymExec.BigStep


open Corellzk2smt.Config (GlobalConfig)
open Corellzk2smt.Language.Core.Syntax.AST
open Corellzk2smt.SymExec.Basic
open Corellzk2smt.FFConstraints.Basic
open Corellzk2smt.Language.Core.Analysis.DefinedVars



def seSimpleCmd {c : ZKConfig}
    (_gconf : GlobalConfig c)
    (_sconf : SymExecConfig c)
    (_symEnv : SymEnv c)
    (_specs : List (FuncSpec c))
    (_i : ComWithMD c)
    : Except String (CmdsSpec c) :=
    Except.error "TBD"

/-- Mint the macro-call arguments (one fresh `ff` var, or `size` fresh `ff` vars for an array)
    for a single return parameter, together with the `SymValue` those fresh vars denote (what
    gets bound into the caller's own output variable via `setVars`). -/
def mintFreshRetParam {c : ZKConfig} (nextVarId : Nat) (type : VarType)
    : Nat × List (MacroCallParam c) × SymValue c :=
  match type with
  | .ff =>
      (nextVarId + 1, [MacroCallParam.var (Var.ffv nextVarId)],
        SymValue.simple (SimpleSymVal.ffvar { var := nextVarId, bits := none }))
  | .array size =>
      let ids := (List.range size).map (fun i => nextVarId + i)
      (nextVarId + size,
        ids.map (fun v => MacroCallParam.var (Var.ffv v)),
        SymValue.array (ids.map (fun v => SimpleSymVal.ffvar { var := v, bits := none })).toArray)

/-- `mintFreshRetParam`, for a whole `rets` list -- in order, threading the fresh-var counter. -/
def mintFreshRets {c : ZKConfig} (nextVarId : Nat) (rets : List Param)
    : Nat × List (MacroCallParam c) × List (SymValue c) :=
  match rets with
  | [] => (nextVarId, [], [])
  | r :: rest =>
      let (nv1, params1, val1) := mintFreshRetParam nextVarId r.type
      let (nv2, params2, vals2) := mintFreshRets nv1 rest
      (nv2, params1 ++ params2, val1 :: vals2)

/-- Mint the trailing macro-call arguments for a callee's auxiliary (internal-only) vars --
    fresh, existentially-unconstrained from the caller's perspective; the callee's own macro
    body is whatever pins down their values. -/
def mintFreshAuxParams {c : ZKConfig} (nextVarId : Nat) (numFFVars numBoolVars : Nat)
    : Nat × List (MacroCallParam c) :=
  let ffIds := (List.range numFFVars).map (fun i => nextVarId + i)
  let nv1 := nextVarId + numFFVars
  let boolIds := (List.range numBoolVars).map (fun i => nv1 + i)
  let nv2 := nv1 + numBoolVars
  (nv2, (ffIds.map (fun v => MacroCallParam.var (Var.ffv v))) ++
        (boolIds.map (fun v => MacroCallParam.var (Var.boolv v))))

/-- Resolve a single actual argument against its declared parameter type, flattening an array
    into its individual elements' macro-call params (in order) -- the reverse direction of
    `mintFreshRetParam`, for the *input* side. -/
def flattenArgVal {c : ZKConfig} (type : VarType) (v : SymValue c)
    : Except String (List (MacroCallParam c)) :=
  match type, v with
  | .ff, .simple sv => Except.ok [simpleSymValToMacroCallParam sv]
  | .array size, .array arr =>
      if arr.size == size then
        Except.ok (arr.toList.map simpleSymValToMacroCallParam)
      else
        Except.error "seFuncCall: array argument size mismatch"
  | _, _ => Except.error "seFuncCall: argument shape doesn't match parameter type"

/-- `flattenArgVal`, for a whole `params`/`argVals` list pair. -/
def flattenArgVals {c : ZKConfig} (params : List Param) (argVals : List (SymValue c))
    : Except String (List (MacroCallParam c)) :=
  match params, argVals with
  | [], [] => Except.ok []
  | p :: ps, v :: vs =>
      match flattenArgVal p.type v with
      | Except.error e => Except.error e
      | Except.ok ps1 =>
        match flattenArgVals ps vs with
        | Except.error e => Except.error e
        | Except.ok ps2 => Except.ok (ps1 ++ ps2)
  | _, _ => Except.error "seFuncCall: mismatched argument count"

/-- Translate a function call: look up the callee's spec, resolve/flatten the actual
    arguments against its declared `params`, mint fresh call-site variables for its `rets`
    (bound into the caller's `outs`) and for its auxiliary vars, and emit a macro-call formula
    referencing the callee's macro by name with all of those as arguments, in
    params-then-rets-then-aux order (matching `FFMacro.params`'s own layout, see `seFunc`). -/
def seFuncCall {c : ZKConfig}
    (_gconf : GlobalConfig c)
    (sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (specs : List (FuncSpec c))
    (fname : FName)
    (args : List (SimpleExpr c))
    (outs : List VarID)
    : Except String (CmdsSpec c) :=
  match fetchFuncSpec specs fname with
  | Except.error e => Except.error e
  | Except.ok spec =>
    match resolveSimpleExprsToSymValue symEnv args with
    | Except.error e => Except.error e
    | Except.ok argVals =>
      match flattenArgVals spec.params argVals with
      | Except.error e => Except.error e
      | Except.ok inputParams =>
        let (nv1, outputParams, outVals) := mintFreshRets sconf.nextVarId spec.rets
        let (nv2, auxParams) := mintFreshAuxParams nv1 spec.numAuxFFVars spec.numAuxBoolVars
        match setVars symEnv outs outVals with
        | Except.error e => Except.error e
        | Except.ok outSymEnv' =>
          Except.ok {
            inSymEnv := symEnv,
            outSymEnv := outSymEnv',
            f := FFFormula.call spec.f.name (inputParams ++ outputParams ++ auxParams),
            nextVarId := nv2
          }

/-- Try to decide a condition without generating a formula, by constant-folding both sides
    (mirrors `evalCond`, but via `tryEvalSimpleExprToFFValue` -- so it only succeeds when both
    sides resolve to constants in `symEnv`). -/
def tryEvalCondToConcreteValue {c : ZKConfig}
    (_gconf : GlobalConfig c)
    (_sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (_md : CmdMD)
    (cond : Cond c)
    : Except String Bool :=
  match cond with
  | .eq s1 s2 =>
    match tryEvalSimpleExprToFFValue symEnv s1 with
    | Except.error err => Except.error err
    | Except.ok val1 =>
      match tryEvalSimpleExprToFFValue symEnv s2 with
      | Except.error err => Except.error err
      | Except.ok val2 =>
        if val1 = val2 then
          Except.ok true
        else
          Except.ok false

/-- Encode a condition as a formula, by resolving both sides against the symbolic
    environment (unlike `tryEvalCondToConcreteValue`, this always succeeds as long as both
    sides resolve to scalars, constant or not). -/
def encodeCond {c : ZKConfig} (symEnv : SymEnv c) (cond : Cond c) : Except String (FFFormula c) :=
  match cond with
  | .eq s1 s2 =>
    match resolveSimpleExpr symEnv s1 with
    | Except.error e => Except.error e
    | Except.ok sv1 =>
      match resolveSimpleExpr symEnv s2 with
      | Except.error e => Except.error e
      | Except.ok sv2 =>
        Except.ok (FFFormula.eq (simpleSymValToTerm sv1) (simpleSymValToTerm sv2))

/-- Whether two simple symbolic values are "the same" for merge purposes: same constant, or
    the same constraint variable *with* the same cached binary expansion. The cached expansion
    is compared too (not just the variable index) because the same variable can end up with a
    different binarization on each branch (e.g. one branch triggers a `bitify` and the other
    doesn't, or they bitify differently), and picking one branch's cached bits unconditionally
    would silently carry a decomposition that isn't actually valid on the other branch. -/
def simpleSymValAgree {c : ZKConfig} (s1 s2 : SimpleSymVal c) : Bool :=
  match s1, s2 with
  | .const v1, .const v2   => v1 == v2
  | .ffvar v1, .ffvar v2   => v1.var == v2.var && v1.bits == v2.bits
  | _, _                   => false

/-- Merge a single scalar position from the two branches: if they agree, keep that value with
    no new formula content; if they disagree, mint a fresh variable for the merged position and
    record, for each branch, the equation tying that fresh variable to what the branch actually
    computed there (added under that branch's own guard by the caller). Returns the merged
    value together with the updated (nextVarId, tb-side equations, eb-side equations), threaded
    explicitly rather than through a state monad. -/
def mergeSimpleSymVal {c : ZKConfig}
    (nextVarId : Nat) (tbExtra ebExtra : FFFormula c) (svTb svEb : SimpleSymVal c)
    : SimpleSymVal c × Nat × FFFormula c × FFFormula c :=
  if simpleSymValAgree svTb svEb then
    (svTb, nextVarId, tbExtra, ebExtra)
  else
    let nv := nextVarId
    let merged := SimpleSymVal.ffvar { var := nv, bits := none }
    let tbExtra' := FFFormula.and tbExtra (FFFormula.eq (FFTerm.var nv) (simpleSymValToTerm svTb))
    let ebExtra' := FFFormula.and ebExtra (FFFormula.eq (FFTerm.var nv) (simpleSymValToTerm svEb))
    (merged, nv + 1, tbExtra', ebExtra')

/-- Merge a single variable's value from the two branches. Scalars merge directly
    (`mergeSimpleSymVal`); arrays merge position-by-position, so only the positions that
    actually disagree cost a fresh variable, rather than the whole array. Branches disagreeing
    on shape (array vs. scalar, or arrays of different length) is a genuine error: every
    variable is expected to have the same shape -- array of the same length, or a scalar
    (constant or variable) -- on both sides of a conditional. -/
def mergeSymValue {c : ZKConfig}
    (nextVarId : Nat) (tbExtra ebExtra : FFFormula c) (svTb svEb : SymValue c)
    : Except String (SymValue c × Nat × FFFormula c × FFFormula c) :=
  match svTb, svEb with
  | .simple s1, .simple s2 =>
      let (merged, nv, tbE, ebE) := mergeSimpleSymVal nextVarId tbExtra ebExtra s1 s2
      Except.ok (.simple merged, nv, tbE, ebE)
  | .array arrTb, .array arrEb =>
      if arrTb.size = arrEb.size then
        let (nv, tbE, ebE, mergedRev) := (arrTb.toList.zip arrEb.toList).foldl
          (fun acc p =>
            let (nextVarId, tbExtra, ebExtra, merged) := acc
            let (mergedVal, nv, tbE, ebE) := mergeSimpleSymVal nextVarId tbExtra ebExtra p.1 p.2
            (nv, tbE, ebE, mergedVal :: merged))
          (nextVarId, tbExtra, ebExtra, [])
        Except.ok (.array mergedRev.reverse.toArray, nv, tbE, ebE)
      else
        Except.error "mergeSymValue: array size mismatch across branches"
  | _, _ => Except.error "mergeSymValue: type mismatch across branches (array vs. scalar)"

/-- Merge every variable of two symbolic environments with the same domain (guaranteed by
    zero-initializing every function-local variable at entry, see `Semantics/DefinedVars.lean`
    and `zeroInitEnv` -- so an if-statement's two branches always agree on which variables
    exist, only possibly on what they hold). -/
def mergeSymEnvKeys {c : ZKConfig}
    (nextVarId : Nat) (tbEnv ebEnv : SymEnv c) (tbExtra ebExtra : FFFormula c)
    (keys : List VarID)
    : Except String (SymEnv c × Nat × FFFormula c × FFFormula c) :=
  match keys with
  | [] => Except.ok (emptySymEnv, nextVarId, tbExtra, ebExtra)
  | id :: rest =>
    match getVar tbEnv id with
    | Except.error e => Except.error e
    | Except.ok svTb =>
      match getVar ebEnv id with
      | Except.error e => Except.error e
      | Except.ok svEb =>
        match mergeSymValue nextVarId tbExtra ebExtra svTb svEb with
        | Except.error e => Except.error e
        | Except.ok (mergedVal, nv, tbE, ebE) =>
          match mergeSymEnvKeys nv tbEnv ebEnv tbE ebE rest with
          | Except.error e => Except.error e
          | Except.ok (restEnv, nv', tbE', ebE') =>
            Except.ok (setVar restEnv id mergedVal, nv', tbE', ebE')

def mergeSymEnv {c : ZKConfig}
    (nextVarId : Nat) (tbEnv ebEnv : SymEnv c)
    : Except String (SymEnv c × Nat × FFFormula c × FFFormula c) :=
  mergeSymEnvKeys nextVarId tbEnv ebEnv FFFormula.true FFFormula.true tbEnv.keys

/-- Merge the specs of the two branches of an `if`: `ite g (f_tb ∧ tbExtra) (f_eb ∧ ebExtra)`,
    where `tbExtra`/`ebExtra` tie every merge-introduced fresh variable to what its own branch
    actually computed. `.ite` (rather than the logically-equivalent `g ∧ A ∨ ¬g ∧ B`) is
    important here, not just cosmetic: `evalFormula` short-circuits `.ite` -- it only ever
    evaluates the branch `g` actually selects -- so the untaken branch's well-formedness/
    totality is never needed to know the whole formula evaluates. `sconf` isn't threaded
    between the two branches' translation (both start counting fresh variables from the same
    point, i.e. variables *can* be reused between them) -- sound because only one branch's
    formula is ever actually evaluated for a given concrete execution. Merging itself continues
    on from whichever branch minted more variables, `max tbSpec.nextVarId ebSpec.nextVarId`. -/
def mergeIfBranches {c : ZKConfig}
    (_gconf : GlobalConfig c)
    (_sconf : SymExecConfig c)
    (symEnv : SymEnv c)
    (_specs : List (FuncSpec c))
    (_md : CmdMD)
    (tbSpec : CmdsSpec c)
    (ebSpec : CmdsSpec c)
    (cond : Cond c)
    : Except String (CmdsSpec c) :=
  match encodeCond symEnv cond with
  | Except.error e => Except.error e
  | Except.ok g =>
    match mergeSymEnv (max tbSpec.nextVarId ebSpec.nextVarId) tbSpec.outSymEnv ebSpec.outSymEnv with
    | Except.error e => Except.error e
    | Except.ok (mergedEnv, nextVarId', tbExtra, ebExtra) =>
      Except.ok {
        inSymEnv := symEnv,
        outSymEnv := mergedEnv,
        f := FFFormula.ite g (FFFormula.and tbSpec.f tbExtra) (FFFormula.and ebSpec.f ebExtra),
        nextVarId := nextVarId'
      }

/-- Sequence two `CmdsSpec`s: conjoin their formulas and thread the first's output as the
    second's input. Purely structural glue -- doesn't need to know what either half actually
    computes (see `seqComposition_correct`).

    `cmd` is the command whose translation this composition corresponds to; it isn't used yet
    beyond annotating `cmdSpec1.f`'s conjunct with an (currently empty) description -- to be
    filled in later with something derived from `cmd`. The annotation is `FFFormula.anno`,
    which every consumer of formulas (`evalFormula`, `ffVarsOfFormula`, ...) passes through
    unchanged, so it carries no semantic weight. -/
def seqComposition {c : ZKConfig}
    (_gconf : GlobalConfig c)
    (_sconf : SymExecConfig c)
    (_cmd : ComWithMD c)
    (cmdSpec1 : CmdsSpec c)
    (cmdsSpec2 : CmdsSpec c)
    : Except String (CmdsSpec c) :=
  Except.ok {
    inSymEnv := cmdSpec1.inSymEnv,
    outSymEnv := cmdsSpec2.outSymEnv,
    f := FFFormula.and (.anno cmdSpec1.f "") cmdsSpec2.f,
    nextVarId := cmdsSpec2.nextVarId
  }

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
            match seCmds gconf sconf symEnv specs eb with
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
              seqComposition gconf sconf i specFirstIter specRestIter
      -- Loop with 0 iterations.
      | Com.loop 0 _body =>
          Except.ok {
            inSymEnv := symEnv,
            outSymEnv := symEnv,
            f := FFFormula.true,
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
      f := FFFormula.true,
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
        seqComposition gconf sconf cmd cmdSpec cmdsSpec

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


/-- Mint fresh symbolic variables for a single function parameter -- one for `.ff`, `size`
    (consecutive) for `.array size`, mirroring `mintFreshRetParam`'s own array branch (the
    call-site/return-value mirror of this function): the updated counter, the `Var`s for the
    macro's formal parameter list (in order), and the `SymValue` to bind into the entry symbolic
    environment under the parameter's program-variable name. -/
def mintFreshParam {c : ZKConfig} (nextVarId : Nat) (type : VarType)
    : Except String (Nat × List Var × SymValue c) :=
  match type with
  | .ff => Except.ok (nextVarId + 1, [Var.ffv nextVarId],
      SymValue.simple (SimpleSymVal.ffvar { var := nextVarId, bits := none }))
  | .array size =>
      let ids := (List.range size).map (fun i => nextVarId + i)
      Except.ok (nextVarId + size, ids.map Var.ffv,
        SymValue.array (ids.map (fun v => SimpleSymVal.ffvar { var := v, bits := none })).toArray)

/-- `mintFreshParam`, for a whole `params` list -- threading the fresh-var counter and building
    up the entry symbolic environment (which must already have every function-local variable
    defined, per `definedVarsOfFunc`, so that body execution's variable lookups never fail
    structurally, mirroring `zeroInitEnv` + `bindInParams` on the concrete side). -/
def mintFreshParams {c : ZKConfig} (nextVarId : Nat) (params : List Param) (env : SymEnv c)
    : Except String (Nat × List Var × SymEnv c) :=
  match params with
  | [] => Except.ok (nextVarId, [], env)
  | p :: ps =>
    match mintFreshParam (c := c) nextVarId p.type with
    | Except.error e => Except.error e
    | Except.ok (nv1, vs, sv) =>
      match mintFreshParams nv1 ps (setVar env p.name sv) with
      | Except.error e => Except.error e
      | Except.ok (nv2, vs2, env') => Except.ok (nv2, vs ++ vs2, env')

/-- Mint fresh symbolic variable(s) for a single return parameter, together with (a conjunction
    of) equality constraint(s) tying them to whatever the return-named program variable
    currently resolves to in `bodySymEnv` (the body's own `outSymEnv`) -- this decouples the
    macro's formal return port(s) from whatever internal variable the body happened to compute
    the return value into, exactly mirroring how `seFuncCall` mints fresh call-site output vars
    rather than reusing the callee's internal ones. `.array size` mints `size` fresh vars (one
    equation per element, conjoined via `foldr .and .true` -- a right-nested conjunction, the
    same shape as this function's own outer per-ret conjunction below) instead of one. -/
def mintFreshRetWithEq {c : ZKConfig} (nextVarId : Nat) (bodySymEnv : SymEnv c) (ret : Param)
    : Except String (Nat × List Var × SymValue c × FFFormula c) :=
  match ret.type with
  | .ff =>
    match getVar bodySymEnv ret.name with
    | Except.error e => Except.error e
    | Except.ok (.array _) =>
        Except.error s!"seFunc: return variable '{ret.name}' is an array, expected scalar"
    | Except.ok (.simple sv) =>
        Except.ok (nextVarId + 1, [Var.ffv nextVarId],
          SymValue.simple (SimpleSymVal.ffvar { var := nextVarId, bits := none }),
          FFFormula.eq (FFTerm.var nextVarId) (simpleSymValToTerm sv))
  | .array size =>
    match getVar bodySymEnv ret.name with
    | Except.error e => Except.error e
    | Except.ok (.simple _) =>
        Except.error s!"seFunc: return variable '{ret.name}' is a scalar, expected array"
    | Except.ok (.array arr) =>
        if arr.size == size then
          let ids := (List.range size).map (fun i => nextVarId + i)
          let eqs := (arr.toList.zip ids).map
            (fun p => FFFormula.eq (FFTerm.var p.2) (simpleSymValToTerm p.1))
          Except.ok (nextVarId + size, ids.map Var.ffv,
            SymValue.array
              (ids.map (fun v => SimpleSymVal.ffvar { var := v, bits := none })).toArray,
            eqs.foldr FFFormula.and FFFormula.true)
        else
          Except.error "seFunc: return array size mismatch"

/-- `mintFreshRetWithEq`, for a whole `rets` list -- also returns the list of
    (return-variable-name, fresh `SymValue`) pairs to rebind into the body's `outSymEnv`, and
    the conjunction of all the per-return equality constraints (defaulting to `.true` for no
    returns, the identity for `.and`-conjunction). -/
def mintFreshRetsWithEq {c : ZKConfig} (nextVarId : Nat) (bodySymEnv : SymEnv c)
    (rets : List Param) :
    Except String (Nat × List Var × List (VarID × SymValue c) × FFFormula c) :=
  match rets with
  | [] => Except.ok (nextVarId, [], [], FFFormula.true)
  | r :: rs =>
    match mintFreshRetWithEq nextVarId bodySymEnv r with
    | Except.error e => Except.error e
    | Except.ok (nv1, vs, sv, eqf) =>
      match mintFreshRetsWithEq nv1 bodySymEnv rs with
      | Except.error e => Except.error e
      | Except.ok (nv2, vs2, binds, restf) =>
        Except.ok (nv2, vs ++ vs2, (r.name, sv) :: binds, FFFormula.and eqf restf)

/-- Translate a function definition into a `FuncSpec`: mint fresh vars for the params (the
    entry symbolic environment, matching concrete `zeroInitEnv`+`bindInParams`), symbolically
    execute the body, mint fresh vars (with equality constraints) for the returns, and collect
    every other variable the body's formula mentions as the macro's trailing auxiliary
    parameters -- `Var`'s `Ord` instance sorts every `.ffv` before any `.boolv`, so
    `(VarSet).toList` already gives exactly the "all-ff-then-all-bool" layout `seFuncCall`'s
    `mintFreshAuxParams` assumes at the call site, with no separate reordering needed. FF-only
    for now (matching `seFuncCall_correct`'s current scope) -- `mintFreshParam`/
    `mintFreshRetWithEq` reject array params/rets outright. -/
def seFunc {c : ZKConfig}
  (gconf : GlobalConfig c)
  (specs : List (FuncSpec c))
  (f : Func c)
  : Except String (FuncSpec c) :=
  match f with
  | Func.mk name params rets body =>
    if hasDupNames (params.map (·.name)) || hasDupNames (rets.map (·.name)) then
      Except.error s!"Function '{name}' has a duplicate parameter name or a duplicate return name"
    else
      let zeroSymEnv : SymEnv c :=
        (definedVarsOfFunc f).foldl
          (fun env id => setVar env id (SymValue.simple (SimpleSymVal.const 0))) emptySymEnv
      match mintFreshParams (c := c) 0 params zeroSymEnv with
      | Except.error e => Except.error e
      | Except.ok (nv1, paramVars, inSymEnv) =>
        match seCmds gconf { nextVarId := nv1 } inSymEnv specs body with
        | Except.error e => Except.error e
        | Except.ok bodySpec =>
          match mintFreshRetsWithEq (c := c) bodySpec.nextVarId bodySpec.outSymEnv rets with
          | Except.error e => Except.error e
          | Except.ok (nv2, retVars, retBinds, retEqFormula) =>
            let outSymEnv :=
              retBinds.foldl (fun env (id, sv) => setVar env id sv) bodySpec.outSymEnv
            let paramVarSet : VarSet := paramVars.foldl (fun acc v => acc.insert v) emptyVarSet
            let retVarSet : VarSet := retVars.foldl (fun acc v => acc.insert v) emptyVarSet
            let bodyVars := ffVarsOfFormula bodySpec.f ∪ bVarsOfFormula bodySpec.f ∪
              ffVarsOfFormula retEqFormula ∪ bVarsOfFormula retEqFormula
            let auxVarsList := (bodyVars \ (paramVarSet ∪ retVarSet)).toList
            let numAuxFFVars := (auxVarsList.filter
              (fun v => match v with | .ffv _ => true | .boolv _ => false)).length
            let numAuxBoolVars := auxVarsList.length - numAuxFFVars
            Except.ok {
              name := name,
              inSymEnv := inSymEnv,
              outSymEnv := outSymEnv,
              f := { name := name, params := paramVars ++ retVars ++ auxVarsList,
                     body := FFFormula.and bodySpec.f retEqFormula },
              nextVarId := nv2,
              params := params,
              rets := rets,
              numAuxFFVars := numAuxFFVars,
              numAuxBoolVars := numAuxBoolVars
            }


def seExecFuncs {c : ZKConfig}
  (gconf : GlobalConfig c)
  (p : List (FuncWithMD c)) : Except String (List (FuncSpec c)) :=
  let rec loop (funcs : List (FuncWithMD c)) (specs : List (FuncSpec c))
    : Except String (List (FuncSpec c)) := do
    match funcs with
    | [] => Except.ok specs
    | func :: funcs' =>
        match func with
        | .mk md func =>
          let spec ← seFunc gconf specs func
          loop funcs' (spec :: specs)
  if hasDupFuncNames p then
    Except.error "Program has two functions with the same name"
  else
    loop p.reverse []

def seExecProg {c : ZKConfig}
  (gconf : GlobalConfig c)
  (p : ProgWithMD c)
  (mainFuncName : FName)
  : Except String (FFConstraintSystem c) := do
  match p with
    | .mk _ funcs =>
      let funcSpecs ← seExecFuncs gconf funcs
      let macros := funcSpecs.map (fun spec => spec.f)
      return {
        macros := macros,
        main := mainFuncName
      }


end Corellzk2smt.SymExec.BigStep
