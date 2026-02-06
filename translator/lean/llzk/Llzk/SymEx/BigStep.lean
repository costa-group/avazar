import Llzk.Basic
import Llzk.Language.Core.Syntax
import Llzk.SymEx.FFConstraints
import Std.Data.TreeMap.Basic

namespace Llzk.SymEx.BigStep

open Llzk.SymEx.FFConstraints
open Llzk.Language.Core

/- Symbolic Environment: A mapping from variable names to FF Variables -/
abbrev SymEnv := Std.TreeMap ProgVarID FFVar

/- An abstraction of the different operations of an environment -/
def emptySEnv : SymEnv := Std.TreeMap.empty

/- Retrive a value from an environemnt. It fails if the variable
   is not in the environemt -/
def get_var (senv : SymEnv) (id : ProgVarID) : Except String FFVar :=
  match senv.get? id with
  | some v => Except.ok v
  | none   => Except.error s!"Variable '{id}' not found"

/- Set the value of a variable in an environemnt. It updates
   the value if it exists already -/
def set_var (senv : SymEnv) (id : ProgVarID) (v : FFVar) : SymEnv :=
  senv.insert id v

/- Update the value of a variable in an environemnt. It fails if the variable
   is not in the environemt -/
def update_var (senv : SymEnv) (id : ProgVarID) (v : FFVar) : Except String SymEnv :=
  if senv.contains id then
    return senv.insert id v
  else
    throw s!"Variable '{id}' not found"

/- A representation for a symbolic state
-/
structure SymState (c : ZKConfig) where
  in_senv : SymEnv   -- Symbolic environment before the cmd
  out_senv : SymEnv  -- Symbolic environment after the cmd
  p: Prog c          -- The corresponding program, don't know if we will need it at the end
  f : FFFormula c    -- Symbolic denotation of the command
  max_var_id : Nat   -- The maximum variable ID used in `f`
  deriving Repr

/- Evaluates a simple expression in the given symbolic environment -/
def eval_simple {c : ZKConfig}
  (senv : SymEnv) (sexp : SimpleExpr c) : Except String (FFTerm c) := do
  match sexp with
  | .inr v => return (.const v)
  | .inl v => return (.var (← get_var senv v))

/- This function, and the next, are used when handling if-statment, to make both
   branches consistent wrt. the outcoming symbolic environment -/
def add_phi_formula_aux {c : ZKConfig}
  (md : CmdMetaData)
  (l1 l2 : List (ProgVarID × FFVar))
  (senv : SymEnv)
  (f1 f2 : FFFormula c)
  (max_var_id : ℕ)
  : Except String (SymEnv × FFFormula c × FFFormula c × ℕ) := do
  match l1, l2 with
  | [], [] => return (senv, f1, f2, max_var_id)
  | (id1, v1)::rest1, (id2, v2)::rest2 =>
      if id1 = id2 && v1.meta_data.orig_name = v2.meta_data.orig_name then
        if v1.id = v2.id then
          let senv' := senv.insert id1 v1
          add_phi_formula_aux md rest1 rest2 senv' f1 f2 max_var_id
        else
          let max_var_id' := max_var_id + 1
          let v := {
                     id := max_var_id',
                     meta_data := { orig_name := v2.meta_data.orig_name, cmd_meta_data := md }
                   }
          let f1' := .and f1 (.eqZero (.sub (.var v) (.var v1)))
          let f2' := .and f2 (.eqZero (.sub (.var v) (.var v2)))
          let senv' := senv.insert id1 v
          add_phi_formula_aux md rest1 rest2 senv' f1' f2' max_var_id'
      else
        throw s!"Mismatched variable IDs: {id1} and {id2}"
  | _,_ => throw "Mismatched variable list lengths"


def add_phi_formula {c : ZKConfig}
  (md : CmdMetaData)
  (senv1 senv2 : SymEnv)
  (ft fe : FFFormula c)
  (max_var_id : ℕ) := do
    add_phi_formula_aux md senv1.toList senv2.toList emptySEnv ft fe max_var_id


/-
  Generates a formula for `out := a << bits`.
  It decomposes `a` into `c.k` bits, ensures they are boolean,
  and reconstructs `out` from the shifted bits (dropping overflows).

  Params:
  - out: The output variable (as FFVar).
  - a: A term that can be a variable or a constant (as FFTerm)
  - bits: The shift amount.
  - nextId: The starting ID for the fresh internal bit variables.
-/
def genSHLFormula {c : ZKConfig}
    (out : FFVar)
    (a : FFTerm c)
    (bits : ℕ)
    (max_var_id : ℕ)
    : FFFormula c :=
  let k := c.k
  -- 1. Create the range of bit indices [0, ..., k-1]
  let indices := List.range k
  -- 2. Generate the fresh variables for the bits of 'a'
  --    We map index 'i' to variable with ID 'nextId + i'
  let bitVars : List (ℕ × FFVar) := indices.map (fun i =>
    (i, {
          id := max_var_id + 1 + i, -- max_var_id is the last used ID, start from next one
          meta_data := { orig_name := s!"bit_{i}", cmd_meta_data := default }
        })
  )
  -- 3. Constraint: Boolean checks for all bits: b * (b - 1) = 0
  --    Equivalently: b^2 - b = 0, or just b * b = b.
  --    Using the explicit form: b * (b -1) = 0
  let boolConstrs := bitVars.map (fun (_, bVar) =>
    let bTerm := FFTerm.var bVar
    FFFormula.eqZero (.mul bTerm (.sub bTerm (.const 1)))
  )
  -- 4. Constraint: Recomposition of 'a'
  --    a = sum(b_i * 2^i)  =>  a - sum(...) = 0
  let sumA := bitVars.foldl (fun acc (i, bVar) =>
    let coeff := (2 ^ i : Nat) -- 2^i as a field element
    FFTerm.add acc (.mul (.const coeff) (.var bVar))
  ) (.const 0)
  let constrA := .eqZero (.sub a sumA)
  -- 5. Constraint: Construction of 'out' (The Shift)
  --    out = sum(b_i * 2^(i + bits))
  --    Crucial: We only sum bits where (i + bits) < k.
  --    Variables that would shift beyond k are dropped (truncated).
  let sumOut := bitVars.foldl (fun acc (i, bVar) =>
    if i + bits < k then
      let coeff := (2 ^ (i + bits) : Nat)
      FFTerm.add acc (.mul (.const coeff) (.var bVar))
    else
      acc -- This bit falls off the edge
  ) (.const 0)
  let constrOut := .eqZero (.sub (.var out) sumOut)
  -- 6. Combine all formulas with AND
  let allConstrs := boolConstrs ++ [constrA, constrOut]
  allConstrs.foldl (init := .true) .and



/- Symbolic execution of skip -/
def sym_exec_skip {c : ZKConfig}
    (md : CmdMetaData)
    (senv : SymEnv)
    (max_var_id : ℕ)
    : Except String (SymState c) :=
  return {
           in_senv := senv,
           out_senv := senv,
           p := [Com.skip md],
           f := .true
           max_var_id := max_var_id
         }

/- Symbolic execution of add -/
def sym_exec_add {c : ZKConfig}
    (md : CmdMetaData)
    (senv : SymEnv)
    (out : ProgVarID)
    (a1 a2 : SimpleExpr c)
    (max_var_id : ℕ)
    : Except String (SymState c) := do
  let max_var_id' := max_var_id+1
  let v1 ← eval_simple senv a1
  let v2 ← eval_simple senv a2
  let out_var := { id := max_var_id', meta_data := { orig_name := out, cmd_meta_data := md } }
  let outv : FFTerm c := .var out_var
  let senv' ← update_var senv out out_var
  let f : FFFormula c := .eqZero (.sub outv (.add v1 v2))
  return {
           in_senv := senv,
           out_senv := senv',
           p := [Com.add md out a1 a2],
           f := f,
           max_var_id := max_var_id'
        }

/- Symbolic execution of sub -/
def sym_exec_sub {c : ZKConfig}
    (md : CmdMetaData)
    (senv : SymEnv)
    (out : ProgVarID)
    (a1 a2 : SimpleExpr c)
    (max_var_id : ℕ)
    : Except String (SymState c) := do
  let max_var_id' := max_var_id+1
  let v1 ← eval_simple senv a1
  let v2 ← eval_simple senv a2
  let out_var := { id := max_var_id', meta_data := { orig_name := out, cmd_meta_data := md } }
  let outv : FFTerm c := .var out_var
  let senv' ← update_var senv out out_var
  let f : FFFormula c := .eqZero (.sub outv (.sub v1 v2))
  return {
           in_senv := senv,
           out_senv := senv',
           p := [Com.sub md out a1 a2],
           f := f,
           max_var_id := max_var_id'
         }

/- Symbolic execution of mul -/
def sym_exec_mul {c : ZKConfig}
    (md : CmdMetaData)
    (senv : SymEnv)
    (out : ProgVarID)
    (a1 a2 : SimpleExpr c)
    (max_var_id : ℕ)
    : Except String (SymState c) := do
  let max_var_id' := max_var_id+1
  let v1 ← eval_simple senv a1
  let v2 ← eval_simple senv a2
  let out_var := { id := max_var_id', meta_data := { orig_name := out, cmd_meta_data := md} }
  let outv : FFTerm c := .var out_var
  let senv' ← update_var senv out out_var
  let f : FFFormula c := .eqZero (.sub outv (.mul v1 v2))
  return {
           in_senv := senv,
           out_senv := senv',
           p := [Com.mul md out a1 a2],
           f := f,
           max_var_id := max_var_id'
         }

/- Symbolic execution of div -/
def sym_exec_div {c : ZKConfig}
    (md : CmdMetaData)
    (senv : SymEnv)
    (out : ProgVarID)
    (a1 a2 : SimpleExpr c)
    (max_var_id : ℕ)
    : Except String (SymState c) := do
  let max_var_id' := max_var_id+1
  let v1 ← eval_simple senv a1
  let v2 ← eval_simple senv a2
  let out_var := { id := max_var_id', meta_data := { orig_name := out, cmd_meta_data := md } }
  let outv : FFTerm c := .var out_var
  let senv' ← update_var senv out out_var
  let f : FFFormula c := .eqZero (.sub (.mul outv v2) v1)
  return {
           in_senv := senv,
           out_senv := senv',
           p := [Com.div md out a1 a2],
           f := f,
           max_var_id := max_var_id'
         }

/- Symbolic execution of shl -/
def sym_exec_shl {c : ZKConfig}
    (md : CmdMetaData)
    (senv : SymEnv)
    (out : ProgVarID)
    (a : SimpleExpr c)
    (bits : ℕ)
    (max_var_id : ℕ)
    : Except String (SymState c) := do
  let max_var_id' := max_var_id+1
  let a_term ← eval_simple senv a
  let out_var := { id := max_var_id', meta_data := { orig_name := out, cmd_meta_data := md } }
  let senv' ← update_var senv out out_var
  let f := genSHLFormula out_var a_term bits max_var_id'
  return {
           in_senv := senv,
           out_senv := senv',
           p := [Com.shl md out a bits],
           f := f,
           max_var_id := max_var_id'+c.k
         }

/- Symbolic execution of assign -/
def sym_exec_assign {c : ZKConfig}
    (md : CmdMetaData)
    (senv : SymEnv)
    (out : ProgVarID)
    (a1 : SimpleExpr c)
    (max_var_id : ℕ)
    : Except String (SymState c) := do
  let max_var_id' := max_var_id+1
  let v1 ← eval_simple senv a1
  let out_var := { id := max_var_id', meta_data := { orig_name := out, cmd_meta_data := md } }
  let outv : FFTerm c := .var out_var
  let senv' ← update_var senv out out_var
  let f : FFFormula c := .eqZero (.sub outv v1)
  return {
           in_senv := senv,
           out_senv := senv',
           p := [Com.assign md out a1],
           f := f,
           max_var_id := max_var_id'
         }


/- Symbolic execution of programs
-/
def sym_exec {c : ZKConfig}
    (senv : SymEnv)
    (p : Prog c)
    (max_var_id : ℕ)
    : Except String (SymState c) := do
  match p with
  | [] => return {
                    in_senv := senv,
                    out_senv := senv,
                    p := [],
                    f := .true,
                    max_var_id := max_var_id
                }
  | cmd::cmds =>
    let s ← match cmd with -- simple command are handled by calling their respective functions
            | Com.skip md =>
              sym_exec_skip md senv max_var_id
            | Com.add md out a1 a2 =>
              sym_exec_add md senv out a1 a2 max_var_id
            | Com.sub md out a1 a2 =>
              sym_exec_sub md senv out a1 a2 max_var_id
            | Com.mul md out a1 a2 =>
              sym_exec_mul md senv out a1 a2 max_var_id
            | Com.div md out a1 a2 =>
              sym_exec_div md senv out a1 a2 max_var_id
            | Com.shl md out a bits =>
              sym_exec_shl md senv out a bits max_var_id
            | Com.assign md out a1 =>
              sym_exec_assign md senv out a1 max_var_id
            | Com.ifst md cond tb eb =>  -- if-statement needs special handling
              let ts ← sym_exec senv tb max_var_id -- Symbolic execution of the 'then' branch
              let es ← sym_exec senv eb max_var_id -- Symbolic execution of the 'else' branch
              let cvar ← get_var senv cond -- Get the condition variable
              let condF := .eqZero (.var cvar) -- condF is true when cond == 0
              -- add phi formulas to make both branches consistent
              let max_var_id' := Nat.max ts.max_var_id es.max_var_id
              let (sout',ft',fe', max_var_id'') ←
                  add_phi_formula md ts.out_senv es.out_senv ts.f es.f max_var_id'
              -- Combine the formulas
              let f := (.or (.and (.not condF) ft') (.and condF fe'))
              pure {
                       in_senv := senv,
                       out_senv := sout',
                       p := [cmd],
                       f := f,
                       max_var_id := max_var_id''
                   }
    let s' ← sym_exec s.out_senv cmds s.max_var_id-- Symbolic execution of the rest of the program
    let f := .and s.f s'.f -- Combine the formulas
    return {
             in_senv := s.in_senv,
             out_senv := s'.out_senv,
             p := p,
             f := f,
             max_var_id := s'.max_var_id
          }


/- Symbolically run a program -/
def sym_exec_prog {c : ZKConfig}
    (prog : Prog c)
    : Except String (SymState c) :=
  do
  let prog_vars_set := collect_prog_vars prog
  let prog_vars := prog_vars_set.toList
  let (senv,max_var_id) :=
     prog_vars.foldl (init := (emptySEnv,0))
                     (fun acc var =>
                          (set_var acc.1 var
                                   {
                                     id := acc.2+1,
                                     meta_data := { orig_name := var, cmd_meta_data := default }
                                   }, acc.2 + 1))
  sym_exec senv prog max_var_id


/-
  let indices := List.range k
  -- 2. Generate the fresh variables for the bits of 'a'
  --    We map index 'i' to variable with ID 'nextId + i'
  let bitVars : List (ℕ × FFVar) := indices.map (fun i =>
    (i, {
          id := max_var_id + 1 + i, -- max_var_id is the last used ID, start from next one
          meta_data := { orig_name := s!"bit_{i}", cmd_meta_data := default }
        })
  )


-/



end Llzk.SymEx.BigStep
