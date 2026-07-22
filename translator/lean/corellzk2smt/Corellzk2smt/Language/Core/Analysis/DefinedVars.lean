import Corellzk2smt.Basic
import Corellzk2smt.Language.Core.Syntax.AST

/- Collects every variable name that is ever an assignment target within a function's body.

   This is used to build a fully-defined initial environment for a function call: every
   variable is defaulted to 0 before execution starts, so a variable assigned along one branch
   of a conditional but not the other is still always defined afterwards (rather than being
   "maybe defined", which would force environments to have different domains along different
   branches of the same function). See `evalFunCall` in `Semantics/BigStep.lean`.

   The language isn't strongly typed, so no attempt is made here to track whether a variable
   is eventually used as an array or a finite-field value -- everything defaults to a scalar
   0, and `new_array`/`copy_array` overwrite that default the first time the variable is
   actually used as an array.
-/

namespace Corellzk2smt.Language.Core.Analysis.DefinedVars

open Corellzk2smt.Language.Core.Syntax.AST

mutual

def definedVarsCom {c : ZKConfig} (vars : VarIDSet) (cmd : Com c) : VarIDSet :=
  match cmd with
  | .assign id _        => vars.insert id
  | .if_stmt _ tb eb     => definedVarsCmds (definedVarsCmds vars tb) eb
  | .loop_exp _ body     => definedVarsCmds vars body
  | .loop _ body         => definedVarsCmds vars body
  | .new_array id _      => vars.insert id
  | .read_array id _ _   => vars.insert id
  | .write_array _ _ _   => vars -- mutates an existing array, doesn't define a new variable
  | .copy_array dst _    => vars.insert dst
  | .func_call outs _ _  => outs.foldl (fun acc id => acc.insert id) vars

def definedVarsCmds {c : ZKConfig} (vars : VarIDSet) (cmds : List (ComWithMD c)) : VarIDSet :=
  match cmds with
  | [] => vars
  | i :: rest =>
    match i with
    | .mk _ cmd => definedVarsCmds (definedVarsCom vars cmd) rest

end

/-- `List.foldl (fun acc id => acc.insert id) vars outs` only ever adds to `vars` -- never drops
    a member. Generic helper for `definedVarsCom`'s `.func_call` case. -/
theorem foldl_insert_var_mono (outs : List VarID) (vars : VarIDSet) (id : VarID)
    (hid : id ∈ vars) : id ∈ outs.foldl (fun acc id' => acc.insert id') vars := by
  induction outs generalizing vars with
  | nil => simpa using hid
  | cons id0 rest ih =>
      simp only [List.foldl_cons]
      exact ih (vars.insert id0) (Std.TreeSet.mem_insert.mpr (Or.inr hid))

/-- `List.foldl (fun acc id => acc.insert id) vars outs` is monotone in its initial set: growing
    `vars1` to `vars2` grows the result the same way. Generic helper for `definedVarsCom`'s
    `.func_call` case. -/
theorem foldl_insert_var_subset_mono (outs : List VarID) (vars1 vars2 : VarIDSet)
    (hsub : ∀ id, id ∈ vars1 → id ∈ vars2) :
    ∀ id, id ∈ outs.foldl (fun acc id' => acc.insert id') vars1 →
      id ∈ outs.foldl (fun acc id' => acc.insert id') vars2 := by
  induction outs generalizing vars1 vars2 with
  | nil => simpa using hsub
  | cons id0 rest ih =>
      simp only [List.foldl_cons]
      exact ih (vars1.insert id0) (vars2.insert id0)
        (fun id hid => Std.TreeSet.mem_insert.mpr
          ((Std.TreeSet.mem_insert.mp hid).imp (fun h => h) (fun h => hsub id h)))

/-- Every element of `outs` itself ends up in `List.foldl (fun acc id => acc.insert id) vars
    outs`, regardless of the starting `vars` -- the dual of `foldl_insert_var_mono` (which shows
    pre-existing members survive). Generic helper for `definedVarsCom`'s `.func_call` case. -/
theorem mem_foldl_insert_var (outs : List VarID) (vars : VarIDSet) (id : VarID)
    (hmem : id ∈ outs) : id ∈ outs.foldl (fun acc id' => acc.insert id') vars := by
  induction outs generalizing vars with
  | nil => exact absurd hmem List.not_mem_nil
  | cons id0 rest ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hmem with heq | hmem'
      · rw [heq]
        exact foldl_insert_var_mono rest (vars.insert id0) id0 Std.TreeSet.mem_insert_self
      · exact ih (vars.insert id0) hmem'

mutual

/-- `definedVarsCom`/`definedVarsCmds` only ever add to their accumulator, never drop a member --
    needed so that, at each recursive step of a `seCmds_domain_of_defined`-style induction, the
    *sub*-command's own defined-vars precondition (built from a *bigger* accumulator, e.g.
    `definedVarsCmds vars tb` when processing `eb`) can be related back to the *original*
    accumulator (`vars`) it was built from. -/
theorem definedVarsCom_mono {c : ZKConfig} (cmd : Com c) (vars : VarIDSet) (id : VarID)
    (hid : id ∈ vars) : id ∈ definedVarsCom vars cmd := by
  cases cmd with
  | assign id' _ => simp only [definedVarsCom]; exact Std.TreeSet.mem_insert.mpr (Or.inr hid)
  | if_stmt _ tb eb =>
      simp only [definedVarsCom]
      exact definedVarsCmds_mono eb (definedVarsCmds vars tb) id
        (definedVarsCmds_mono tb vars id hid)
  | loop_exp _ body => simp only [definedVarsCom]; exact definedVarsCmds_mono body vars id hid
  | loop _ body => simp only [definedVarsCom]; exact definedVarsCmds_mono body vars id hid
  | new_array id' _ => simp only [definedVarsCom]; exact Std.TreeSet.mem_insert.mpr (Or.inr hid)
  | read_array id' _ _ => simp only [definedVarsCom]; exact Std.TreeSet.mem_insert.mpr (Or.inr hid)
  | write_array _ _ _ => simp only [definedVarsCom]; exact hid
  | copy_array dst _ => simp only [definedVarsCom]; exact Std.TreeSet.mem_insert.mpr (Or.inr hid)
  | func_call outs _ _ =>
      simp only [definedVarsCom]
      exact foldl_insert_var_mono outs vars id hid

theorem definedVarsCmds_mono {c : ZKConfig} (cmds : List (ComWithMD c)) (vars : VarIDSet)
    (id : VarID) (hid : id ∈ vars) : id ∈ definedVarsCmds vars cmds := by
  cases cmds with
  | nil => simpa only [definedVarsCmds] using hid
  | cons i rest =>
      cases i with
      | mk _ cmd =>
          simp only [definedVarsCmds]
          exact definedVarsCmds_mono rest (definedVarsCom vars cmd) id
            (definedVarsCom_mono cmd vars id hid)

end

mutual

/-- `definedVarsCom`/`definedVarsCmds` are monotone in their initial accumulator: growing `vars1`
    to `vars2` (as sets) grows the result the same way. Lets a `seCmds_domain_of_defined`-style
    induction lift a defined-vars precondition proved against a smaller accumulator up to a
    bigger one it's actually needed against (e.g. `definedVarsCmds vars tb`'s membership, via
    `definedVarsCom_mono`, into `eb`'s own precondition over `definedVarsCmds (definedVarsCmds
    vars tb) eb`). -/
theorem definedVarsCom_subset_mono {c : ZKConfig} (cmd : Com c) (vars1 vars2 : VarIDSet)
    (hsub : ∀ id, id ∈ vars1 → id ∈ vars2) :
    ∀ id, id ∈ definedVarsCom vars1 cmd → id ∈ definedVarsCom vars2 cmd := by
  cases cmd with
  | assign id' _ =>
      intro id hid
      simp only [definedVarsCom] at hid ⊢
      exact Std.TreeSet.mem_insert.mpr
        ((Std.TreeSet.mem_insert.mp hid).imp (fun h => h) (fun h => hsub id h))
  | if_stmt _ tb eb =>
      intro id hid
      simp only [definedVarsCom] at hid ⊢
      exact definedVarsCmds_subset_mono eb (definedVarsCmds vars1 tb) (definedVarsCmds vars2 tb)
        (definedVarsCmds_subset_mono tb vars1 vars2 hsub) id hid
  | loop_exp _ body =>
      intro id hid
      simp only [definedVarsCom] at hid ⊢
      exact definedVarsCmds_subset_mono body vars1 vars2 hsub id hid
  | loop _ body =>
      intro id hid
      simp only [definedVarsCom] at hid ⊢
      exact definedVarsCmds_subset_mono body vars1 vars2 hsub id hid
  | new_array id' _ =>
      intro id hid
      simp only [definedVarsCom] at hid ⊢
      exact Std.TreeSet.mem_insert.mpr
        ((Std.TreeSet.mem_insert.mp hid).imp (fun h => h) (fun h => hsub id h))
  | read_array id' _ _ =>
      intro id hid
      simp only [definedVarsCom] at hid ⊢
      exact Std.TreeSet.mem_insert.mpr
        ((Std.TreeSet.mem_insert.mp hid).imp (fun h => h) (fun h => hsub id h))
  | write_array _ _ _ =>
      intro id hid
      simp only [definedVarsCom] at hid ⊢
      exact hsub id hid
  | copy_array dst _ =>
      intro id hid
      simp only [definedVarsCom] at hid ⊢
      exact Std.TreeSet.mem_insert.mpr
        ((Std.TreeSet.mem_insert.mp hid).imp (fun h => h) (fun h => hsub id h))
  | func_call outs _ _ =>
      intro id hid
      simp only [definedVarsCom] at hid ⊢
      exact foldl_insert_var_subset_mono outs vars1 vars2 hsub id hid

theorem definedVarsCmds_subset_mono {c : ZKConfig} (cmds : List (ComWithMD c))
    (vars1 vars2 : VarIDSet) (hsub : ∀ id, id ∈ vars1 → id ∈ vars2) :
    ∀ id, id ∈ definedVarsCmds vars1 cmds → id ∈ definedVarsCmds vars2 cmds := by
  cases cmds with
  | nil =>
      intro id hid
      simpa only [definedVarsCmds] using hsub id hid
  | cons i rest =>
      cases i with
      | mk _ cmd =>
          intro id hid
          simp only [definedVarsCmds] at hid ⊢
          exact definedVarsCmds_subset_mono rest (definedVarsCom vars1 cmd)
            (definedVarsCom vars2 cmd) (definedVarsCom_subset_mono cmd vars1 vars2 hsub) id hid

end

/-- Every variable a function ever assigns, including its parameters. -/
def definedVarsOfFunc {c : ZKConfig} (f : Func c) : VarIDSet :=
  match f with
  | .mk _name params _rets body =>
    let initVars := params.foldl (fun acc p => acc.insert p.name) emptyVarIDSet
    definedVarsCmds initVars body

end Corellzk2smt.Language.Core.Analysis.DefinedVars
