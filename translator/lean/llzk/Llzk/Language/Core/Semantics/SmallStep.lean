import Llzk.Basic
import Llzk.Language.Core.Syntax
import Llzk.Language.Core.Semantics.Basic

namespace Llzk.Language.Core.Semantics.SmallStep

open Llzk.Language.Core


/- Configuration: The remaining program (List of commands) and the current Environment
-/
abbrev Config (c : ZKConfig) := Prog c × Env c

/- Executable Small-Step Semantics

   Returns:
    - Except.error: Runtime error (e.g., variable not found, empty program, etc.)
    - Except.ok (some (p', s')): The system took one step from (p,s) to state (p', s')

   Note: it uses the same exec_* functions, as in the big step semantics,defined
         above for each command
-/
def step {c : ZKConfig} (cfg : Config c) : Except String (Config c) := do
  let (prog, env) := cfg
  match prog with
  | [] => throw "Cannot make a step within an empty program"
  | cmd :: rest =>
      match cmd with
      | Com.skip _ =>
          let env' ← exec_skip env
          return (rest, env')
      | Com.add _ out a1 a2 =>
          let env' ← exec_add env out a1 a2
          return (rest, env')
      | Com.sub _ out a1 a2 =>
          let env' ← exec_sub env out a1 a2
          return (rest, env')
      | Com.mul _ out a1 a2 =>
          let env' ← exec_mul env out a1 a2
          return (rest, env')
      | Com.div _ out a1 a2 =>
          let env' ← exec_div env out a1 a2
          return (rest, env')
      | Com.shl _ out a bits =>
          let env' ← exec_shl env out a bits
          return (rest, env')
      | Com.assign _ out a =>
          let env' ← exec_assign env out a
          return (rest, env')
      | Com.ifst _ cond tb eb =>
          let condVal ← get_var env cond
          if condVal != 0 then
            -- Prepend the True Block (tb) to the remaining code (rest)
            return (tb ++ rest, env)
          else
            -- Prepend the Else Block (eb) to the remaining code (rest)
            return (eb ++ rest, env)


/- Run the small-step semantics until completion or until fuel runs out.

   - `fuel`: Maximum number of steps allowed (prevents infinite loops).
   - `cfg`: The current configuration (Program + Environment).
-/
def exec_prog {c : ZKConfig} (fuel : Nat) (cfg : Config c) : Except String (Config c) :=
  match fuel with
  | 0 => Except.ok cfg -- Out of fuel, return current config
  | fuel' + 1 =>
      match step cfg with
      | Except.error msg => Except.error msg
      | Except.ok cfg' => exec_prog fuel' cfg'


/- A convenience wrapper to initialize and run a program using exec_prog.
-/
def run_prog {c : ZKConfig}
    (fuel : Nat) (p : Prog c) (f : Oracle c) : Except String (Config c) := do
  let vars_set := collect_prog_vars p
  let vars := vars_set.toList
  let env := vars.foldl (init := (emptyEnv c)) (fun env name => set_var env name (f name))
  exec_prog fuel (p, env)


/- Computes the size of a program. Needed to prove termination
   of `exec_prog_full` bellow -/
mutual
def sizeOfProg {c : ZKConfig} (p : Prog c) : Nat :=
  match p with
  | [] => 0
  | cmd :: cmds =>
    (sizeOfCmd cmd) + (sizeOfProg cmds)

def sizeOfCmd {c : ZKConfig} (cmd : Com c) : Nat :=
  match cmd with
  | Com.skip _ => 1
  | Com.add _ _ _ _ => 1
  | Com.sub _ _ _ _ => 1
  | Com.mul _ _ _ _ => 1
  | Com.div _ _ _ _ => 1
  | Com.shl _ _ _ _ => 1
  | Com.assign _ _ _ => 1
  | Com.ifst _ _ tb eb =>
      1 + sizeOfProg tb + sizeOfProg eb
end -- mutual

/- Computes the size of a configuration. Needed to prove termination
   of `exec_prog_full` bellow -/
def sizeOfConfig {c : ZKConfig} (cfg : Config c) : Nat :=
  let (prog, _) := cfg
  sizeOfProg prog

/- A helper lemma about size of programs -/
theorem sizeOfProg_app {c : ZKConfig} (p1 p2 : Prog c) :
  sizeOfProg (p1 ++ p2) = sizeOfProg p1 + sizeOfProg p2 := by
  induction p1 with
  | nil =>
      simp [sizeOfProg]
  | cons cmd cmds ih =>
      dsimp [sizeOfProg]
      rewrite [ih]
      simp [Nat.add_assoc]
-- qed

/-
 A tactic to solve each case of the `step_dec` theorem below

   exec:   The execution function call (e.g., exec_skip s)
   h:      The hypothesis name (e.g., h)
-/
local macro "solve_step_dec_case"
  exec:term ","  h:ident : tactic =>
  `(tactic| (
            dsimp at $h:ident
            dsimp [sizeOfProg,sizeOfCmd]
            match h_exec: $exec with
            | Except.error msg =>
              rw [h_exec] at $h:ident
              simp only [bind_pure_comp, Except.map_error, reduceCtorEq] at $h:ident
            | Except.ok env'' =>
              simp [*] at $h:ident
              obtain ⟨h_rest,h_env''⟩ := $h:ident
              rewrite [h_rest]
              linarith
  ))

/- A helper lemma stating that the `step` decreases the size of
   the configuration -/
theorem step_dec {c : ZKConfig} (cfg cfg' : Config c) :
    step cfg = Except.ok cfg' → sizeOfProg cfg'.1 < sizeOfProg cfg.1 := by
    intro h
    obtain ⟨prog, env⟩ := cfg
    obtain ⟨prog', env'⟩ := cfg'
    simp only -- remove .1
    cases prog with
    | nil =>
        -- Cannot step from empty program
        dsimp [step] at h
        contradiction
    | cons cmd rest =>
        dsimp [step] at h
        cases cmd with
        | skip md =>
            solve_step_dec_case exec_skip env, h
        | add md out a1 a2 =>
            solve_step_dec_case exec_add env out a1 a2, h
        | sub md out a1 a2 =>
            solve_step_dec_case exec_sub env out a1 a2, h
        | mul md out a1 a2 =>
            solve_step_dec_case exec_mul env out a1 a2, h
        | div md out a1 a2 =>
            solve_step_dec_case exec_div env out a1 a2, h
        | shl md out a bits =>
            solve_step_dec_case exec_shl env out a bits, h
        | assign md out a =>
            solve_step_dec_case exec_assign env out a, h
        | ifst md cond tb eb =>
            dsimp at h
            match h_exec: get_var env cond with
            | Except.error msg =>
              rw [h_exec] at h
              contradiction
            | Except.ok v =>
              simp only [sizeOfProg,sizeOfCmd]
              rw [h_exec] at h
              dsimp [Bind.bind, Except.bind] at h
              by_cases h_cond: v ≠ 0
              ·  -- True branch
                simp only [bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte, h_cond] at h
                dsimp [pure, Except.pure] at h
                injection h with h
                injection h with h_rest h_env'
                rewrite [← h_rest]
                rw [sizeOfProg_app]
                linarith
              ·  -- False branch
                simp only [bne_iff_ne, ↓reduceIte, h_cond] at h
                dsimp [pure, Except.pure] at h
                injection h with h
                injection h with h_rest h_env'
                rewrite [← h_rest]
                rw [sizeOfProg_app]
                linarith
-- qed


/- This one executes the program till the end. It is not limited
   by fuel.
-/
def exec_prog_full {c : ZKConfig} (cfg : Config c) : Except String (Config c) :=
  -- We use 'match h : ...' to explicitly name the hypothesis 'h'
  match h : step cfg with
  | Except.error e => Except.error e
  | Except.ok cfg' =>
      let (prog', env') := cfg'
      match prog' with
      | [] => Except.ok cfg'
      | _  => exec_prog_full cfg'
termination_by sizeOfConfig cfg
decreasing_by
  apply step_dec
  assumption


/- A convenience wrapper to initialize and run a program using exec_prog_full.
-/
def run_prog_full {c : ZKConfig}
    (p : Prog c) (f : Oracle c) : Except String (Config c) := do
  let vars_set := collect_prog_vars p
  let vars := vars_set.toList
  let env := vars.foldl (init := (emptyEnv c)) (fun env name => set_var env name (f name))
  exec_prog_full (p, env)



/- Inductive Small-Step Semantics Relation

   `Step (p, s) (p', s')` means that configuration `(p, s)` transitions
   to `(p', s')` in one step.
-/
inductive Step {c : ZKConfig} : Config c → Config c → Prop where
  | skip {md s s' p} :
      exec_skip s = Except.ok s' →
      Step ((Com.skip md) :: p, s) (p, s')
  | add {md out a1 a2 s p s'} :
      exec_add s out a1 a2 = Except.ok s' →
      Step ((Com.add md out a1 a2) :: p, s) (p, s')
  | sub {md out a1 a2 s p s'} :
      exec_sub s out a1 a2 = Except.ok s' →
      Step ((Com.sub md out a1 a2) :: p, s) (p, s')
  | mul {md out a1 a2 s p s'} :
      exec_mul s out a1 a2 = Except.ok s' →
      Step ((Com.mul md out a1 a2) :: p, s) (p, s')
  | div {md out a1 a2 s p s'} :
      exec_div s out a1 a2 = Except.ok s' →
      Step ((Com.div md out a1 a2) :: p, s) (p, s')
  | shl {md out a bits s p s'} :
      exec_shl s out a bits = Except.ok s' →
      Step ((Com.shl md out a bits) :: p, s) (p, s')
  | assign {md out a s p s'} :
      exec_assign s out a = Except.ok s' →
      Step ((Com.assign md out a) :: p, s) (p, s')
  | if_true {md cond tb eb s v p} :
      get_var s cond = Except.ok v →
      v ≠ 0 →
      Step ((Com.ifst md cond tb eb) :: p, s) (tb ++ p, s)
  | if_false {md cond tb eb s v p} :
      get_var s cond = Except.ok v →
      v = 0 →
      Step ((Com.ifst md cond tb eb) :: p, s) (eb ++ p, s)

/- `StepPlus` is the transitive closure of Step, i.e, `StepPlus cfg1 cfg2` means
   that `cfg1` transitions to `cfg2` in one or more steps.
-/
abbrev StepPlus {c : ZKConfig} := Relation.TransGen (@Step c)

/- `StepPlus'` is a head-recursive version of `StepPlus`. In some proofs, it is easier to work
   with head recursion (first step, then rest), rather than tail recursion (first rest,
   then last step).
-/
inductive StepPlus' {c : ZKConfig} : Config c → Config c → Prop where
  -- Base Case: 1 step (Since you want transitivity, we start at 1, not 0)
  | step {cfg1 cfg2 : Config c} :
      Step cfg1 cfg2 ->
      StepPlus' cfg1 cfg2
  -- Inductive Step: Take 1 step, then n more
  | succ {cfg1 cfg2 cfg3 : Config c} :
      Step cfg1 cfg2 →
      StepPlus' cfg2 cfg3 →
      StepPlus' cfg1 cfg3

/- In what follows we prove equivalence between `StepPlus` and `StepPlus'`. First we
   prove an auxiliary lemma to help with the main theorem.
-/
theorem StepPlus'_append {c : ZKConfig} {x y z : Config c}
  (h_plus : StepPlus' x y) (h_step : Step y z) : StepPlus' x z := by
  induction h_plus with
  | step h =>
    -- Base case: We have x -> y and y -> z.
    -- Use succ to combine them: x -> y -> z
    exact StepPlus'.succ h (StepPlus'.step h_step)
  | succ h_step_xy h_plus_yz ih =>
    -- Inductive case: x -> y -> ... -> z' and we append z' -> z.
    -- Keep the first step (x -> y) and apply IH to the rest.
    exact StepPlus'.succ h_step_xy (ih h_step)
-- qed

/- Equivalence of `StepPlus` and `StepPlus'` -/
theorem StepPlus_iff_StepPlus' {c : ZKConfig} (x y : Config c) :
  StepPlus x y ↔ StepPlus' x y := by
  constructor
  -- Direction 1: StepPlus (Standard) -> StepsPlusR (Yours)
  · intro h
    induction h with
    | single h_step =>
      -- Convert single step
      exact StepPlus'.step h_step
    | tail _ h_step ih =>
      -- Convert tail extension using our helper lemma
      exact StepPlus'_append ih h_step
  -- Direction 2: StepsPlusR (Yours) -> StepPlus (Standard)
  · intro h
    induction h with
    | step h_step =>
      -- Convert single step
      exact Relation.TransGen.single h_step
    | succ h_step _ ih =>
      -- Relation.TransGen has a lemma `head` that works exactly like `succ`
      -- head : r a b → TransGen r b c → TransGen r a c
      exact Relation.TransGen.head h_step ih


/- `StepsN n cfg1 cfg2` means `cfg1` transitions to `cfg2` in exactly `n` steps
-/
inductive StepsN {c : ZKConfig} : Nat → Config c → Config c → Prop where
  -- Base Case: 1 step (Since you want transitivity, we start at 1, not 0)
  | step {cfg : Config c} :
      StepsN 0 cfg cfg
  -- Inductive Step: Take 1 step, then n more
  | succ {n : Nat} {cfg1 cfg2 cfg3 : Config c} :
      StepsN n cfg1 cfg2 →
      Step cfg2 cfg3 →
      StepsN (n + 1) cfg1 cfg3

/- `StepsN'` is a head-recursive version of `StepsN`. In some proofs, it is easier to work
   with head recursion (first step, then rest), rather than tail recursion (first rest,
   then last step).
-/
inductive StepsN' {c : ZKConfig} : Nat → Config c → Config c → Prop where
  | step {cfg : Config c} :
      StepsN' 0 cfg cfg
  | succ {n : Nat} {cfg1 cfg2 cfg3 : Config c} :
      Step cfg1 cfg2 →
      StepsN' n cfg2 cfg3 →
      StepsN' (n + 1) cfg1 cfg3

/- In what follows we prove that `StepsN'` and `StepsN` are equivalent. First we prove
   some auxiliary lemmas to help with the main theorem.
-/
theorem StepsN'.append {c : ZKConfig} {n : Nat} {a b d : Config c}
    (h_path : StepsN' n a b) (h_last : Step b d) :
    StepsN' (n + 1) a d := by
  induction h_path generalizing d with
  | step =>
    -- Base Case: Path was 0 steps (so a = b).
    -- We are appending one step 'a -> d'.
    -- We build this using the head-recursive 'succ': (a->d) :: (d->d 0 steps)
    apply StepsN'.succ h_last StepsN'.step
  | succ h_head h_tail ih =>
    -- Inductive Step: Path is (a -> x -> ... -> b).
    -- We need to append (b -> d) to the end.
    -- IH tells us we can append (b -> d) to the tail (x -> ... -> b).
    apply StepsN'.succ h_head (ih h_last)
-- qed

theorem StepsN.prepend {c : ZKConfig} {n : Nat} {a b d : Config c}
    (h_first : Step a b) (h_path : StepsN n b d) :
    StepsN (n + 1) a d := by
  induction h_path generalizing a with
  | step =>
    -- Base Case: Path was 0 steps (so b = d).
    -- We are prepending one step 'a -> b'.
    -- We build this using the tail-recursive 'succ': (a->a 0 steps) + (a->b)
    apply StepsN.succ StepsN.step h_first
  | succ h_front h_last ih =>
    -- Inductive Step: Path is (b -> ... -> y -> d).
    -- We need to prepend (a -> b).
    -- IH says we can prepend (a -> b) to the front part (b -> ... -> y).
    apply StepsN.succ (ih h_first) h_last
-- qed

/- Equivalence of `StepsN` and `StepsN'` -/
theorem steps_N_steps_N'_equivalent {c : ZKConfig} {n : Nat} {a b : Config c} :
    StepsN n a b ↔ StepsN' n a b := by
  constructor
  -- Direction 1: Tail (StepsN) → Head (StepsN')
  case mp =>
    intro h
    induction h with
    | step =>
      exact StepsN'.step
    | succ h_front h_last ih =>
      -- We have a path 'StepsN' (ih) and a last step.
      -- Use our helper lemma to append the last step to the StepsN' path.
      exact StepsN'.append ih h_last
  -- Direction 2: Head (StepsN') → Tail (StepsN)
  case mpr =>
    intro h
    induction h with
    | step =>
      exact StepsN.step
    | succ h_first h_rest ih =>
      -- We have a first step and a path 'StepsN' (ih).
      -- Use our helper lemma to prepend the first step to the StepsN path.
      exact StepsN.prepend h_first ih
-- qed

/- The following theorem proves equivalence between `StepPlus` and `StepsN (n+1)`
-/
theorem step_plus_iff_steps_n {c : ZKConfig} {a b : Config c} :
    StepPlus a b ↔ ∃ n, StepsN (n+1) a b := by
  constructor
  -- Direction 1: StepPlus -> ∃ n, StepsN (n+1) a b
  · intro h
    dsimp only [StepPlus] at h
    induction h with
    | single h_step =>
        exists 0
        exact StepsN.succ StepsN.step h_step
    | tail ih h_step a_ih =>
        obtain ⟨n, hn⟩ := a_ih
        exists (n + 1)
        apply StepsN.succ hn h_step
  -- Direction 2: ∃ n, StepsN (n+1) a b -> StepPlus a b
  · intro h
    obtain ⟨n, hn⟩ := h
    induction n generalizing a b with
    | zero =>
        dsimp at hn
        cases hn with
        | @succ _ a cfg2 b h_rest h_step =>
            cases h_rest
            apply Relation.TransGen.single h_step
    | succ n' ih =>
        cases hn with
        | @succ _ a cfg2 b h_rest h_step =>
            have ih_applied := ih h_rest
            apply Relation.TransGen.tail ih_applied h_step
-- qed


/- A tactic to solve each case of the `step_ind_iff_step_prog` theorem below

   exec:   The execution function call (e.g., exec_skip s)
   constr: The BigStep constructor (e.g., Step.mul)
   h:      The hypothesis name (e.g., h)
-/
local macro "solve_step_exec_case"
  exec:term "," constr:ident "," h:ident : tactic =>
  `(tactic| (
            dsimp only [bind, Except.bind] at $h:ident
            match h_exec: $exec with
            | Except.error msg =>
                rw [h_exec] at $h:ident
                contradiction
            | Except.ok env' =>
                rw [h_exec] at $h:ident
                dsimp only [pure, Except.pure, Except.ok] at $h:ident
                injection $h with h_eq
                rw [← h_eq]
                exact $constr h_exec
  ))


/- Equivalence of `Step` and `step` -/
theorem step_ind_iff_step_prog {c : ZKConfig} (a b : Config c) :
    Step a b ↔ step a = Except.ok b := by
  constructor
  -- Direction 1: Step a b -> step a = Except.ok b
  · intro h
    dsimp only [step, pure, Except.pure, bind, Except.bind]
    cases h <;> simp [*]
  -- Direction 2: step a = Except.ok b -> Step a b
  · intro h
    have (prog, env) := a
    cases prog with
    | nil =>
        dsimp only [step] at h
        contradiction
    | cons cmd cmds =>
        dsimp only [step] at h
        cases cmd with
        | skip md =>
            solve_step_exec_case (exec_skip env), Step.skip, h
        | add md out a1 a2 =>
            solve_step_exec_case (exec_add env out a1 a2), Step.add, h
        | sub md out a1 a2 =>
            solve_step_exec_case (exec_sub env out a1 a2), Step.sub, h
        | mul md out a1 a2 =>
            solve_step_exec_case (exec_mul env out a1 a2), Step.mul, h
        | div md out a1 a2 =>
            solve_step_exec_case (exec_div env out a1 a2), Step.div, h
        | shl md out a bits =>
            solve_step_exec_case (exec_shl env out a bits), Step.shl, h
        | assign md out a =>
            solve_step_exec_case (exec_assign env out a), Step.assign, h
        | ifst md cond tb eb =>
            dsimp only [bind, Except.bind] at h
            cases h_cond : get_var env cond with
            | error msg =>
                rw [h_cond] at h
                contradiction
            | ok v =>
                rw [h_cond] at h
                dsimp at h
                by_cases h_cond_val : v = 0
                · -- False branch
                    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
                      Except.ok.injEq, h_cond_val] at h
                    rw [← h]
                    exact Step.if_false h_cond h_cond_val
                · -- True branch
                    simp only [bne_iff_ne, ne_eq, not_false_eq_true, ↓reduceIte, pure, Except.pure,
                      Except.ok.injEq, h_cond_val] at h
                    rw [← h]
                    exact Step.if_true h_cond h_cond_val
-- qed

/- Next we prove equivalence of `StepsN'` and `exec_prog`. We prove every direction
   separately. Note that we use `StepsN'` here because its head-recursive structure
   aligns better with the recursive structure of `exec_prog`.
-/


/- First direction: `StepsN' fuel a b` implies `exec_prog fuel a = Except.ok b`
-/
theorem steps_n'_implies_exec_prog_n {c : ZKConfig} (a b : Config c) (fuel : ℕ) :
    StepsN' fuel a b → exec_prog fuel a = Except.ok b := by
    induction fuel generalizing a b with
    | zero =>
        intro h
        cases h -- No transition is possible with 0 steps
        dsimp only [exec_prog]
    | succ fuel' ih =>
        intro h
        cases h with
        | @succ _ a cfg2 b h_step h_rest  =>
            -- Multiple steps case
            have ih_applied := ih cfg2 b h_rest
            have h_step_exec := (step_ind_iff_step_prog a cfg2).1 h_step
            dsimp only [exec_prog]
            rw [h_step_exec]
            dsimp -- this aparently simplifies the match.
            rw [ih_applied]
-- qed

/- Second direction: `exec_prog fuel a = Except.ok b` implies `StepsN' fuel a b`
-/
theorem exec_prog_n_implies_steps_n' {c : ZKConfig} (a b : Config c) (fuel : ℕ) :
    exec_prog fuel a = Except.ok b → StepsN' fuel a b := by
    induction fuel generalizing a b with
    | zero =>
        intro h
        dsimp only [exec_prog] at h
        injection h with h_eq
        rw [h_eq ]
        exact StepsN'.step
    | succ fuel' ih =>
        intro h
        dsimp only [exec_prog] at h
        cases h_step : step a with
        | error msg =>
            rw [h_step] at h
            contradiction
        | ok cfg =>
            rw [h_step] at h
            dsimp at h
            let h_step_prop := (step_ind_iff_step_prog a cfg).2 h_step
            let h_rest_prop := ih cfg b h
            exact StepsN'.succ h_step_prop h_rest_prop
-- qed

/- Equivalence of `exec_prog` and `StepsN'` -/
theorem exec_prog_n_iff_steps_n' {c : ZKConfig} (a b : Config c) (fuel : ℕ) :
    exec_prog fuel a = Except.ok b ↔ StepsN' fuel a b := by
  constructor
  · apply exec_prog_n_implies_steps_n'
  · apply steps_n'_implies_exec_prog_n
--qed

/- Equivalence of `exec_prog` and `StepsN` -/
theorem exec_prog_n_iff_steps_n {c : ZKConfig} (a b : Config c) (fuel : ℕ) :
    exec_prog fuel a = Except.ok b ↔ StepsN fuel a b := by
  rw [steps_N_steps_N'_equivalent]
  apply exec_prog_n_iff_steps_n'
-- qed

end Llzk.Language.Core.Semantics.SmallStep
