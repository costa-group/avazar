/- This file includes a proof of concept for a loop unrolling
   strategy. In particular that we can prove termination of an
   interpreter and corresponding proofs.
-/
inductive Com where
  | skip : Com
  | cond (t e : List Com) : Com
  | loop (start rep : Nat ) (body: List Com) : Com

/- Size of a program, which is used for proving termination
   of the interpreter and corresponding proofs.
-/
mutual
def size_of_prog (p : List Com) : Nat :=
  match p with
   | [] => 0
   | c::cs => 1 + size_of_cmd c + size_of_prog cs

def size_of_cmd (c: Com) : Nat :=
  match c with
   | Com.skip => 0
   | Com.cond t e => size_of_prog t + size_of_prog e
   | Com.loop _ rep body => rep*(1+(size_of_prog body))
end

/- This follows the same structure as the interpreter, but instead of executing
   commands, it counts the number of commands in a program. This is
   used to show that we can prove termination.
-/
def count (p : List Com) : Nat :=
  match p with
   | [] => 0
   | c::cs =>
   let x := match c with
            | Com.skip => 0
            | Com.cond t e => 0 + count t + count e
            | Com.loop start rep body =>
              if rep > 0 then
                0 + count body + count [(Com.loop (start+1) (rep-1) body)]
              else
                0
    x + count cs
termination_by
  size_of_prog p
decreasing_by
  · simp only [size_of_prog, size_of_cmd]
    grind
  · simp only [size_of_prog, size_of_cmd]
    grind
  · simp only [size_of_prog, size_of_cmd]
    rename_i h_rep
    rw [← Nat.sub_add_cancel h_rep]
    grind
  · simp only [size_of_prog, size_of_cmd]
    rename_i h_rep
    rw [← Nat.sub_add_cancel h_rep]
    grind
  · simp [size_of_prog]
    grind

/- A simple test to show that we can prove inductive properties
    about the count function, which is used to show that we can
    prove termination of inductive principles, etc.
-/
theorem count_is_zero (p : List Com) : count p = 0 := by
  cases p with
  | nil => simp [count]
  | cons c cs =>
    cases c with
    | skip =>
      simp only [count]
      have ih : count cs = 0 := count_is_zero cs
      rw [ih]
    | cond t e =>
      simp only[count]
      have ih_t : count t = 0 := count_is_zero t
      have ih_e : count e = 0 := count_is_zero e
      have ih : count cs = 0 := count_is_zero cs
      rw [ih, ih_t, ih_e ]
    | loop start rep body =>
      have ih : count cs = 0 := count_is_zero cs
      rw [count]
      by_cases h_rep : rep > 0
      · simp only [h_rep]
        simp
        have ih_body : count body = 0 := count_is_zero body
        have ih_loop : count [(Com.loop (start+1) (rep-1) body)] = 0
             := count_is_zero [(Com.loop (start+1) (rep-1) body)]
        simp [ih, ih_body, ih_loop]
      · simp only [h_rep]
        simp
        simp [ih]
termination_by
  size_of_prog p
decreasing_by
  · simp only [size_of_prog, size_of_cmd]
    grind
  · simp only [size_of_prog, size_of_cmd]
    grind
  · simp only [size_of_prog, size_of_cmd]
    grind
  · simp only [size_of_prog, size_of_cmd]
    grind
  · simp only [size_of_prog, size_of_cmd]
    grind
  · simp only [size_of_prog, size_of_cmd]
    rw [← Nat.sub_add_cancel h_rep]
    grind
  · simp only [size_of_prog, size_of_cmd]
    rw [← Nat.sub_add_cancel h_rep]
    grind
