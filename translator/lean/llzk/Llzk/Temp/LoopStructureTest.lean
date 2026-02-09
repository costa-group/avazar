/- This file includes a proof of concept for a loop unrolling
   strategy. In particular that we can prove termination of an
   interpreter and corresponding proofs.
-/
inductive Com where
  | skip : Com
  | cond (t e : List Com) : Com
  | loope (start rep : Nat ) (body: List Com) : Com
  | loop (start rep : Nat ) (body: List Com) : Com

mutual
def num_of_loope_p (p : List Com) : Nat :=
  match p with
   | [] => 0
   | c::cs =>
      num_of_loope_cmd c + num_of_loope_p cs
def num_of_loope_cmd (c : Com) : Nat :=
   match c with
   | Com.skip => 0
   | Com.cond t e => num_of_loope_p t + num_of_loope_p e
   | Com.loope _ _ body => 1+num_of_loope_p body
   | Com.loop _ _ body => num_of_loope_p body
end


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
   | Com.skip => 1
   | Com.cond t e => 1 + size_of_prog t + size_of_prog e
   | Com.loope _ _ body => 1 + size_of_prog body
   | Com.loop _ rep body => rep*(1+size_of_prog body)
end

theorem num_of_loope_p_cons_1 (c : Com) (cs : List Com) (H: num_of_loope_cmd c = 0) : num_of_loope_p (c :: cs) = num_of_loope_p cs := by
  simp only [num_of_loope_p]
  simp only [H]
  grind

theorem num_of_loope_p_cons_2 (c : Com) (cs : List Com) (H: num_of_loope_p cs = 0) : num_of_loope_p (c :: cs) = num_of_loope_cmd c := by
  simp only [num_of_loope_p]
  grind



def const_eval (a : Nat) : Nat := a

/- This follows the same structure as the interpreter, but instead of executing
   commands, it counts the number of commands in a program. This is
   used to show that we can prove termination.
-/
mutual
def count (p : List Com) : Nat :=
  match p with
  | [] => 1
  | c::cs =>
    count_cmd c + count cs
termination_by (num_of_loope_p p, size_of_prog p)
decreasing_by
  · have h1 : num_of_loope_cmd c ≤ num_of_loope_cmd c + num_of_loope_p cs := by
      grind
    rcases Nat.lt_or_eq_of_le h1 with h_less | h_equal
    · simp only [num_of_loope_p]
      apply Prod.Lex.left
      exact h_less
    · simp only [num_of_loope_p]
      rw [← h_equal]
      apply Prod.Lex.right
      simp only [size_of_prog]
      grind
  · have h1 : num_of_loope_p cs ≤ num_of_loope_cmd c + num_of_loope_p cs := by
      grind
    rcases Nat.lt_or_eq_of_le h1 with h_less | h_equal
    · simp only [num_of_loope_p]
      apply Prod.Lex.left
      exact h_less
    · simp only [num_of_loope_p]
      rw [← h_equal]
      apply Prod.Lex.right
      simp only [size_of_prog]
      grind

def count_cmd (c : Com) : Nat :=
  match c with
  | Com.skip => 1
  | Com.cond t e => 1 + count t + count e
  | Com.loope start rep body =>
    let start' := const_eval start
    let rep' := const_eval rep
    count_cmd (Com.loop start' rep' body)
  | Com.loop start (rep+1) body =>
      1+count body + count_cmd (Com.loop (start+1) rep body)
  | Com.loop _ 0 _ =>
      1
termination_by (num_of_loope_cmd c, size_of_cmd c)
decreasing_by
  · have h1 : num_of_loope_p t ≤ num_of_loope_p t +  num_of_loope_p e := by grind
    simp only [num_of_loope_cmd]
    rcases Nat.lt_or_eq_of_le h1 with h_less | h_equal
    · apply Prod.Lex.left
      exact h_less
    · rw [← h_equal]
      apply Prod.Lex.right
      simp only [size_of_cmd]
      grind
  · have h1 : num_of_loope_p e ≤ num_of_loope_p t +  num_of_loope_p e := by grind
    simp only [num_of_loope_cmd]
    rcases Nat.lt_or_eq_of_le h1 with h_less | h_equal
    · apply Prod.Lex.left
      exact h_less
    · rw [← h_equal]
      apply Prod.Lex.right
      simp only [size_of_cmd]
      grind
  · apply Prod.Lex.left
    simp only [num_of_loope_cmd]
    grind
  · simp only [num_of_loope_cmd]
    apply Prod.Lex.right
    simp only [size_of_cmd]
    grind
  · simp only [num_of_loope_cmd]
    apply Prod.Lex.right
    simp only [size_of_cmd]
    grind
end


mutual
theorem count_nonneg (p : List Com) : count p > 0 := by
  induction p with
  | nil =>
    simp only [count]
    grind
  | cons c cs ih =>
    simp only [count]
    have h1 : count_cmd c > 0 := count_cmd_nonneg c
    grind

theorem count_cmd_nonneg (c : Com) : count_cmd c > 0 := by
  cases c with
  | skip =>
    simp only [count_cmd]
    grind
  | cond t e =>
    simp only [count_cmd]
    grind
  | loope start rep body =>
    simp only [count_cmd]
    cases (const_eval rep) with
    | zero =>
      simp only [count_cmd]
      grind
    | succ rep' =>
      simp only [count_cmd]
      grind
  | loop start rep body =>
    cases rep with
    | zero =>
      simp only [count_cmd]
      grind
    | succ rep' =>
      simp only [count_cmd]
      grind
end
