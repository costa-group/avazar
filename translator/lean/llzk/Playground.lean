import Llzk.Basic
import Mathlib.Tactic.Linarith
import Llzk.SymEx.Runner
import Llzk.Language.Core.Parser
import Llzk.Language.Core.Semantics.Runner

open Llzk.SymEx.Runner
open Llzk.Language.Core.Parser
open Llzk.Language.Core.Semantics.Runner
open Llzk.Language.Core.Semantics.BigStep


def p1 := "
# this is a comment
x := 1
if (z) {
  w := 1
  if (w) {
    x := 1
  } else {
    z := 2
  }
  y := x+4
} else {
  w := x / 6
}
x := 2 * w
"

def p2 := "
w := x + w
"

#eval @parse F11 p1

#eval (do
  let stdout ← IO.getStdout
  parse_test p1 stdout : IO Unit)

#eval (@run goldilocks64 p1)

#eval (@run goldilocks64 p2)

#eval (@run_from_file goldilocks64 "test_progs/p1.llzk")

#eval (do
  let outHandle ← IO.getStdout
  @run_sym_exec_from_file F11 "test_progs/p1.llzk" outHandle false
  : IO Unit)

#eval (do
  let outHandle ← IO.getStdout
  @run_sym_exec F11 p2 outHandle false
  : IO Unit)



-- Comparison Tests
def to_signed {c : ZKConfig} (x : FF c) : Int :=
  let midpoint := (c.p - 1) / 2
  if x.val <= midpoint then
    (x.val : Int)        -- 0, 1, ... midpoint
  else
    (x.val : Int) - c.p    -- -1, -2, ... -midpoint


def signed_lt {c : ZKConfig} (x y : FF c) : Bool :=
  to_signed x < to_signed y

def unsigned_lt {c : ZKConfig} (x y : FF c) : Bool :=
   x.val < y.val



-- Testing signed and unsigned comparisons

-- Example with p = 11 (Midpoint q = 5)
-- Order: 6(-5), 7(-4), 8(-3), 9(-2), 10(-1), 0, 1, 2, 3, 4, 5
#eval @signed_lt F11 (10 : ZMod 11) (0 : ZMod 11)
#eval @unsigned_lt F11 (10 : ZMod 11) (0 : ZMod 11)

#eval @signed_lt F11 (6 : ZMod 11) (10 : ZMod 11)
#eval @unsigned_lt F11 (6 : ZMod 11) (10 : ZMod 11)

#eval @signed_lt F11 (0 : ZMod 11) (6 : ZMod 11)
#eval @unsigned_lt F11 (0 : ZMod 11) (6 : ZMod 11)



inductive Com  where
  | skip : Com
  | cond  (t e : List Com) : Com
  | loop (lb ub : Nat ) (body: List Com) : Com

mutual
def size_of_p (p : List Com) : Nat :=
  match p with
   | [] => 0
   | c::cs =>
              1 + size_of_cmd c + size_of_p cs

def size_of_cmd (c: Com) : Nat :=
  match c with
   | Com.skip => 1
   | Com.cond t e => 1 + size_of_p t + size_of_p e
   | Com.loop lb ub body =>
     1 + ub*(1+(size_of_p body))
end

def count (p : List Com) : Nat :=
  match p with
   | [] => 0
   | c::cs =>
   let x := match c with
            | Com.skip => 0
            | Com.cond t e => 0 + count t + count e
            | Com.loop lb ub body =>
              if ub > 0 then
                0 + count body + count [(Com.loop (lb+1) (ub-1) body)]
              else
                0
    x + count cs
termination_by
  size_of_p p
decreasing_by
  · simp only [size_of_p, size_of_cmd]
    grind
  · simp only [size_of_p, size_of_cmd]
    grind
  · simp only [size_of_p, size_of_cmd]
    rename_i h_ub
    rw [← Nat.sub_add_cancel h_ub]
    grind
  · simp only [size_of_p, size_of_cmd]
    rename_i h_ub
    rw [← Nat.sub_add_cancel h_ub]
    grind
  · simp [size_of_p]

theorem bla (p : List Com) : count p = 0 := by
  cases p with
  | nil => simp [count]
  | cons c cs =>
    cases c with
    | skip =>
      simp only [count]
      have ih : count cs = 0 := bla cs
      rw [ih]
    | cond t e =>
      simp only[count]
      have ih_t : count t = 0 := bla t
      have ih_e : count e = 0 := bla e
      have ih : count cs = 0 := bla cs
      rw [ih, ih_t, ih_e ]
    | loop lb ub body =>
      rw [count]
      refine if h_ub : ub > 0 then ?_ else ?_
      · simp only [h_ub]
        have ih_body : count body = 0 := bla body
        have ih_loop : count [(Com.loop (lb+1) (ub-1) body)] = 0
             := bla [(Com.loop (lb+1) (ub-1) body)]
        have ih : count cs = 0 := bla cs
        simp [ih, ih_body, ih_loop]
      · simp only [h_ub]
        have ih : count cs = 0 := bla cs
        simp [ih]
termination_by
  size_of_p p
decreasing_by
  · simp only [size_of_p, size_of_cmd]
    grind
  · simp only [size_of_p, size_of_cmd]
    grind
  · simp only [size_of_p, size_of_cmd]
    grind
  · simp only [size_of_p, size_of_cmd]
    grind
  · simp only [size_of_p, size_of_cmd]
    rw [← Nat.sub_add_cancel h_ub]
    grind
  · simp only [size_of_p, size_of_cmd]
    rw [← Nat.sub_add_cancel h_ub]
    grind
  · simp only [size_of_p]
    grind
  · simp only [size_of_p]
    grind
