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
