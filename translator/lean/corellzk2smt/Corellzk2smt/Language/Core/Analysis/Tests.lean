import Corellzk2smt.Basic
import Corellzk2smt.Language.Core.Syntax.AST
import Corellzk2smt.Language.Core.Analysis.Useless_commands
import Std.Data.TreeSet.Basic

/- Unit tests for `Useless_commands.lean`. Correctness is checked with
   `example ... := by rfl`/`decide` -/

namespace Corellzk2smt.Language.Core.Analysis.Tests

open Corellzk2smt.Language.Core.Syntax.AST
open Corellzk2smt.Language.Core.Analysis.Useless_commands

-- `removeUselessProg` unfolds through several layers of mutual/structural recursion
-- (liveness propagation, the loop fixed point, `Std.TreeSet` operations); checking its
-- output by `rfl` on the larger test programs needs more headroom than the default limit.
set_option maxRecDepth 4000

-- Test helpers --

/-- Builds a command with placeholder source-location metadata; only the
    liveness metadata computed by `removeUselessProg` matters for these tests. -/
private def mkCmd {c : ZKConfig} (cmd : Com c) : ComWithMD c :=
  ComWithMD.mk { src_info := { row := 0, col := 0 } } cmd

private def mkFunc {c : ZKConfig}
    (name : FName) (params rets : List Param) (body : List (ComWithMD c)) : FuncWithMD c :=
  FuncWithMD.mk { src_info := { row := 0, col := 0 } } (Func.mk name params rets body)

private def mkProg {c : ZKConfig} (funcs : List (FuncWithMD c)) : ProgWithMD c :=
  ProgWithMD.mk {} funcs

private def progFuncs {c : ZKConfig} (p : ProgWithMD c) : List (FuncWithMD c) :=
  match p with | .mk _ fs => fs

private def funcMD {c : ZKConfig} (f : FuncWithMD c) : FuncMD :=
  match f with | .mk md _ => md

/-- A metadata-free mirror of `Com`/`ComWithMD`, so tests can compare the
    *shape* of a program after `removeUselessProg` -- which commands survive,
    in what order and nesting -- without hand-reproducing the exact liveness
    metadata the analysis computes for every surviving node. -/
inductive BareCom (c : ZKConfig) where
  | assign (out : VarID) (e : Expr c)
  | if_stmt (cond : Cond c) (tb eb : List (BareCom c))
  | loop_exp (rep : SimpleExpr c) (body : List (BareCom c))
  | loop (rep : ℕ) (body : List (BareCom c))
  | new_array (out : VarID) (size : SimpleExpr c)
  | read_array (out : VarID) (arr : VarID) (idx : SimpleExpr c)
  | write_array (arr : VarID) (idx : SimpleExpr c) (value : SimpleExpr c)
  | copy_array (out : VarID) (arr : VarID)
  | func_call (outs : List VarID) (fname : FName) (args : List (SimpleExpr c))
  deriving Repr, BEq, Inhabited

mutual

private def bareOf {c : ZKConfig} (i : ComWithMD c) : BareCom c :=
  match i with
  | .mk _ cmd =>
    match cmd with
    | .assign out e => .assign out e
    | .if_stmt cond tb eb => .if_stmt cond (bareOfList tb) (bareOfList eb)
    | .loop_exp rep body => .loop_exp rep (bareOfList body)
    | .loop rep body => .loop rep (bareOfList body)
    | .new_array out size => .new_array out size
    | .read_array out arr idx => .read_array out arr idx
    | .write_array arr idx value => .write_array arr idx value
    | .copy_array out arr => .copy_array out arr
    | .func_call outs fname args => .func_call outs fname args

private def bareOfList {c : ZKConfig} (cmds : List (ComWithMD c)) : List (BareCom c) :=
  match cmds with
  | [] => []
  | i :: rest => bareOf i :: bareOfList rest

end

private def bareBody {c : ZKConfig} (f : FuncWithMD c) : List (BareCom c) :=
  bareOfList (funcWithMDBody f)

-- p4: a straight-line dead assignment
-- func main(x:ff) -> y:ff {
--   a = felt.add x 1
--   b = felt.mul x 2
--   y = a
-- }
-- `b` is computed but never used, so it must be removed.

private def p4Main : FuncWithMD F5 :=
  mkFunc "main" [⟨"x", .ff⟩] [⟨"y", .ff⟩]
    [ mkCmd (.assign "a" (.bop .add (.var "x") (.val 1)))
    , mkCmd (.assign "b" (.bop .mul (.var "x") (.val 2)))
    , mkCmd (.assign "y" (.id (.var "a")))
    ]

private def p4Prog : ProgWithMD F5 := mkProg [p4Main]

example : (progFuncs (removeUselessProg p4Prog)).map bareBody =
    [[ .assign "a" (.bop .add (.var "x") (.val 1))
     , .assign "y" (.id (.var "a")) ]] := by rfl

-- p5: calls, arrays, and if-statements bundled together
-- func helper(x:ff, y:ff) -> s:ff, p:ff {
--   s = felt.add x y
--   p = felt.mul x y
-- }
--
-- func main(x:ff, w:ff) -> result:ff {
--   dead1 = felt.mul x 99
--   call helper(x, w) to s2, p2
--   call helper(x, w) to sum, prod
--   array.new 4 deadarr
--   array.write x deadarr[0]
--   array.new 4 livearr
--   array.write w livearr[0]
--   array.read livearr[0] fromArr
--   array.copy livearr deadcopy
--   cond1 = bool.gt x 0
--   if (cond1 == 1) { junk1 = felt.add x 1 } else { junk2 = felt.add x 2 }
--   cond2 = bool.gt w 0
--   if (cond2 == 1) { junk3 = felt.mul w 3; branchval = felt.add w 1 }
--   else { junk4 = felt.mul w 4 }
--   tmp = felt.add sum branchval
--   result = felt.add tmp fromArr
-- }
--
-- Exercises, all in one function: a dead first call whose results (`s2`,
-- `p2`) are never read, while an otherwise-identical second call survives
-- because `sum` is used; a dead array (`deadarr`) together with its dead
-- write; a dead `array.copy`; a condition (`cond1`) and if-statement that
-- become dead together once both of their branches turn out to only produce
-- unused values; and a second if-statement where one branch is partly dead
-- (`junk3`) and partly live (`branchval`), while its other branch is
-- entirely dead (`junk4`).

private def p5Helper : FuncWithMD F5 :=
  mkFunc "helper" [⟨"x", .ff⟩, ⟨"y", .ff⟩] [⟨"s", .ff⟩, ⟨"p", .ff⟩]
    [ mkCmd (.assign "s" (.bop .add (.var "x") (.var "y")))
    , mkCmd (.assign "p" (.bop .mul (.var "x") (.var "y")))
    ]

private def p5Main : FuncWithMD F5 :=
  mkFunc "main" [⟨"x", .ff⟩, ⟨"w", .ff⟩] [⟨"result", .ff⟩]
    [ mkCmd (.assign "dead1" (.bop .mul (.var "x") (.val 99)))
    , mkCmd (.func_call ["s2", "p2"] "helper" [.var "x", .var "w"])
    , mkCmd (.func_call ["sum", "prod"] "helper" [.var "x", .var "w"])
    , mkCmd (.new_array "deadarr" (.val 4))
    , mkCmd (.write_array "deadarr" (.val 0) (.var "x"))
    , mkCmd (.new_array "livearr" (.val 4))
    , mkCmd (.write_array "livearr" (.val 0) (.var "w"))
    , mkCmd (.read_array "fromArr" "livearr" (.val 0))
    , mkCmd (.copy_array "deadcopy" "livearr")
    , mkCmd (.assign "cond1" (.bop .gt (.var "x") (.val 0)))
    , mkCmd (.if_stmt (.eq (.var "cond1") (.val 1))
        [ mkCmd (.assign "junk1" (.bop .add (.var "x") (.val 1))) ]
        [ mkCmd (.assign "junk2" (.bop .add (.var "x") (.val 2))) ])
    , mkCmd (.assign "cond2" (.bop .gt (.var "w") (.val 0)))
    , mkCmd (.if_stmt (.eq (.var "cond2") (.val 1))
        [ mkCmd (.assign "junk3" (.bop .mul (.var "w") (.val 3)))
        , mkCmd (.assign "branchval" (.bop .add (.var "w") (.val 1))) ]
        [ mkCmd (.assign "junk4" (.bop .mul (.var "w") (.val 4))) ])
    , mkCmd (.assign "tmp" (.bop .add (.var "sum") (.var "branchval")))
    , mkCmd (.assign "result" (.bop .add (.var "tmp") (.var "fromArr")))
    ]

private def p5Prog : ProgWithMD F5 := mkProg [p5Helper, p5Main]

example : (progFuncs (removeUselessProg p5Prog)).map bareBody =
    [ [ .assign "s" (.bop .add (.var "x") (.var "y"))
      , .assign "p" (.bop .mul (.var "x") (.var "y")) ]
    , [ .func_call ["sum", "prod"] "helper" [.var "x", .var "w"]
      , .new_array "livearr" (.val 4)
      , .write_array "livearr" (.val 0) (.var "w")
      , .read_array "fromArr" "livearr" (.val 0)
      , .assign "cond2" (.bop .gt (.var "w") (.val 0))
      , .if_stmt (.eq (.var "cond2") (.val 1))
          [ .assign "branchval" (.bop .add (.var "w") (.val 1)) ]
          []
      , .assign "tmp" (.bop .add (.var "sum") (.var "branchval"))
      , .assign "result" (.bop .add (.var "tmp") (.var "fromArr")) ]
    ] := by rfl

-- p6: a fully dead loop next to a partially dead one
-- func main(x:ff) -> acc:ff {
--   acc = 0
--   repeat 5 { junk = felt.add x 1 }
--   repeat 4 { acc = felt.add acc x; junk2 = felt.mul x 3 }
-- }
--
-- The first loop only ever computes `junk`, which is never read anywhere, so
-- the whole loop is useless. The second loop's `junk2` is likewise unused,
-- but `acc` is the function's return value, so that assignment must survive
-- while `junk2` is dropped from the loop body.

private def p6Main : FuncWithMD F5 :=
  mkFunc "main" [⟨"x", .ff⟩] [⟨"acc", .ff⟩]
    [ mkCmd (.assign "acc" (.id (.val 0)))
    , mkCmd (.loop_exp (.val 5)
        [ mkCmd (.assign "junk" (.bop .add (.var "x") (.val 1))) ])
    , mkCmd (.loop_exp (.val 4)
        [ mkCmd (.assign "acc" (.bop .add (.var "acc") (.var "x")))
        , mkCmd (.assign "junk2" (.bop .mul (.var "x") (.val 3))) ])
    ]

private def p6Prog : ProgWithMD F5 := mkProg [p6Main]

example : (progFuncs (removeUselessProg p6Prog)).map bareBody =
    [[ .assign "acc" (.id (.val 0))
     , .loop_exp (.val 4) [ .assign "acc" (.bop .add (.var "acc") (.var "x")) ] ]] := by
  rfl

-- p7: a loop with a genuine cross-iteration dependency
-- func main(w:ff) -> x:ff {
--   x = 0
--   y = 0
--   z = 0
--   repeat 3 {
--     x = y
--     y = z
--     z = w
--   }
-- }
--
-- Regression test for why `removeUselessCmd`'s `.loop`/`.loop_exp` cases must
-- compute a genuine fixed point (`loopFixedPointOut`) instead of a single
-- pass: `x` only depends on `y`, `y` only on `z`, and `z` only on the
-- loop-invariant `w`, so a single backward pass seeded from the loop's own
-- live-out (`{x}`) would miss that `y` and `z` are live too, since neither is
-- in that initial out set. All three assignments inside the loop must
-- survive. `x = 0` (the value of `x` on entry to the loop) is genuinely
-- dead, since every iteration overwrites `x` from `y` before anything could
-- read the old value.

private def p7Main : FuncWithMD F5 :=
  mkFunc "main" [⟨"w", .ff⟩] [⟨"x", .ff⟩]
    [ mkCmd (.assign "x" (.id (.val 0)))
    , mkCmd (.assign "y" (.id (.val 0)))
    , mkCmd (.assign "z" (.id (.val 0)))
    , mkCmd (.loop_exp (.val 3)
        [ mkCmd (.assign "x" (.id (.var "y")))
        , mkCmd (.assign "y" (.id (.var "z")))
        , mkCmd (.assign "z" (.id (.var "w"))) ])
    ]

private def p7Prog : ProgWithMD F5 := mkProg [p7Main]

example : (progFuncs (removeUselessProg p7Prog)).map bareBody =
    [[ .assign "y" (.id (.val 0))
     , .assign "z" (.id (.val 0))
     , .loop_exp (.val 3)
         [ .assign "x" (.id (.var "y"))
         , .assign "y" (.id (.var "z"))
         , .assign "z" (.id (.var "w")) ] ]] := by rfl

-- p8: an if-statement with an implicit empty else must not drop its
--        live-in variable
-- func main(cond:ff, y:ff) -> z:ff {
--   if (cond == 1) {
--     y = 1
--   }
--   z = y
-- }
--
-- Regression test for a liveness bug: an `if` with no `else` clause parses
-- to an empty else-branch (`[]`). The then-branch here fully overwrites `y`
-- (so it doesn't need `y`'s prior value), but on the implicit empty
-- else-path nothing happens, so `y` must still be live-in to the whole
-- if-statement -- its value has to survive unchanged from before the `if`,
-- since `z = y` needs it right after. Getting this wrong wouldn't change
-- which commands survive here (there is nothing upstream of the `if` to
-- wrongly delete), so this also checks the if-statement's recorded
-- `live_in` directly rather than just the surviving command shape.

private def p8Main : FuncWithMD F5 :=
  mkFunc "main" [⟨"cond", .ff⟩, ⟨"y", .ff⟩] [⟨"z", .ff⟩]
    [ mkCmd (.if_stmt (.eq (.var "cond") (.val 1))
        [ mkCmd (.assign "y" (.id (.val 1))) ]
        [])
    , mkCmd (.assign "z" (.id (.var "y")))
    ]

-- Nothing is removed: both the if-statement and `z = y` survive unchanged.
example : bareBody (removeUselessFunc p8Main) =
    [ .if_stmt (.eq (.var "cond") (.val 1))
        [ .assign "y" (.id (.val 1)) ]
        []
    , .assign "z" (.id (.var "y")) ] := by rfl

-- The if-statement's (and hence the function's) live_in must still include
-- `y` -- the exact fact the bug this guards against would drop.
example : (funcMD (removeUselessFunc p8Main)).liveness.live_in.contains "y" = true := by decide

end Corellzk2smt.Language.Core.Analysis.Tests
