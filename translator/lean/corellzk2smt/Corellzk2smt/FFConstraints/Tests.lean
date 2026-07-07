import Corellzk2smt.Basic
import Corellzk2smt.Config
import Corellzk2smt.FFConstraints.Basic
import Corellzk2smt.FFConstraints.Satisfiability
import Corellzk2smt.FFConstraints.SMT

namespace Corellzk2smt.FFConstraints.Tests

open Corellzk2smt.Config (GlobalConfig)
open Corellzk2smt.FFConstraints.Basic
open Corellzk2smt.FFConstraints.Satisfiability
open Corellzk2smt.FFConstraints.SMT

private instance [BEq ε] [BEq α] : BEq (Except ε α) where
  beq x y :=
    match x, y with
    | .ok a, .ok b => a == b
    | .error e1, .error e2 => e1 == e2
    | _, _ => false


private def gconf5 : GlobalConfig F5 := default

private def m1 : FFMacro F5 := { name := "foo", params := [], body := .true }
private def m2 : FFMacro F5 := { name := "bar", params := [], body := .false }
private def m3 : FFMacro F5 := { name := "baz", params := [], body := .true }

-- fetchMacro on an empty list always returns an error
example : fetchMacro gconf5 [] "foo" = Except.error "Macro foo not found" := rfl

-- fetchMacro finds the first element and returns the remaining list
example : fetchMacro gconf5 [m1, m2, m3] "foo" = Except.ok (m1, [m2, m3]) := rfl

-- fetchMacro finds an element that is not first; only the tail after it is returned
example : fetchMacro gconf5 [m1, m2, m3] "bar" = Except.ok (m2, [m3]) := rfl

-- fetchMacro returns an error when no macro matches the name
example : fetchMacro gconf5 [m1, m2, m3] "qux" = Except.error "Macro qux not found" := rfl


-- Assignment used in evalTerm / evalFormula tests:
--   ff: v_0 ↦ 2, v_1 ↦ 3, v_n ↦ 0
--   bool: b_0 ↦ true, b_n ↦ false
private def assign5 : Assignment F5 := {
  ff   := fun n => match n with | 0 => 2 | 1 => 3 | _ => 0
  bool := fun n => n == 0
}

-- evalTerm: a constant value is returned unchanged
example : evalTerm gconf5 assign5 (.val 3) [] = Except.ok 3 := by
  simp [evalTerm]

-- evalTerm: a variable is looked up in the assignment (v_1 ↦ 3)
example : evalTerm gconf5 assign5 (.var 1) [] = Except.ok 3 := by
  simp [evalTerm]
  rfl

-- evalTerm: addition wraps modulo p  (2 + 3 = 5 ≡ 0 in F5)
example : evalTerm gconf5 assign5 (.add (.var 0) (.var 1)) [] = Except.ok 0 := by
  simp [evalTerm]
  rfl

-- evalTerm: negation  (−2 ≡ 3 in F5)
example : evalTerm gconf5 assign5 (.neg (.val 2)) [] = Except.ok 3 := by
  simp [evalTerm]
  rfl

-- evalFormula: two identical field elements satisfy equality
example : evalFormula gconf5 assign5 (.eq (.val 3) (.val 3)) [] = Except.ok true := by
  simp [evalFormula, evalTerm]

-- evalFormula: (not true) evaluates to false
example : evalFormula gconf5 assign5 (.not .true) [] = Except.ok false := by
  simp [evalFormula]

-- evalFormula: range check passes when the value lies within the bounds
--   v_0 ↦ 2, and 1.val ≤ 2.val ≤ 4.val holds
example : evalFormula gconf5 assign5 (.range (.var 0) 1 4) [] = Except.ok true := by
  simp only [evalFormula, evalTerm]
  rfl

-- evalFormula: a macro call expands the macro and renames its parameters
--   "isZero" checks whether its argument equals 0; v_0 ↦ 2, so the result is false
private def m_isZero : FFMacro F5 := {
  name := "isZero", params := [.ffv 0], body := .eq (.var 0) (.val 0)
}
example : evalFormula gconf5 assign5 (.call "isZero" [.var (.ffv 0)]) [m_isZero] =
  Except.ok false := by
    simp [evalFormula, fetchMacro, m_isZero, newAssignment, newAssignment', evalTerm, assign5]
    grind

example : evalFormula gconf5 assign5 (.call "isZero" [.var (.ffv 2)]) [m_isZero] =
  Except.ok true := by
    simp [evalFormula, fetchMacro, m_isZero, newAssignment, newAssignment', evalTerm, assign5]

-- ── SMT variable printing ──────────────────────────────────────────────────

-- varID is pure; both FF and bool variables use the same "v_n" prefix.
-- The type distinction (FFp vs Bool) is expressed in the SMT sort, not the name.
example : varID gconf5 (Var.ffv 3) = "v_3" := rfl
example : varID gconf5 (Var.boolv 2) = "b_2" := rfl

-- IO printing functions require a stream that captures output to a string.
private def mkCaptureStream : IO (IO.FS.Stream × IO.Ref String) := do
  let r ← IO.mkRef ""
  let stream : IO.FS.Stream := {
    flush   := pure ()
    read    := fun _ => pure ByteArray.empty
    write   := fun bytes => r.modify (· ++ String.fromUTF8! bytes)
    getLine := pure ""
    putStr  := fun s => r.modify (· ++ s)
    isTty   := pure false
  }
  return (stream, r)

-- printTerm: an FF variable prints as "v_n"
#eval do
  let (stream, ref) ← mkCaptureStream
  printTerm gconf5 stream (.var 0 : FFTerm F5)
  let result ← ref.get
  if result == "v_0" then IO.println "OK"
  else IO.println s!"FAIL: expected 'v_0', got '{result}'"

-- printFormula: a bool variable also prints as "b_n"
#eval do
  let (stream, ref) ← mkCaptureStream
  printFormula gconf5 stream (.bool 1 : FFFormula F5) 0 false
  let result ← ref.get
  if result == "b_1" then IO.println "OK"
  else IO.println s!"FAIL: expected ' b_1', got '{result}'"

-- printMacro: FF params get sort FFp, bool params get sort Bool
private def m_vars : FFMacro F5 := {
  name := "check",
  params := [.ffv 0, .boolv 1],
  body := .and (.eq (.var 0) (.val 0)) (.bool 1)
}
#eval do
  let (stream, ref) ← mkCaptureStream
  printMacro gconf5 stream m_vars
  let result ← ref.get
  let expected :=
  "(define-fun check ((v_0 FFp) (b_1 Bool)) Bool\n" ++
  "  (and \n" ++
  "    (= v_0 0)\n" ++
  "    b_1  )\n" ++
  ")\n"
  if result == expected then IO.println "OK"
  else IO.println s!"FAIL:\nexpected: '{expected}'\ngot:      '{result}'"

-- ── printConstraintSystem_asJSON ──────────────────────────────────────────

-- Test 1: main macro missing → error line
private def sys_no_main : FFConstraintSystem F5 := { macros := [], main := "main" }

#eval do
  let (stream, ref) ← mkCaptureStream
  printConstraintSystem_asJSON gconf5 stream sys_no_main
  let result ← ref.get
  if result == "Error: Macro main not found\n" then IO.println "OK"
  else IO.println s!"FAIL: got '{result}'"

-- Test 2: FF variable → "v_0" appears in params, vars, and the call formula
private def sys_ff_var : FFConstraintSystem F5 := {
  macros := [{ name := "main", params := [.ffv 0], body := .eq (.var 0) (.val 0) }],
  main := "main"
}

#eval do
  let (stream, ref) ← mkCaptureStream
  printConstraintSystem_asJSON gconf5 stream sys_ff_var
  let result ← ref.get
  let expected :=
    "{\n" ++
    "  \"prime\": 5,\n" ++
    "  \"macros\": {\n" ++
    "    \"main\": {\n" ++
    "        \"params\": [{ \"name\": \"v_0\", \"type\": \"ff\" }],\n" ++
    "        \"vars_info\": {},\n" ++
    "        \"formula\": \" (= v_0 0) \"\n" ++
    "     }\n" ++
    "  },\n" ++
    "  \"main\": {\n" ++
    "    \"vars\": [{ \"name\": \"v_0\", \"type\": \"ff\" }],\n" ++
    "    \"formula\": \" (main v_0) \" }\n" ++
    "}\n"
  if result == expected then IO.println "OK"
  else IO.println s!"FAIL:\nexpected: '{expected}'\ngot:      '{result}'"

-- Test 3: bool variable → "b_2" appears with type "bool"
private def sys_bool_var : FFConstraintSystem F5 := {
  macros := [{ name := "main", params := [.boolv 2], body := .bool 2 }],
  main := "main"
}

#eval do
  let (stream, ref) ← mkCaptureStream
  printConstraintSystem_asJSON gconf5 stream sys_bool_var
  let result ← ref.get
  let expected :=
    "{\n" ++
    "  \"prime\": 5,\n" ++
    "  \"macros\": {\n" ++
    "    \"main\": {\n" ++
    "        \"params\": [{ \"name\": \"b_2\", \"type\": \"bool\" }],\n" ++
    "        \"vars_info\": {},\n" ++
    "        \"formula\": \" b_2 \"\n" ++
    "     }\n" ++
    "  },\n" ++
    "  \"main\": {\n" ++
    "    \"vars\": [{ \"name\": \"b_2\", \"type\": \"bool\" }],\n" ++
    "    \"formula\": \" (main b_2) \" }\n" ++
    "}\n"
  if result == expected then IO.println "OK"
  else IO.println s!"FAIL:\nexpected: '{expected}'\ngot:      '{result}'"

end Corellzk2smt.FFConstraints.Tests
