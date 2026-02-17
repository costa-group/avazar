import Llzk.Basic
import Init.Data.BitVec

/- This is a namespace for the core language -/

namespace Llzk.Language.Core.Syntax.AST

/- A structure for command information. It will be mainly used to related
   instructions to the source code, like line numbers, etc. More fields
   can be added later.
-/
structure SrcInfo where
  line : ℕ
  deriving Repr, BEq, Inhabited

/- A structure for command metadata. More fields can be added later. -/
structure CmdMetaData where
  src_info : SrcInfo
  deriving Repr, BEq, Inhabited

abbrev emptyCMD : CmdMetaData := ⟨⟨0⟩⟩

abbrev VarID := String -- Program variable identifier
abbrev FName := String -- Function name


/- A simple expression is either a variable, constant variable, or a finite field value -/
inductive SimpleExpr (c : ZKConfig) where
  | var (name : VarID) : SimpleExpr c   -- variable
  | cvar (name : VarID) : SimpleExpr c  -- constant variable
  | val (val : FF c) : SimpleExpr c     -- FF value
  deriving Repr, BEq, Inhabited


/- Expression can be binary or unary operations, where operands are simple expressions -/
inductive Expr (c : ZKConfig) where
  -- arithmetic
  | id (e : SimpleExpr c) : Expr c  -- identity
  | neg (e : SimpleExpr c) : Expr c -- negation
  | add (e1 e2 : SimpleExpr c) : Expr c
  | sub (e1 e2 : SimpleExpr c) : Expr c
  | mul (e1 e2 : SimpleExpr c) : Expr c
  | div (e1 e2 : SimpleExpr c) : Expr c
  -- bitwise
  | shl (e bits: SimpleExpr c) : Expr c -- shift left
  | shr (e bits : SimpleExpr c) : Expr c -- shift right
  | and (e1 e2 : SimpleExpr c) : Expr c -- bitwise and
  | or (e1 e2 : SimpleExpr c) : Expr c -- bitwise or
  | xor (e1 e2 : SimpleExpr c) : Expr c -- bitwise xor
  | not (e : SimpleExpr c) : Expr c -- bitwise not
  -- boolean
  | True : Expr c -- boolean true
  | False : Expr c -- boolean false
  | eq (e1 e2 : SimpleExpr c) : Expr c -- equality check
  | neq (e1 e2 : SimpleExpr c) : Expr c -- inequality check
  | lt (e1 e2 : SimpleExpr c) : Expr c -- less than check
  | gt (e1 e2 : SimpleExpr c) : Expr c -- greater than check
  | le (e1 e2 : SimpleExpr c) : Expr c -- less than or equal check
  | ge (e1 e2 : SimpleExpr c) : Expr c -- greater than or equal check
  | bor (e1 e2 : SimpleExpr c) : Expr c -- logical or
  | band (e1 e2 : SimpleExpr c) : Expr c -- logical and
  | bneg (e : SimpleExpr c) : Expr c -- logical negation
   deriving Repr, BEq, Inhabited

inductive Cond (c : ZKConfig) where
  | eq (e1 e2 : SimpleExpr c) : Cond c
  | neq (e1 e2 : SimpleExpr c) : Cond c
  deriving Repr, BEq, Inhabited

/- A data type for command -/
inductive Com (c : ZKConfig) where
  -- in principle `skip` is not needed, we keep so we can augment it with
  -- debugging information if needed in the future, like a list of variables
  -- to print, etc.
  | skip (md: CmdMetaData)
  -- x := e
  | assign (md: CmdMetaData) (out: VarID) (e : Expr c)
  -- if (cond) {tb} else {eb}
  | if_stmt (md: CmdMetaData) (cond: Cond c) (tb eb :  List (Com c))
  -- with (out := e) { body }
  -- e is supposed to be a constant expression, runtime error should be thrown
  -- if it is not. We keep it as Expr for simplicity.
  | with_const (md: CmdMetaData) (out: VarID) (e : Expr c) (body: List (Com c))
  -- for (i,start,rep,step) { body }
  -- expressions are supposed to be constant expression, runtime error
  -- should be thrown if they are not. We keep them as Expr for simplicity
  | loop_exp (md: CmdMetaData) (idx: VarID) (start rep step: Expr c) (body: List (Com c))
  -- for (i,start,rep,step) { body }
  | loop (md: CmdMetaData) (idx: VarID) (start : FF c) (rep : ℕ) (step: FF c) (body: List (Com c))
  -- size is supposed to be a constant expression, runtime error should be thrown if it is not.
  | new_array (md: CmdMetaData) (out: VarID) (size: SimpleExpr c)
  -- out := arr[idx]
  | read_array (md: CmdMetaData) (out: VarID) (arr: VarID) (idx: SimpleExpr c)
  -- out[idx] := value
  | write_array (md: CmdMetaData) (arr: VarID) (idx: SimpleExpr c) (value: SimpleExpr c)
  -- out := copy_array arr
  | copy_array (md: CmdMetaData) (out: VarID) (arr: VarID)
  -- out1, out2, ... := func(args)
  | func_call (md: CmdMetaData) (outs: List VarID) (fname: FName) (args: List (SimpleExpr c))
   deriving Repr, BEq, Inhabited


/- We have two types: finite field and array -/
inductive VarType where
  | ff
  | array (size : ℕ)
  deriving Repr, BEq, Inhabited

/- A parameter is a pair of variable identifier and its type -/
abbrev Param := (VarID × VarType)

/- A function receives input parameters `params`, executes the whole `body`,
   and returns the variables in `rets`.
-/
structure Function (c : ZKConfig) where
  md : CmdMetaData
  name : FName
  params : List Param
  rets : List Param
  body : List (Com c)
  deriving Repr, BEq, Inhabited

/- A program is a list of functions. Since we forbid recursion, a function can only call
those that precede it in the list (this should be forced in the semantics)
 -/
abbrev Prog (c : ZKConfig) := List (Function c)


/- Search a function by name. It returns the function and the remaining program,
   which includes the functions that can be called by it. -/
def fetchFunc {c : ZKConfig} (p : Prog c) (fname : FName) : Except String (Function c × Prog c) :=
  match p with
  | [] => Except.error s!"Function {fname} not found in the program"
  | f :: fs =>
    if f.name == fname then
      Except.ok (f, fs)
    else
      fetchFunc fs fname

/- fetchFunc returns a smaller program -/
theorem fetchLT {c : ZKConfig} (p : Prog c) (fname : FName) (f : Function c) (p' : Prog c) :
  fetchFunc p fname = Except.ok (f, p') → p'.length < p.length := by
  cases p with
  | nil => simp [fetchFunc]
  | cons f' fs =>
    simp only [fetchFunc]
    by_cases hname : f'.name = fname
    · simp only [hname]
      simp only [BEq.rfl, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq, List.length_cons, and_imp]
      intro h1 h2
      rw [h2]
      simp only [lt_add_iff_pos_right, zero_lt_one]
    · simp only [beq_iff_eq, hname, ↓reduceIte, List.length_cons]
      intro h1
      have h2 := fetchLT fs fname f p' h1
      grind


/- The following few functions are used to convert a program to a string
   using pretty printing. It is registered as ToString instance for Prog
   so that it can be called implicitly
-/
def getIndent (level : Nat) : String :=
  String.ofList (List.replicate (level * 2) ' ')

def formatSexpr {c : ZKConfig} (s : SimpleExpr c) : String :=
  match s with
  | .var varName => s!"%{varName}"
  | .cvar cvarName => s!"${cvarName}"
  | .val val => s!"{val}"

-- register ToString instance for SimpleExpr
instance {c : ZKConfig} : ToString (SimpleExpr c) where
  toString s := formatSexpr s

def formatExpr {c : ZKConfig} (e : Expr c) : String :=
  match e with
  -- arithmetic
  | .id s => s!"{s}"
  | .neg s => s!"felt.neg {s}"
  | .add s1 s2 => s!"felt.add {s1} {s2}"
  | .sub s1 s2 => s!"felt.sub {s1} {s2}"
  | .mul s1 s2 => s!"felt.mul {s1} {s2}"
  | .div s1 s2 => s!"felt.div {s1} {s2}"
  -- bitwise
  | .shl s bits => s!"bit.shl {s} {bits}"
  | .shr s bits => s!"bit.shr {s} {bits}"
  | .and s1 s2 => s!"bit.and {s1} {s2}"
  | .or s1 s2 => s!"bit.or {s1} {s2}"
  | .xor s1 s2 => s!"bit.xor {s1} {s2}"
  | .not s => s!"bit.not {s}"
   -- boolean
  | .True => "bool.True"
  | .False => "bool.False"
  | .eq s1 s2 => s!"bool.eq {s1} {s2}"
  | .neq s1 s2 => s!"bool.neq {s1} {s2}"
  | .lt s1 s2 => s!"bool.lt {s1} {s2}"
  | .gt s1 s2 => s!"bool.gt {s1} {s2}"
  | .le s1 s2 => s!"bool.le {s1} {s2}"
  | .ge s1 s2 => s!"bool.ge {s1} {s2}"
  | .bor s1 s2 => s!"bool.or {s1} {s2}"
  | .band s1 s2 => s!"bool.and {s1} {s2}"
  | .bneg s => s!"bool.not {s}"

-- register ToString instance for Expr
instance {c : ZKConfig} : ToString (Expr c) where
  toString e := formatExpr e

def formatCond {c : ZKConfig} (cond : Cond c) : String :=
  match cond with
  | .eq s1 s2 => s!"{s1} == {s2}"
  | .neq s1 s2 => s!"{s1} != {s2}"

-- register ToString instance for Cond
instance {c : ZKConfig} : ToString (Cond c) where
  toString cond := formatCond cond

def formatParam (p : Param) : String :=
  let (varName, varType) := p
  let typeStr := match varType with
                 | VarType.ff => "ff"
                 | VarType.array size => s!"arr<{size}>"
  s!"%{varName}:{typeStr}"

-- register ToString instance for Param
instance : ToString Param where
  toString p := formatParam p

def formatParams (ps : List Param) : String :=
  String.intercalate ", " (ps.map toString)

-- register ToString instance for (List Param)
instance : ToString (List Param) where
  toString ps := formatParams ps

mutual

def formatCom {c : ZKConfig} (cmd : Com c) (level : Nat) (sp : String) : String :=
  match cmd with
  | .skip _ => s!"skip"
  | .assign _ out e => s!"%{out} := {e}"
  | .if_stmt _ cond tb eb =>
      let tbStr := formatBody tb (level + 1)
      let ebStr := formatBody eb (level + 1)
      s!"if ({cond}) " ++ "{\n" ++ s!"{tbStr}" ++
        s!"{sp}} else " ++ "{\n" ++ s!"{ebStr}" ++ s!"{sp}}"
  | .with_const _ out e body =>
      let bodyStr := formatBody body (level + 1)
      s!"with_const (${out} = {e}) " ++ "{\n" ++ s!"{bodyStr}" ++ s!"{sp}}"
  | .loop_exp _ idx start rep step body =>
      let bodyStr := formatBody body (level + 1)
      s!"for (${idx}, {start}, {rep}, {step}) " ++ "{\n" ++
      s!"{bodyStr}" ++ s!"{sp}}"
  | .loop _ idx start rep step body =>
      let bodyStr := formatBody body (level + 1)
      s!"for (${idx}, {start}, {rep}, {step}) " ++ "{\n" ++
      s!"{bodyStr}" ++ s!"{sp}}"
  | .new_array _ out size =>
      s!"array.new {size} %{out}"
  | .read_array _ out arr idx =>
      s!"array.read %{arr}[{idx}] %{out}"
  | .write_array _ arr idx value =>
      s!"array.write {value} %{arr}[{idx}]"
  | .copy_array _ out arr =>
      s!"array.copy %{arr} %{out}"
  | .func_call _ outs fname args =>
      let outsStr := String.intercalate ", " (outs.map (fun v => s!"%{v}"))
      let argsStr := String.intercalate ", " (args.map toString)
      if (outs == []) then
        s!"call %{fname} ({argsStr})"
      else
        s!"call %{fname} ({argsStr}) to {outsStr}"

def formatBody {c : ZKConfig} (p : List (Com c)) (level : Nat) : String :=
  let sp := getIndent level
  match p with
  | [] => ""
  | cmd::cmds =>
      let cmdStr := formatCom cmd level sp
      let restStr := formatBody cmds level
      s!"{sp}{cmdStr}\n{restStr}"

end -- mutual

def formatFunction {c : ZKConfig} (f : Function c) : String :=
  let bodyStr := formatBody f.body 1
  if (f.rets == []) then
    s!"func %{f.name}({f.params}) " ++ "{\n" ++ s!"{bodyStr}" ++ "}\n"
  else
    s!"func %{f.name}({f.params}) : {f.rets} " ++ "{\n" ++ s!"{bodyStr}" ++ "}\n"

-- register ToString instance for Function
instance {c : ZKConfig} : ToString (Function c) where
  toString f := formatFunction f

def formatProg {c : ZKConfig} (p : Prog c) : String :=
  let funcStrs := p.map toString
  String.intercalate "\n\n" funcStrs

-- register ToString instance for Program
instance {c : ZKConfig} : ToString (Prog c) where
  toString p := formatProg p


mutual

def printCom {c : ZKConfig}
    (h : IO.FS.Stream) (cmd : Com c) (level : Nat) (sp : String) : IO Unit := do
  match cmd with
  | .skip _ => h.putStr s!"skip"
  | .assign _ out e => h.putStr s!"%{out} = {e}"
  | .if_stmt _ cond tb eb =>
      h.putStr s!"if ({cond})"
      h.putStrLn " {"
      printBody h tb (level + 1)
      h.putStr sp
      h.putStrLn "} else {"
      printBody h eb (level + 1)
      h.putStr sp
      h.putStr "}"
  | .with_const _ out e body =>
      h.putStr s!"with_const (${out} := {e})"
      h.putStrLn " {"
      printBody h body (level + 1)
      h.putStr sp
      h.putStr "}"
  | .loop_exp _ idx start rep step body =>
      h.putStr s!"for (${idx}, {start}, {rep}, {step})"
      h.putStrLn " {"
      printBody h body (level + 1)
      h.putStr sp
      h.putStr "}"
  | .loop _ idx start rep step body =>
      h.putStr s!"for (${idx}, {start}, {rep}, {step})"
      h.putStrLn " {"
      printBody h body (level + 1)
      h.putStr sp
      h.putStrLn "}"
  | .new_array _ out size =>
      h.putStr s!"array.new {size} %{out}"
  | .read_array _ out arr idx =>
      h.putStr s!"array.read %{arr}[{idx}] %{out}"
  | .write_array _ arr idx value =>
      h.putStr s!"array.write {value} %{arr}[{idx}]"
  | .copy_array _ out arr =>
      h.putStr s!"array.copy %{arr} %{out}"
  | .func_call _ outs fname args =>
      let outsStr := String.intercalate ", " (outs.map (fun v => s!"%{v}"))
      let argsStr := String.intercalate ", " (args.map toString)
      if (outs == []) then
        h.putStr s!"call %{fname} ({argsStr})"
      else
        h.putStr s!"call %{fname} ({argsStr}) to {outsStr}"

def printBody {c : ZKConfig} (h : IO.FS.Stream) (p : List (Com c)) (level : Nat) : IO Unit := do
  let sp := getIndent level
  match p with
  | [] => pure ()
  | cmd::cmds =>
      h.putStr s!"{sp}"
      printCom h cmd level sp
      h.putStrLn ""
      printBody h cmds level

end -- mutual

def printFunction {c : ZKConfig} (h : IO.FS.Stream) (f : Function c) : IO Unit := do
  if (f.rets == []) then
    h.putStr s!"func %{f.name}({f.params})"
  else
    h.putStr s!"func %{f.name}({f.params}) : {f.rets}"
  h.putStrLn " {"
  printBody h f.body 1
  h.putStrLn "}"

def printProg {c : ZKConfig} (h : IO.FS.Stream) (p : Prog c) : IO Unit := do
    for f in p do
      printFunction h f
      h.putStrLn ""


/- Size of a command and list of commands. They are used to prove termination of
   functions that manipulate programs -/

mutual

def sizeOfCom {c : ZKConfig} (cmd : Com c) : Nat :=
  match cmd with
  | .if_stmt _ _ tb eb =>
      1 + sizeOfComs tb + sizeOfComs eb
  | .with_const _ _ _ body =>
      1 + sizeOfComs body
  | .loop_exp _ _ _ _ _ body =>
      1 + sizeOfComs body
  | .loop _ _ _ rep _ body =>
      1 + rep*(1+sizeOfComs body)
  | _ => 1

def sizeOfComs {c : ZKConfig} (cmds : List (Com c)) : Nat :=
match cmds with
| [] => 0
| cmd::rest => 1 + sizeOfCom cmd + sizeOfComs rest

end -- mutual

/- Number of loop_exp in a command and list of commands. They are used to prove termination of
   functions that manipulate programs -/

mutual

def numOfLoopExpCom {c : ZKConfig} (cmd : Com c) : Nat :=
  match cmd with
  | .if_stmt _ _ tb eb =>
      numOfLoopExpComs tb + numOfLoopExpComs eb
  | .with_const _ _ _ body =>
      numOfLoopExpComs body
  | .loop_exp _ _ _ _ _ body =>
      1 + numOfLoopExpComs body
  | .loop _ _ _ _ _ body =>
      numOfLoopExpComs body
  | _ => 0

def numOfLoopExpComs {c : ZKConfig} (cmds : List (Com c)) : Nat :=
  match cmds with
  | [] => 0
  | cmd::rest => numOfLoopExpCom cmd + numOfLoopExpComs rest

end -- mutual



end Llzk.Language.Core.Syntax.AST
