import Llzk.Basic
import Std.Data.TreeSet.Basic

/- This is a namespace for the core language -/

/- This is the reference to LLZK dialects, where the different
   operations are defined

 https://project-llzk.github.io/llzk-lib/main/dialects.html#felt-dialect

-/
namespace Llzk.Language.Core.Syntax.AST


abbrev VarID := String -- Program variable identifier
abbrev FName := String -- Function name


abbrev VarIDSet := Std.TreeSet VarID
abbrev emptyVarIDSet : VarIDSet := Std.TreeSet.empty

/- toString instance for VarIDSet -/
def VarIDSetToString (s : VarIDSet) : String :=
  let vars := s.toList
  String.intercalate ", " vars

instance : ToString VarIDSet where
  toString s := "{" ++ VarIDSetToString s ++ "}"


/- A structure for command information. It will be mainly used to related
   instructions to the source code, like line numbers, etc. More fields
   can be added later.
-/
structure SrcInfo where
  row : ℕ
  col : ℕ
  deriving Repr, BEq, Inhabited

structure LivenessInfo where
  live_in : VarIDSet := emptyVarIDSet
  live_out : VarIDSet := emptyVarIDSet
  deriving Repr, BEq, Inhabited

structure CmdMD where
  src_info : SrcInfo
  liveness : LivenessInfo := default
  deriving Repr, BEq, Inhabited

structure FuncMD where
  src_info : SrcInfo
  liveness : LivenessInfo := default
  deriving Repr, BEq, Inhabited

structure ProgMD where
  deriving Repr, BEq, Inhabited




/- A simple expression is either a variable or a finite field value -/
inductive SimpleExpr (c : ZKConfig) where
  | var (name : VarID) : SimpleExpr c   -- variable
  | val (val : FF c) : SimpleExpr c     -- FF value
  deriving Repr, BEq, Inhabited


/- Expression can be binary or unary operations, where operands are simple expressions -/
inductive Expr (c : ZKConfig) where
  -- arithmetic
  | id (s : SimpleExpr c) : Expr c  -- identity
  | neg (s : SimpleExpr c) : Expr c -- negation
  | add (s1 s2 : SimpleExpr c) : Expr c
  | sub (s1 s2 : SimpleExpr c) : Expr c
  | mul (s1 s2 : SimpleExpr c) : Expr c
  | div (s1 s2 : SimpleExpr c) : Expr c
  -- bitwise
  | shl (s bits: SimpleExpr c) : Expr c -- shift left
  | shr (s bits : SimpleExpr c) : Expr c -- shift right
  | and (s1 s2 : SimpleExpr c) : Expr c -- bitwise and
  | or (s1 s2 : SimpleExpr c) : Expr c -- bitwise or
  | xor (s1 s2 : SimpleExpr c) : Expr c -- bitwise xor
  | not (s : SimpleExpr c) : Expr c -- bitwise not
  -- boolean
  | True : Expr c -- boolean true
  | False : Expr c -- boolean false
  | eq (s1 s2 : SimpleExpr c) : Expr c -- equality check
  | neq (s1 s2 : SimpleExpr c) : Expr c -- inequality check
  | lt (s1 s2 : SimpleExpr c) : Expr c -- less than check
  | gt (s1 s2 : SimpleExpr c) : Expr c -- greater than check
  | le (s1 s2 : SimpleExpr c) : Expr c -- less than or equal check
  | ge (s1 s2 : SimpleExpr c) : Expr c -- greater than or equal check
  | bor (s1 s2 : SimpleExpr c) : Expr c -- logical or
  | band (s1 s2 : SimpleExpr c) : Expr c -- logical and
  | bneg (s : SimpleExpr c) : Expr c -- logical negation
   deriving Repr, BEq, Inhabited

inductive Cond (c : ZKConfig) where
  | eq (s1 s2 : SimpleExpr c) : Cond c
  | neq (s1 s2 : SimpleExpr c) : Cond c
  deriving Repr, BEq, Inhabited

mutual

/- A data type for command -/
inductive Com (c : ZKConfig) where
  -- in principle `skip` is not needed, we keep so we can augment it with
  -- debugging information if needed in the future, like a list of variables
  -- to print, etc.
  | skip
  -- x := e
  | assign (out: VarID) (e : Expr c)
  -- if (cond) {tb} else {eb}
  | if_stmt (cond: Cond c) (tb eb :  List (ComWithMD c))
  -- with (out := e) { body }
  -- e is supposed to be a constant expression, runtime error should be thrown
  -- if it is not. We keep it as Expr for simplicity.
  | loop_exp (rep: SimpleExpr c) (body: List (ComWithMD c))
  -- repeat N { body }
  -- N is supposed to be a natural number
  | loop (rep : ℕ) (body: List (ComWithMD c))
  -- size is supposed to be a constant expression, runtime error should be thrown if it is not.
  | new_array (out: VarID) (size: SimpleExpr c)
  -- out := arr[idx]
  | read_array (out: VarID) (arr: VarID) (idx: SimpleExpr c)
  -- out[idx] := value
  | write_array (arr: VarID) (idx: SimpleExpr c) (value: SimpleExpr c)
  -- out := copy_array arr
  | copy_array (out: VarID) (arr: VarID)
  -- out1, out2, ... := func(args)
  | func_call (outs: List VarID) (fname: FName) (args: List (SimpleExpr c))
   deriving Repr, BEq, Inhabited

/- Adding metadata to commands -/
inductive ComWithMD (c : ZKConfig) : Type
  | mk (md : CmdMD) (cmd : Com c) : ComWithMD c
  deriving Repr, BEq, Inhabited

end

/- A command with metadata -/
--abbrev ComWithMD (c : ZKConfig) := ProgElem (Com c)

/- We have two types: finite field and array -/
inductive VarType where
  | ff
  | array (size : ℕ)
  deriving Repr, BEq, Inhabited

/- A parameter is a pair of variable identifier and its type -/
structure Param where
  name : VarID
  type : VarType
  deriving Repr, BEq, Inhabited

/- A function receives input parameters `params`, executes the whole `body`,
   and returns the variables in `rets`.
-/
inductive Func (c : ZKConfig) where
  | mk (name : FName) (params : List Param)
       (rets : List Param) (body : List (ComWithMD c)) : Func c
  deriving Repr, BEq, Inhabited

/- A function with metadata -/
inductive FuncWithMD (c : ZKConfig) where
  | mk (md : FuncMD) (func : Func c) : FuncWithMD c
  deriving Repr, BEq, Inhabited

/- A program is a list of functions. Since we forbid recursion, a function can only call
those that precede it in the list (this should be forced in the semantics)
 -/
abbrev Prog (c : ZKConfig) := List (FuncWithMD c)

/- A program with metadata. It is the top-level element of a program, which includes
   the whole program and the metadata for it. -/
inductive ProgWithMD (c : ZKConfig) where
  | mk (md : ProgMD) (prog : Prog c) : ProgWithMD c
  deriving Repr, BEq, Inhabited

/- Search a function by name. It returns the function and the remaining program,
   which includes the functions that can be called by it. -/
def fetchFunc {c : ZKConfig}
  (p : Prog c) (fname : FName) : Except String (FuncWithMD c × Prog c) :=
  match p with
  | [] => Except.error s!"Function {fname} not found in the program"
  | funcWMD :: fs =>
    match funcWMD with
    | .mk _ f =>
    match f with
     | .mk name _ _ _ =>
       if name == fname then
         Except.ok (funcWMD, fs)
       else
         fetchFunc fs fname

/- fetchFunc returns a smaller program -/
theorem fetchLT {c : ZKConfig}
  (p : Prog c) (fname : FName) (f : FuncWithMD c) (p' : Prog c) :
  fetchFunc p fname = Except.ok (f, p') → p'.length < p.length := by
  cases p with
  | nil => simp [fetchFunc]
  | cons func fs =>
    match func with
    | .mk _ f' =>
      match f' with
      | .mk name params rets body =>
        simp only [fetchFunc]
        by_cases hname : name = fname
        · simp only [hname]
          simp only [BEq.rfl, List.length_cons]
          simp only [if_true]
          intro h_eq
          injection h_eq with h_inner
          injection h_inner with h_func h_prog
          rw [h_prog]
          apply Nat.le_refl
        · simp only [beq_iff_eq, hname, List.length_cons]
          simp only [if_false]
          intro h1
          have h2 := fetchLT fs fname f p' h1
          apply Nat.lt_of_lt_of_le h2
          apply Nat.le_succ

/- Size of a command and list of commands. They are used to prove termination of
   functions that manipulate programs -/

mutual

def sizeOfCom {c : ZKConfig} (i : ComWithMD c) : Nat :=
  match i with
  | .mk _ info =>
    match info with
    | .skip => 1
    | .if_stmt _ tb eb =>
        1 + sizeOfComs tb + sizeOfComs eb
    | .loop_exp _ body =>
      1 + sizeOfComs body
    | .loop rep body =>
      1 + rep*(1+sizeOfComs body)
    | _ => 1

def sizeOfComs {c : ZKConfig} (cmds : List (ComWithMD c)) : Nat :=
match cmds with
| [] => 0
| cmd::rest => 1 + sizeOfCom cmd + sizeOfComs rest

end -- mutual

/- Number of loop_exp in a command and list of commands. They are used to prove termination of
   functions that manipulate programs -/

mutual

def numOfLoopExpCom {c : ZKConfig} (cmd : ComWithMD c) : Nat :=
  match cmd with
  | .mk _ info =>
    match info with
    | .if_stmt _ tb eb =>
        numOfLoopExpComs tb + numOfLoopExpComs eb
    | .loop_exp _ body =>
      1 + numOfLoopExpComs body
    | .loop _ body =>
      numOfLoopExpComs body
    | _ => 0

def numOfLoopExpComs {c : ZKConfig} (cmds : List (ComWithMD c)) : Nat :=
  match cmds with
  | [] => 0
  | cmd::rest => numOfLoopExpCom cmd + numOfLoopExpComs rest

end -- mutual





end Llzk.Language.Core.Syntax.AST
