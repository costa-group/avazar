import Corellzk2smt.Basic
import Corellzk2smt.Config

--import Std.Data.TreeSet.Basic

/- This is a namespace for the core language -/

/- This is the reference to LLZK dialects, where the different
   operations are defined

 https://project-llzk.github.io/llzk-lib/main/dialects.html#felt-dialect

-/
namespace Corellzk2smt.Language.Core.Syntax.AST


open Corellzk2smt.Config

abbrev VarID := String -- Program variable identifier
abbrev FName := String -- Function name

/- Sets of variable identifiers -/
abbrev VarIDSet := Std.TreeSet VarID
abbrev emptyVarIDSet : VarIDSet := Std.TreeSet.empty

/- toString instance for VarIDSet -/
instance : ToString VarIDSet where
  toString s := "{" ++ (String.intercalate ", " s.toList) ++ "}"


/- A structure for command source code information. It will be mainly used
   to related instructions to the source code, like line numbers, etc. More
   fields can be added later.
-/
structure SrcInfo where
  row : ℕ
  col : ℕ
  deriving Repr, BEq, Inhabited, Ord

/- A structure to include the liveness information at a given program point.
-/
structure LivenessInfo where
  live_in : VarIDSet := emptyVarIDSet
  live_out : VarIDSet := emptyVarIDSet
  deriving Repr, BEq, Inhabited

/- Metadata for commands, it includes source code information and liveness
   information. More fields can be added later.
-/
structure CmdMD where
  src_info : SrcInfo
  liveness : LivenessInfo := default
  deriving Repr, BEq, Inhabited

/- Metadata for functions, it includes source code information and liveness
   information. More fields can be added later.
-/
structure FuncMD where
  src_info : SrcInfo
  liveness : LivenessInfo := default -- TBD: not sure this is needed
  deriving Repr, BEq, Inhabited

/- Metadata for programs, it does not include anything for now. -/
structure ProgMD where
  deriving Repr, BEq, Inhabited


/- A simple expression is either a variable or a finite field value -/
inductive SimpleExpr (c : ZKConfig) where
  | var (name : VarID) : SimpleExpr c   -- variable
  | val (val : FF c) : SimpleExpr c     -- FF value
  deriving Repr, BEq, Inhabited

/- Binary operations -/
inductive BinOp where
  | add -- addition (arithmetic)
  | sub -- subtraction (arithmetic)
  | mul -- multiplication (arithmetic)
  | div -- division (arithmetic)
  | pow -- exponentiation (arithmetic)
  | shl -- shift left (arithmetic)
  | shr -- shift right (arithmetic)
  | and -- bitwise and (bitwise)
  | or  -- bitwise or (bitwise)
  | xor -- bitwise xor (bitwise)
  | eq  -- equality (boolean)
  | neq -- inequality (boolean)
  | lt  -- signed less than (boolean)
  | gt  -- signed greater than (boolean)
  | le  -- signed less than or equal to (boolean)
  | ge  -- signed greater than or equal to (boolean)
  | bor -- boolean or (boolean)
  | band -- boolean and (boolean)
  deriving Repr, BEq, Inhabited

/- Unary operations -/
inductive UnOp where
  | neg   -- arithmetic negation (arithmetic)
  | not   -- bitwise negation (bitwise)
  | bneg  -- boolean negation (boolean)
  deriving Repr, BEq, Inhabited

/- Expression can be binary or unary operations, where operands are simple expressions -/
inductive Expr (c : ZKConfig) where
  -- arithmetic
  | bop (op : BinOp) (s1 s2 : SimpleExpr c) : Expr c
  | uop (op : UnOp) (s : SimpleExpr c) : Expr c
  | id (s : SimpleExpr c) : Expr c
   deriving Repr, BEq, Inhabited

/- A condition is a comparison between two simple expressions. This will appear in a
   conditional statement. More elaborated conditions can be evaluated using the corresponding
   expression first, for example:

     z = bool.gt x y
     if (z == 1) { ... } else { ... }

-/
inductive Cond (c : ZKConfig) where
  | eq (s1 s2 : SimpleExpr c) : Cond c
  deriving Repr, BEq, Inhabited



/- The next data type is for representing commands. It consists of one for a command, and
   another one for a command with metadata. This is why it is mutually defined.
-/

mutual

/- A data type for command -/
inductive Com (c : ZKConfig) where
  -- assign 'e' to variable 'out'
  | assign (out: VarID) (e : Expr c)
  -- conditional statement
  | if_stmt (cond: Cond c) (tb eb :  List (ComWithMD c))
  -- In loop_exp: the loop body is repeated 'se' times.
  -- In loop: the loop body is repeated N times.
  -- We have both loop and loop_exp because in the symbolic execution it is easier to
  -- handle the case where the number of repetitions is a constant, and we can
  -- unroll it. So in principle loop_exp will be evaluated using a corresponding
  -- loop command.
  | loop_exp (rep: SimpleExpr c) (body: List (ComWithMD c))
  | loop (rep : ℕ) (body: List (ComWithMD c))
  -- size is supposed to be a constant expression. Note that during symbolic execution,
  -- 'size' should be a constant expression, a runtime error should be thrown if it is not.
  | new_array (out: VarID) (size: SimpleExpr c)
  -- assign 'arr[idx]' to 'out'
  | read_array (out: VarID) (arr: VarID) (idx: SimpleExpr c)
  -- assign 'value' to 'arr[idx]'
  | write_array (arr: VarID) (idx: SimpleExpr c) (value: SimpleExpr c)
  -- assign copy of 'arr' to 'out'
  | copy_array (out: VarID) (arr: VarID)
  -- assign result of 'fname(args)' to 'outs'
  | func_call (outs: List VarID) (fname: FName) (args: List (SimpleExpr c))
   deriving Repr, BEq, Inhabited

/- Adding metadata to commands -/
inductive ComWithMD (c : ZKConfig) : Type
  | mk (md : CmdMD) (cmd : Com c) : ComWithMD c
  deriving Repr, BEq, Inhabited

end




/- Type are used only for function parameters and return values. For other variables they
   are inferred dynamically. They are needed for functions mainly for symbolic execution,
   since every function is translated separately without considering the calling context.

   We have two types: finite field and array (of finite field).
-/
inductive VarType where
  | ff
  | array (size : ℕ)
  deriving Repr, BEq, Inhabited

/- A function parameter is a pair of variable identifier and its type -/
structure Param where
  name : VarID
  type : VarType
  deriving Repr, BEq, Inhabited

/- A function receives input parameters `params`, executes the whole `body`,
   and returns the values of the variables in `rets`.
-/
inductive Func (c : ZKConfig) where
  | mk (name : FName)
       (params : List Param)
       (rets : List Param)
       (body : List (ComWithMD c)) : Func c
  deriving Repr, BEq, Inhabited

/- A function with metadata -/
inductive FuncWithMD (c : ZKConfig) where
  | mk (md : FuncMD) (func : Func c) : FuncWithMD c
  deriving Repr, BEq, Inhabited

/- A program is a list of functions. Since we forbid recursion, a function
   can only call those that precede it in the list (this should be forced
   in the semantics).
-/
abbrev Prog (c : ZKConfig) := List (FuncWithMD c)

/- A program with metadata. It is the top-level element of a program, which
   includes the whole program and the metadata of the program.
-/
inductive ProgWithMD (c : ZKConfig) where
  | mk (md : ProgMD) (prog : Prog c) : ProgWithMD c
  deriving Repr, BEq, Inhabited

/- Search a function by name. It returns the function and the remaining program,
   which includes the functions that can be called by it.
-/
def fetchFunc {c : ZKConfig}
  (p : Prog c) (fname : FName) : Except String (FuncWithMD c × Prog c) :=
  match p with
  | [] => Except.error s!"Function {fname} not found"
  | funcWMD :: fs =>
    match funcWMD with
    | .mk _ f =>
    match f with
     | .mk name _ _ _ =>
       if name == fname then
         Except.ok (funcWMD, fs)
       else
         fetchFunc fs fname

/- fetchFunc returns a smaller program. It is used to prove termination
   of the functions representing the semantics.
-/
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
   functions that manipulate programs. The only "tricky" parts are thos of loop_exp
   and loop.
-/

mutual

def sizeOfCom {c : ZKConfig} (i : ComWithMD c) : Nat :=
  match i with
  | .mk _ info =>
    match info with
    | .if_stmt _ tb eb =>
        1 + sizeOfComs tb + sizeOfComs eb
    | .loop_exp _ body =>
      1 + sizeOfComs body
    | .loop rep body =>
      1 + rep*(1+sizeOfComs body)
    | .assign _ _ => 1
    | .new_array _ _ => 1
    | .read_array _ _ _ => 1
    | .write_array _ _ _ => 1
    | .copy_array _ _ => 1
    | .func_call _ _ _ => 1

def sizeOfComs {c : ZKConfig} (cmds : List (ComWithMD c)) : Nat :=
match cmds with
| [] => 1
| cmd::rest => 1 + sizeOfCom cmd + sizeOfComs rest

end -- mutual

theorem sizeOfCom_pos {c : ZKConfig} (cmd : ComWithMD c) :
  sizeOfCom cmd > 0 := by
  cases cmd with
  | mk _ info =>
    match info with
    | .if_stmt _ tb eb => simp only [sizeOfCom]; grind
    | .loop_exp _ body => simp only [sizeOfCom]; grind
    | .loop rep body => simp only [sizeOfCom]; grind
    | .assign _ _ => simp only [sizeOfCom]; grind
    | .new_array _ _ => simp only [sizeOfCom]; grind
    | .read_array _ _ _ => simp only [sizeOfCom]; grind
    | .write_array _ _ _ => simp only [sizeOfCom]; grind
    | .copy_array _ _ => simp only [sizeOfCom]; grind
    | .func_call _ _ _ => simp only [sizeOfCom]; grind

theorem sizeOfComs_a_lt_a_plus_b {c : ZKConfig}
  (cmds1 cmds2 : List (ComWithMD c)) :
  sizeOfComs cmds1 < sizeOfComs cmds1 + sizeOfComs cmds2 := by
  cases cmds1 with
  | nil =>
    cases cmds2 with
    | nil => simp only [sizeOfComs]; grind
    | cons cmd2 rest2 => simp only [sizeOfComs]; grind
  | cons cmd1 rest1 =>
    cases cmds2 with
    | nil => simp only [sizeOfComs]; grind
    | cons cmd2 rest2 => simp only [sizeOfComs]; grind





/- Number of loop_exp in a command and list of commands. They are used
   to prove termination of functions that manipulate programs
-/

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

mutual

def numIfstmt {c : ZKConfig} (cmd : ComWithMD c) : Nat :=
  match cmd with
  | .mk _ info =>
    match info with
    | .if_stmt _ tb eb =>
        1 + numIfstmts tb + numIfstmts eb
    | .loop_exp _ body =>
        numIfstmts body
    | .loop _ body =>
      numIfstmts body
    | _ => 0

def numIfstmts {c : ZKConfig} (cmds : List (ComWithMD c)) : Nat :=
  match cmds with
  | [] => 0
  | cmd::rest => numIfstmt cmd + numIfstmts rest

end -- mutual


end Corellzk2smt.Language.Core.Syntax.AST
