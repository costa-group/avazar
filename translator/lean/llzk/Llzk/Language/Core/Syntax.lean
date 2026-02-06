import Llzk.Basic
import Init.Data.BitVec

/- This is a namespace for the core language, to disnguish it from future
   extensions such as supporting arrays (in case they incorporated via program
   transfromations, otherwise ... ) -/

namespace Llzk.Language.Core

/- A structure for command information. It will be mainly used to related
   instructions to the source code, like line numbers, etc. More fields
   can be added later
-/
structure SrcInfo where
  line : ℕ
  deriving Repr, BEq, Inhabited

/- A structure for command metadata. More fields can be added later -/
structure CmdMetaData where
  src_info : SrcInfo
  deriving Repr, BEq, Inhabited

/- A type for program variable -/
abbrev ProgVarID := String

/- A simple Expression is either a variable or a field value -/
def SimpleExpr (c : ZKConfig) := ProgVarID ⊕ (FF c)
  deriving Repr, BEq, Inhabited

/- A data type for command -/
inductive Com (c : ZKConfig) where
  -- do nothing
  | skip   (meta_data: CmdMetaData)
  -- out := a1 + a2
  | add    (meta_data: CmdMetaData) (out: ProgVarID) (a1 a2 : SimpleExpr c)
  -- out := a1 - a2
  | sub    (meta_data: CmdMetaData) (out: ProgVarID) (a1 a2 : SimpleExpr c)
  -- out := a1 * a2
  | mul    (meta_data: CmdMetaData) (out: ProgVarID) (a1 a2 : SimpleExpr c)
  -- out := a1 / a2
  | div    (meta_data: CmdMetaData) (out: ProgVarID) (a1 a2 : SimpleExpr c)
  -- out := a << bits (should `a` be only variable in shl?)
  | shl    (meta_data: CmdMetaData) (out: ProgVarID) (a : SimpleExpr c) (bits : ℕ)
  -- out := a
  | assign (meta_data: CmdMetaData) (out: ProgVarID) (a : SimpleExpr c)
  -- if (cond) {tb} else {eb}
  | ifst   (meta_data: CmdMetaData) (cond: ProgVarID) (tb eb :  List (Com c))
  deriving Repr, BEq, Inhabited

/- A program is a list of commands -/
abbrev Prog (c : ZKConfig) := List (Com c)


/- The following few functions are used to convert a program to a string
   using pretty printing. It is registered as ToString instance for Prog
   so that it can be called implicitly
-/
def get_indent (level : Nat) : String :=
  String.ofList (List.replicate (level * 2) ' ')

def format_expr {c : ZKConfig} : SimpleExpr c → String
  | .inl varName => varName
  | .inr val => s!"{repr val}" -- Or toString if FF has it

mutual
  def format_prog {c : ZKConfig} (p : Prog c) (level : Nat) : String :=
    match p with
    | [] => ""
    | cmd::cmds =>
        let cmdStr := format_single_com cmd level
        let restStr := format_prog cmds level
        s!"{cmdStr}\n{restStr}"

  def format_single_com {c : ZKConfig} (cmd : Com c) (level : Nat) : String :=
    let sp := get_indent level
    match cmd with
    | .skip _ => s!"{sp}skip"
    | .assign _ out a => s!"{sp}{out} := {format_expr a}"
    | .add _ out a1 a2 => s!"{sp}{out} := {format_expr a1} + {format_expr a2}"
    | .sub _ out a1 a2 => s!"{sp}{out} := {format_expr a1} - {format_expr a2}"
    | .mul _ out a1 a2 => s!"{sp}{out} := {format_expr a1} * {format_expr a2}"
    | .div _ out a1 a2 => s!"{sp}{out} := {format_expr a1} / {format_expr a2}"
    | .shl _ out a bits => s!"{sp}{out} := {format_expr a} << {bits}"
    | .ifst _ cond tb eb =>
        let bodyIndent := level + 1
       -- We break the string to safely insert the curly braces
        s!"{sp}if ({cond}) " ++ "{\n" ++
        s!"{format_prog tb bodyIndent}" ++
        s!"{sp}" ++ "} else {" ++ "\n" ++
        s!"{format_prog eb bodyIndent}" ++
        s!"{sp}}"
end -- mutual

-- register ToString instance for Com
instance {c : ZKConfig} : ToString (Prog c) where
  toString p := format_prog p 0



/- Directly print to a stream (could be a file or stdout). Should be better
   performance-wise than going through ToString first.
-/
mutual
  def print_prog {c : ZKConfig} (h : IO.FS.Stream) (p : Prog c) (level : Nat) : IO Unit :=
    match p with
    | [] => h.flush
    | cmd::cmds => do
        print_single_com h cmd level
        print_prog h cmds level

  def print_single_com {c : ZKConfig} (h : IO.FS.Stream) (cmd : Com c) (level : Nat) : IO Unit := do
    let sp := get_indent level
    match cmd with
    | .skip _ => h.putStrLn s!"{sp}skip"
    | .assign _ out a => h.putStrLn s!"{sp}{out} := {format_expr a}"
    | .add _ out a1 a2 => h.putStrLn s!"{sp}{out} := {format_expr a1} + {format_expr a2}"
    | .sub _ out a1 a2 => h.putStrLn s!"{sp}{out} := {format_expr a1} - {format_expr a2}"
    | .mul _ out a1 a2 => h.putStrLn s!"{sp}{out} := {format_expr a1} * {format_expr a2}"
    | .div _ out a1 a2 => h.putStrLn s!"{sp}{out} := {format_expr a1} / {format_expr a2}"
    | .shl _ out a bits => h.putStrLn s!"{sp}{out} := {format_expr a} << {bits}"
    | .ifst _ cond tb eb =>
        let bodyIndent := level + 1
       -- We break the string to safely insert the curly braces
        h.putStr s!"{sp}if ({cond}) "
        h.putStrLn "{"
        print_prog h tb bodyIndent
        h.putStr s!"{sp}"
        h.putStrLn "} else {"
        print_prog h eb bodyIndent
        h.putStrLn s!"{sp}}"
end -- mutual


/- Accessing the metadata of a command -/
def get_meta_data {c : ZKConfig} (cmd : Com c) : CmdMetaData :=
  match cmd with
  | Com.skip md => md
  | Com.add md _ _ _ => md
  | Com.sub md _ _ _ => md
  | Com.mul md _ _ _ => md
  | Com.div md _ _ _ => md
  | Com.shl md _ _ _ => md
  | Com.assign md _ _ => md
  | Com.ifst md _ _ _ => md

/- A type for a set of program variables -/
abbrev ProgVarIDSet := Std.TreeSet ProgVarID

/- Empty set for ProgVarIDSet -/
def emptyProgVarIDSet : ProgVarIDSet := Std.TreeSet.empty

/- The following functions are used to collect the program variables
   into a set. This is needed becuase for now we do not require variables
   to be declared before they are used.
-/
def collect_prog_vars_step {c : ZKConfig}
  (out : String) (as : List (SimpleExpr c)) (vars_in : ProgVarIDSet) : ProgVarIDSet :=
  let def_in' := vars_in.insert out
  as.foldl (init := def_in') (fun acc x =>
                                match x with
                                | .inl v => acc.insert v
                                | .inr _  => acc)

mutual
  def collect_prog_vars' {c : ZKConfig} (p : Prog c) (vars_in : ProgVarIDSet) : ProgVarIDSet :=
    match p with
    | [] => vars_in
    | cmd::cmds =>
        let vars_after_cmd := collect_prog_vars_cmd cmd vars_in
        collect_prog_vars' cmds vars_after_cmd

  def collect_prog_vars_cmd {c : ZKConfig} (cmd : Com c) (vars_in : ProgVarIDSet) : ProgVarIDSet :=
    match cmd with
    | Com.skip _ => vars_in
    | Com.add _ out a1 a2 =>
        collect_prog_vars_step out [a1,a2] vars_in
    | Com.sub _ out a1 a2 =>
        collect_prog_vars_step out [a1,a2] vars_in
    | Com.mul _ out a1 a2 =>
        collect_prog_vars_step out [a1,a2] vars_in
    | Com.div _ out a1 a2 =>
        collect_prog_vars_step out [a1,a2] vars_in
    | Com.shl _ out a _ =>
      collect_prog_vars_step out [a] vars_in
    | Com.assign _ out a =>
      collect_prog_vars_step out [a] vars_in
    | Com.ifst _ cond tb eb =>
        let vars_in' := vars_in.insert cond
        let tb_out := collect_prog_vars' tb vars_in'
        let eb_out := collect_prog_vars' eb vars_in'
        tb_out.union eb_out
end -- mutual

def collect_prog_vars {c : ZKConfig} (p : Prog c) : ProgVarIDSet :=
  collect_prog_vars' p emptyProgVarIDSet


/- The following functions can be used to add unique identifiers to
   commands. In principle, at the end this should be done during
   parsing and not through these functions.
-/
mutual
  def add_ids' {c : ZKConfig} (prog : Prog c) (id : ℕ) : (Prog c) × ℕ :=
    match prog with
    | [] => ([], id)
    | cmd::cmds =>
        let (cmd', id') := add_ids_cmd cmd id
        let (cmds', id'') := add_ids' cmds id'
        (cmd'::cmds', id'')

  def add_ids_cmd {c : ZKConfig} (cmd : Com c) (id : ℕ) : (Com c) × ℕ :=
    match cmd with
    | Com.skip md => (Com.skip { md with src_info := { line := id } }, id + 1)
    | Com.add md out a1 a2 =>
        (Com.add { md with src_info := { line := id } } out a1 a2, id + 1)
    | Com.sub md out a1 a2 =>
        (Com.sub { md with src_info := { line := id } } out a1 a2, id + 1)
    | Com.mul md out a1 a2 =>
        (Com.mul { md with src_info := { line := id } } out a1 a2, id + 1)
    | Com.div md out a1 a2 =>
        (Com.div { md with src_info := { line := id } } out a1 a2, id + 1)
    | Com.shl md out a bits =>
        (Com.shl { md with src_info := { line := id } } out a bits, id + 1)
    | Com.assign md out a =>
        (Com.assign { md with src_info := { line := id } } out a, id + 1)
    | Com.ifst md cond tb eb =>
        let (tb' , id') := add_ids' tb (id+1)
        let (eb' , id'') := add_ids' eb id'
        (Com.ifst { md with src_info := { line := id } } cond tb' eb', id'')
end -- mutual

def add_ids {c : ZKConfig} (p : Prog c) : Prog c :=
  let (p',_) :=  add_ids' p 0
  p'

end Core

end Llzk.Language
