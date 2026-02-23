import Llzk.Basic
import Llzk.Language.Core.Syntax.AST


namespace Llzk.Language.Core.Syntax.Printer

open Llzk.Language.Core.Syntax.AST



/- The following few functions are used to convert a program to a string
   using pretty printing. It is registered as ToString instance for Prog
   so that it can be called implicitly
-/
def getIndent (level : Nat) (spl : Nat := 2) : String :=
  String.ofList (List.replicate (level * spl) ' ')

def formatSexpr {c : ZKConfig} (s : SimpleExpr c) : String :=
  match s with
  | .var varName => s!"{varName}"
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
  let typeStr := match p.type with
                 | VarType.ff => "ff"
                 | VarType.array size => s!"arr<{size}>"
  s!"{p.name}:{typeStr}"

-- register ToString instance for Param
instance : ToString Param where
  toString p := formatParam p

def formatParams (ps : List Param) : String :=
  String.intercalate ", " (ps.map toString)

-- register ToString instance for (List Param)
instance : ToString (List Param) where
  toString ps := formatParams ps

mutual

def formatCom {c : ZKConfig} (i : ComWithMD c) (level : Nat) (sp : String) : String :=
  match i with
  | .mk _ info =>
      match info with
      | .skip => s!"skip"
      | .assign out e => s!"{out} := {e}"
      | .if_stmt cond tb eb =>
          let tbStr := formatBody tb (level + 1)
          let ebStr := formatBody eb (level + 1)
          s!"if ({cond}) " ++ "{\n" ++ s!"{tbStr}" ++
          s!"{sp}} else " ++ "{\n" ++ s!"{ebStr}" ++ s!"{sp}}"
      | .loop_exp rep body =>
          let bodyStr := formatBody body (level + 1)
          s!"repeat {rep} " ++ "{\n" ++ s!"{bodyStr}" ++ s!"{sp}}"
      | .loop rep body =>
          let bodyStr := formatBody body (level + 1)
          s!"for {rep} " ++ "{\n" ++ s!"{bodyStr}" ++ s!"{sp}}"
      | .new_array out size =>
         s!"array.new {size} {out}"
      | .read_array out arr idx =>
         s!"array.read {arr}[{idx}] {out}"
      | .write_array arr idx value =>
          s!"array.write {value} {arr}[{idx}]"
      | .copy_array out arr =>
         s!"array.copy {arr} {out}"
      | .func_call outs fname args =>
         let outsStr := String.intercalate ", " (outs.map (fun v => s!"{v}"))
         let argsStr := String.intercalate ", " (args.map toString)
         if (outs == []) then
            s!"call {fname} ({argsStr})"
         else
            s!"call {fname} ({argsStr}) to {outsStr}"

def formatBody {c : ZKConfig} (p : List (ComWithMD c)) (level : Nat) : String :=
  let sp := getIndent level
  match p with
  | [] => ""
  | cmd::cmds =>
      let cmdStr := formatCom cmd level sp
      let restStr := formatBody cmds level
      s!"{sp}{cmdStr}\n{restStr}"

end -- mutual

def formatFunction {c : ZKConfig} (f : FuncWithMD c) : String :=
  match f with
  | .mk _ func =>
    match func with
    | .mk name params rets body =>
      let bodyStr := formatBody body 1
      if (rets == []) then
        s!"func {name}({params}) " ++ "{\n" ++ s!"{bodyStr}" ++ "}\n"
      else
        s!"func {name}({params}) : {rets} " ++ "{\n" ++ s!"{bodyStr}" ++ "}\n"

-- register ToString instance for Function
instance {c : ZKConfig} : ToString (FuncWithMD c) where
  toString f := formatFunction f

def formatProg {c : ZKConfig} (p : ProgWithMD c) : String :=
  match p with
  | .mk _ fs =>
      let funcStrs := fs.reverse.map toString
      String.intercalate "\n\n" funcStrs

-- register ToString instance for Program
instance {c : ZKConfig} : ToString (ProgWithMD c) where
  toString p := formatProg p


structure FormatConfig where
  indentSize : Nat := 2
  showLiveness : Bool := false
  deriving Repr, BEq, Inhabited


section Printing

variable (fc : FormatConfig)

mutual

def printCom {c : ZKConfig}
    (h : IO.FS.Stream) (i : ComWithMD c) (level : Nat) (sp : String) : IO Unit := do
  match i with
  | .mk _md info =>
      match info with
      | .skip => h.putStr s!"skip"
      | .assign out e => h.putStr s!"{out} = {e}"
      | .if_stmt cond tb eb =>
          h.putStr s!"if ({cond})"
          h.putStrLn " {"
          printBody h tb (level + 1)
          h.putStr sp
          h.putStrLn "} else {"
          printBody h eb (level + 1)
          h.putStr sp
          h.putStr "}"
      | .loop_exp rep body =>
          h.putStr s!"repeat {rep}"
          h.putStrLn " {"
          printBody h body (level + 1)
          h.putStr sp
          h.putStr "}"
      | .loop rep body =>
          h.putStr s!"repeat {rep}"
          h.putStrLn " {"
          printBody h body (level + 1)
          h.putStr sp
          h.putStr "}"
      | .new_array out size =>
          h.putStr s!"array.new {size} {out}"
      | .read_array out arr idx =>
          h.putStr s!"array.read {arr}[{idx}] {out}"
      | .write_array arr idx value =>
          h.putStr s!"array.write {value} {arr}[{idx}]"
      | .copy_array out arr =>
          h.putStr s!"array.copy {arr} {out}"
      | .func_call outs fname args =>
          let outsStr := String.intercalate ", " (outs.map (fun v => s!"{v}"))
          let argsStr := String.intercalate ", " (args.map toString)
          if (outs == []) then
            h.putStr s!"call {fname} ({argsStr})"
          else
            h.putStr s!"call {fname} ({argsStr}) to {outsStr}"

def printBody {c : ZKConfig}
  (h : IO.FS.Stream) (p : List (ComWithMD c)) (level : Nat) : IO Unit := do
  let sp := getIndent level fc.indentSize
  match p with
  | [] => pure ()
  | cmd::cmds =>
      match cmd with
      | .mk md _ =>
        if fc.showLiveness then
          h.putStr s!"{sp}"
          h.putStrLn s!"# live_in={md.liveness.live_in}, live_out={md.liveness.live_out}"
        h.putStr s!"{sp}"
        printCom h cmd level sp
        h.putStrLn ""
        printBody h cmds level

end -- mutual

def printFunction {c : ZKConfig}
    (h : IO.FS.Stream) (f : FuncWithMD c) : IO Unit := do
  match f with
  | .mk md func =>
    match func with
    | .mk name params rets body =>
      if fc.showLiveness then
        h.putStrLn s!"# live_in={md.liveness.live_in}, live_out={md.liveness.live_out}"
      if (rets == []) then
        h.putStr s!"func {name}({params})"
      else
        h.putStr s!"func {name}({params}) : {rets}"
      h.putStrLn " {"
      printBody fc h body 1
      h.putStrLn "}"

def printProg {c : ZKConfig} (p : ProgWithMD c)
    (h : IO.FS.Stream) : IO Unit := do
    match p with
    | .mk _ fs =>
      for f in fs.reverse do
        printFunction fc h f
        h.putStrLn ""

end Printing -- section

end Llzk.Language.Core.Syntax.Printer
