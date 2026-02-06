import Llzk.Basic
import Llzk.Language.Core.Parser
import Llzk.Language.Core.Semantics.Basic
import Llzk.Language.Core.Semantics.BigStep

open Llzk.Language.Core.Parser
open Llzk.Language.Core
open Llzk.Language.Core.Semantics
open Llzk.Language.Core.Semantics.BigStep


namespace Llzk.Language.Core.Semantics.Runner

-- let fileHandle ← IO.FS.Handle.mk "test.txt" IO.FS.Mode.write
-- let fileStream := IO.FS.Stream.ofHandle fileHandle
-- (← IO.getStdout)

def print_list {c : ZKConfig} (l : List (String × (FF c))) := do
  match l with
  | [] => pure ()
  | (var,val)::l' =>
    IO.println s!"{var} = {val.val}"
    print_list l'

def print_env {c : ZKConfig} (env : Env c) :=
  print_list env.toList

def run {c : ZKConfig} (prog_str : String) :=
  match parse prog_str with
  | Except.ok prog =>
      match run_prog prog (fun _ => 0) with
      | Except.ok (final_env : Env c) =>
        print_env final_env
      | Except.error e => IO.println s!"Runtime error: {e}"
  | Except.error e => IO.println s!"Parsing error: {e}"

def run_from_file {c : ZKConfig} (filePath : System.FilePath) : IO Unit := do
  let fileContent ← IO.FS.readFile filePath
  @run c fileContent

end Llzk.Language.Core.Semantics.Runner
