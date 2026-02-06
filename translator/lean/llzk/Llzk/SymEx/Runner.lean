import Llzk.Language.Core.Syntax
import Llzk.Language.Core.Parser
import Llzk.SymEx.FFConstraints
import Llzk.SymEx.BigStep

open Llzk.Language.Core.Parser
open Llzk.SymEx.FFConstraints
open Llzk.SymEx.BigStep

namespace Llzk.SymEx.Runner

/- Symbolic execution runners -/

def run_sym_exec {c : ZKConfig} (prog_str : String) (out_stream : IO.FS.Stream)
  (raw : Bool) : IO Unit := do
  match parse prog_str with
  | Except.ok prog =>
      match sym_exec_prog prog  with
      | Except.ok (sst : SymState c) =>
        if raw then
          out_stream.putStrLn s!"{(repr sst.f)}"
        else
          print_smt2 (collect_vars sst.f) sst.f out_stream
      | Except.error e => IO.println s!"Symbolic execution error: {e}"
  | Except.error e => IO.println s!"Parsing error: {e}"

def run_sym_exec_from_file {c : ZKConfig}
  (filePath : System.FilePath) (out_stream : IO.FS.Stream) (raw : Bool) : IO Unit := do
  let fileContent ← IO.FS.readFile filePath
  @run_sym_exec c fileContent out_stream raw

end Llzk.SymEx.Runner
