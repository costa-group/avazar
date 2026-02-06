import Llzk.SymEx.Runner

open Llzk.SymEx.Runner

/-- Main entry point for symbolic execution from command line -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [inFile,outFile] =>
    IO.FS.withFile outFile IO.FS.Mode.write fun outHandle => do
      let outStream := IO.FS.Stream.ofHandle outHandle
      @run_sym_exec_from_file F11 inFile outStream false
      outHandle.flush
      return 0
  | _ =>
    IO.println "Usage: program <input_file> <output_file>"
    return 1
