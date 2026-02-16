import Llzk.Language.Core.Syntax.AST
import Llzk.Language.Core.Syntax.Parser
import Llzk.Basic

open Llzk.Language.Core.Syntax.AST
open Llzk.Language.Core.Syntax.Parser


/-- Main entry point for symbolic execution from command line -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [inFile,outFile] =>
    IO.FS.withFile outFile IO.FS.Mode.write fun outHandle => do
      let outStream := IO.FS.Stream.ofHandle outHandle
      IO.println s!"Parsing program {inFile}..."
      let initialState ← ParserM.fromFile inFile
      let (prog,_) ← StateT.run (@parseProg F11 []) initialState
      IO.println s!"Printing program into {outFile}..."
      @printProg F11 outStream prog.reverse
      outStream.flush
      return 0
  | _ =>
    IO.println "Usage: program <input_file> <output_file>"
    return 1
