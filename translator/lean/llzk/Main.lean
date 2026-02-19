import Llzk.Language.Core.Syntax.AST
import Llzk.Language.Core.Syntax.Parser
import Llzk.Basic
import Llzk.Language.Core.Analysis.Liveness

import Cli

open Llzk.Language.Core.Syntax.AST
open Llzk.Language.Core.Syntax.Parser
open Llzk.Language.Core.Analysis.Liveness

open Cli



def prettyPrinting (inFile : String) (outStream : IO.FS.Stream) : IO Unit := do
     IO.println s!"Parsing program {inFile}..."
     let initialState ← ParserM.fromFile inFile
     let (prog,_) ← StateT.run (@parseProg F11 []) initialState
     let progWithLiveness := addLivenessProg prog
     IO.println s!"Printing program ..."
     @printProg F11 outStream progWithLiveness
     outStream.flush



def runLlzkCmd (p : Parsed) : IO UInt32 := do
  let input : String := p.positionalArg! "input" |>.as! String
  let outStream ← if p.hasFlag "output" then
    let output : String := p.flag! "output" |>.as! String
    let h ← IO.FS.Handle.mk output IO.FS.Mode.write
    pure (IO.FS.Stream.ofHandle h)
  else
    IO.getStdout
  prettyPrinting input outStream
  return 0



def llzkCmd : Cmd := `[Cli|
  llzkCmd VIA runLlzkCmd; ["0.0.1"]
  "Translator for Core Llzk programs."
  FLAGS:
    pp, prettyprinting;         "Parse and pretty-print the input program."
    o, output : String;         "The output file. If not provided, stdout is used."
  ARGS:
    input : String;      "The input program"
]


/-- Main entry point for symbolic execution from command line -/
def main (args : List String) : IO UInt32 := do
  llzkCmd.validate args
