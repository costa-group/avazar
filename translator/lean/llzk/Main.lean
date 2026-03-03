import Llzk.Language.Core.Syntax.Printer
import Llzk.Language.Core.Syntax.Parser
import Llzk.Basic
import Llzk.Language.Core.Analysis.Liveness
import Llzk.FFConstraints.SMT
import Llzk.SymExec.BigStep

import Cli

open Llzk.Language.Core.Syntax.Printer
open Llzk.Language.Core.Syntax.Parser
open Llzk.Language.Core.Analysis.Liveness
open Llzk.SymExec.BigStep
open Llzk.FFConstraints.SMT

open Cli

def symExec (_p : Parsed) (inFile : String) (outStream : IO.FS.Stream) : IO Unit := do
     IO.println s!"Parsing {inFile}..."
     let initialState ← ParserM.fromFile inFile
     let (prog,_) ← StateT.run (@parseProg F11 []) initialState
     IO.println s!"Adding liveness information..."
     let progWithLiveness := addLivenessProg prog
     IO.println s!"Performing symbolic execution..."
     match @seExecProg F11 {} progWithLiveness "main" with
     | Except.error e =>
         IO.println s!"Error during symbolic execution: {e}"
     | Except.ok constraints =>
       IO.println s!"Generating SMT constraints..."
       IO.println s!""
       @printConstraintSystem F11 outStream constraints
       outStream.flush

/- Pretty printing of a given program -/
def prettyPrinting (p : Parsed) (inFile : String) (outStream : IO.FS.Stream) : IO Unit := do
     let fc : FormatConfig := {
       indentSize := 2,
       showLiveness := p.hasFlag "showliveness"
     }
     IO.println s!"Parsing {inFile}..."
     let initialState ← ParserM.fromFile inFile
     let (prog,_) ← StateT.run (@parseProg F11 []) initialState
     let progWithLiveness := addLivenessProg prog
     IO.println s!"Pretty printing the input program..."
     IO.println s!""
     @printProg fc F11 progWithLiveness outStream
     outStream.flush


/- Main entry point for the command line interface -/
def runLlzkCmd (p : Parsed) : IO UInt32 := do
  let input : String := p.positionalArg! "input" |>.as! String
  let outStream ← if p.hasFlag "output" then
    let output : String := p.flag! "output" |>.as! String
    let h ← IO.FS.Handle.mk output IO.FS.Mode.write
    pure (IO.FS.Stream.ofHandle h)
  else
    IO.getStdout
  if p.hasFlag "prettyprint" then
     prettyPrinting p input outStream
  else if p.hasFlag "symbolicexec" then
     symExec p input outStream
  else
     IO.println "No action specified. Use --help for more information."
  return 0


/- Commandline options -/
def llzkCmd : Cmd := `[Cli|
  llzkCmd VIA runLlzkCmd; ["0.0.1"]
  "Translator for Core Llzk programs."
  FLAGS:
    sl, showliveness;        "Show liveness information for each command."
    pp, prettyprint;         "Parse and pretty-print the input program."
    se, symbolicexec;        "Perform symbolic execution of the input program."
    o, output : String;      "The output file. If not provided, stdout is used."
  ARGS:
    input : String;      "The input program"
]


/-- Main entry point for symbolic execution from command line -/
def main (args : List String) : IO UInt32 := do
  llzkCmd.validate args
