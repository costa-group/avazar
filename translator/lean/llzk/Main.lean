import Llzk.Language.Core.Syntax.Printer
import Llzk.Language.Core.Syntax.Parser
import Llzk.Basic
import Llzk.Language.Core.Analysis.Liveness
import Llzk.Language.Core.Analysis.Useless_commands
import Llzk.FFConstraints.SMT
import Llzk.SymExec.BigStep
import Llzk.SymExec.Basic

import Cli

open Llzk.Language.Core.Syntax.Printer
open Llzk.Language.Core.Syntax.Parser
open Llzk.Language.Core.Analysis.Liveness
open Llzk.Language.Core.Analysis.Useless_commands
open Llzk.SymExec.Basic
open Llzk.SymExec.BigStep
open Llzk.FFConstraints.SMT

open Cli


def buildCfg (c : ZKConfig) (p : Parsed) : Except String (SymExecConfig c):= do
  let nextId := 0
  let cmpScm ←
    match p.flag! "comparison_scheme" |>.as! String with
      | "range_of_diff" => pure CmpScm.range_of_diff
      | "normal" => pure CmpScm.normal
      | scm => Except.error s!"Unsupported comparison scheme: {scm}"
  let boolScm ←
    match p.flag! "boolean_scheme" |>.as! String with
      | "range" => pure BoolFFScm.range
      | "mul" => pure BoolFFScm.mul
      | scm => Except.error s!"Unsupported boolean encoding scheme: {scm}"
  let cfg : SymExecConfig c := {
    nextId := nextId,
    cmpScm := cmpScm,
    ffbool := boolScm
  }
  Except.ok cfg

def symExec (c : ZKConfig) (p : Parsed) (inFile : String) (outStream : IO.FS.Stream) : IO Unit := do
     IO.println s!"Parsing {inFile}..."
     let initialState ← ParserM.fromFile inFile
     let (prog,_) ← StateT.run (@parseProg c []) initialState
     IO.println s!"Adding liveness information..."
     let progWithLiveness := addLivenessProg prog
     let progToExec ←
       if p.hasFlag "removeuseless" then
         IO.println s!"Removing useless commands..."
         pure (removeUselessProg progWithLiveness)
       else
         pure progWithLiveness
     IO.println s!"Performing symbolic execution..."
     let mainFunc := p.flag! "main" |>.as! String
     let secfg ← match buildCfg c p with
       | Except.ok cfg => pure cfg
       | Except.error e =>
           IO.println s!"Error building symbolic execution configuration: {e}"
           return
     match @seExecProg c secfg progToExec mainFunc with
     | Except.error e =>
         IO.println s!"Error during symbolic execution: {e}"
     | Except.ok constraints =>
         match p.flag! "smt2_format" |>.as! String with
         | "smtlib" =>
            IO.println s!"Generating encoding using SMT-LIB format..."
            IO.println s!""
            @printConstraintSystem c outStream constraints
            outStream.flush
         | "json" =>
            IO.println s!"Generating encoding using JSON format..."
            IO.println s!""
            @printConstraintSystem_asJSON c outStream constraints
            outStream.flush
         | fmt =>
            IO.println s!"Unsupported SMT output format: {fmt}."

/- Pretty printing of a given program -/
def prettyPrinting
     (c : ZKConfig) (p : Parsed) (inFile : String) (outStream : IO.FS.Stream)
     : IO Unit := do
     let fc : FormatConfig := {
       indentSize := 2,
       showLiveness := p.hasFlag "showliveness"
     }
     IO.println s!"Parsing {inFile}..."
     let initialState ← ParserM.fromFile inFile
     let (prog,_) ← StateT.run (@parseProg c []) initialState
     let progWithLiveness := addLivenessProg prog
     let progToPrint ←
       if p.hasFlag "removeuseless" then
         IO.println s!"Removing useless commands..."
         pure (removeUselessProg progWithLiveness)
       else
         pure progWithLiveness
     IO.println s!"Pretty printing the input program..."
     IO.println s!""
     printProg fc progToPrint outStream
     outStream.flush


def getZKConfig (p : Parsed) : IO ZKConfig := do
  let zkConfigStr := p.flag! "zkconfig" |>.as! String
  match zkConfigStr with
  | "f11" => return F11
  | "f5" => return F5
  | "g64" => return goldilocks64
  | _ => panic! s!"Unsupported ZKConfig: {zkConfigStr}"

/- Main entry point for the command line interface -/
def runLlzkCmd (p : Parsed) : IO UInt32 := do
  let zkConfig ← getZKConfig p
  let input : String := p.positionalArg! "input" |>.as! String
  let outStream ← if p.hasFlag "output" then
    let output : String := p.flag! "output" |>.as! String
    let h ← IO.FS.Handle.mk output IO.FS.Mode.write
    pure (IO.FS.Stream.ofHandle h)
  else
    IO.getStdout
  if p.hasFlag "prettyprint" then
     prettyPrinting zkConfig p input outStream
  else if p.hasFlag "symbolicexec" then
     symExec zkConfig p input outStream
  else
     IO.println "No action specified. Use --help for more information."
  return 0


/- Commandline options -/
def llzkCmd : Cmd := `[Cli|
  llzkCmd VIA runLlzkCmd; ["0.0.1"]
  "Translator for Core Llzk programs."
  FLAGS:
    sl, showliveness;        "Show liveness information for each command."
    ru, removeuseless;       "Show liveness information and emove useless commands from the program."
    pp, prettyprint;         "Parse and pretty-print the input program."
    se, symbolicexec;        "Perform symbolic execution of the input program."
    zk, zkconfig : String;   "The ZKConfig to use for symbolic execution (f11,g64). Default is f11."
    m, main : String;        "The main function for symbolic execution (default: main)"
    o, output : String;      "The output file. If not provided, stdout is used."
    smt2, smt2_format : String;  "The format of the SMT output (smtlib,json). Default is smtlib."
    cmpscm, comparison_scheme : String; "Encoding of signed comparison (range_of_diff, normal). \
    Default is range_of_diff."
    boolscm, boolean_scheme : String; "Encoding of boolean variables for bits (range, mul). \
    Default is range."
  ARGS:
    input : String;      "The input program"
  EXTENSIONS:
    defaultValues! #[("zkconfig", "f11"),
                     ("main", "main"),
                     ("smt2_format", "smtlib"),
                     ("comparison_scheme", "range_of_diff"),
                     ("boolean_scheme", "range")
                    ]
]


/-- Main entry point for symbolic execution from command line -/
def main (args : List String) : IO UInt32 := do
  llzkCmd.validate args
