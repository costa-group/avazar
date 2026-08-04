import Corellzk2smt.Language.Core.Syntax.Printer
import Corellzk2smt.Language.Core.Syntax.Parser
import Corellzk2smt.Basic
import Corellzk2smt.Config
import Corellzk2smt.Language.Core.Analysis.Useless_commands
import Corellzk2smt.FFConstraints.SMT
import Corellzk2smt.SymExec.BigStep
import Cli

open Corellzk2smt.Language.Core.Syntax.Printer
open Corellzk2smt.Language.Core.Syntax.Parser
open Corellzk2smt.Language.Core.Analysis.Useless_commands
open Corellzk2smt.Config
open Corellzk2smt.FFConstraints.SMT
open Corellzk2smt.SymExec.BigStep

open Cli

/- Build the ZKConfig depending on the choosen prime -/
def buildZKConfig (p : Parsed) : IO ZKConfig := do
  let zkConfigStr := p.flag! "zkconfig" |>.as! String
  match zkConfigStr with
  | "f11" => return F11
  | "f5" => return F5
  | "g64" => return goldilocks64
  | _ => panic! s!"Unsupported ZKConfig: {zkConfigStr}"

/- Build the GlobalConfig configuration that we will pass everywhere -/
def buildGlobalConfig (c : ZKConfig) (_p : Parsed) : IO (GlobalConfig c) := do
  let gconf : GlobalConfig c := default
  pure { gconf with prog_printer.show_liveness := _p.hasFlag "showliveness" }

/- Pretty printing of a given program -/
def prettyPrinting
  (c : ZKConfig) (gconf : GlobalConfig c)
  (_p : Parsed) (inFile : String) (outStream : IO.FS.Stream)
     : IO Unit := do
     IO.println s!"Parsing {inFile}..."
     let initialState ← ParserM.fromFile gconf inFile
     let (prog,_) ← StateT.run (@parseProg c []) initialState
     IO.println s!"Pretty printing the input program..."
     IO.println s!""
     printProg gconf prog outStream
     outStream.flush


/- Symbolic execution -/
def symExec (c : ZKConfig) (gconf : GlobalConfig c) (p : Parsed) (inFile : String) (outStream : IO.FS.Stream) : IO Unit := do
     IO.println s!"Parsing {inFile}..."
     let initialState ← ParserM.fromFile gconf inFile
     let (prog,_) ← StateT.run (@parseProg c []) initialState
     -- removeUselessProg computes its own liveness information from scratch
     -- (it never reads pre-existing metadata), so calling addLivenessProg
     -- first would be redundant, wasted work when -ru is set.
     let progToExec ←
       if p.hasFlag "removeuseless" then
         IO.println s!"Removing useless commands..."
         pure (removeUselessProg prog)
       else
         pure prog
     IO.println s!"Performing symbolic execution..."
     let mainFunc := p.flag! "main" |>.as! String
     match @seExecProg c gconf progToExec mainFunc with
     | Except.error e =>
         IO.println s!"Error during symbolic execution: {e}"
     | Except.ok constraints =>
         match p.flag! "smt2_format" |>.as! String with
         | "smtlib" =>
            IO.println s!"Generating encoding using SMT-LIB format..."
            IO.println s!""
            @printConstraintSystem c gconf outStream constraints
            outStream.flush
         | "json" =>
            IO.println s!"Generating encoding using JSON format..."
            IO.println s!""
            @printConstraintSystem_asJSON c gconf outStream constraints
            outStream.flush
         | fmt =>
            IO.println s!"Unsupported SMT output format: {fmt}."



/- Main entry point for the command line interface -/
def corellzk2smtRunner (p : Parsed) : IO UInt32 := do
  --
  -- Build the ZKConfig
  let zkConfig ← buildZKConfig p
  --
  -- Build the GlobalConfig
  let gconf ← buildGlobalConfig zkConfig p
  --
  -- We have to have an input file
  let input : String := p.positionalArg! "input" |>.as! String
  --
  -- Output wither goes to a file, or to the standard output if not output file is specified
  let outStream ← if p.hasFlag "output" then
    let output : String := p.flag! "output" |>.as! String
    let h ← IO.FS.Handle.mk output IO.FS.Mode.write
    pure (IO.FS.Stream.ofHandle h)
  else
    IO.getStdout
  --
  -- Now we can do the action specified by the user
  if p.hasFlag "prettyprint" then
     prettyPrinting zkConfig gconf p input outStream
  else if p.hasFlag "symbolicexec" then
     symExec zkConfig gconf p input outStream
  else
     IO.println "No action specified. Use --help for more information."
  return 0


/- Commandline options -/
def corellzk2smtCli : Cmd := `[Cli|
  corellzk2smtCli VIA corellzk2smtRunner; ["0.0.1"]
  "Translator for Core Llzk programs."
  FLAGS:
    pp, prettyprint;         "Parse and pretty print the input program."
    se, symbolicexec;        "Perform symbolic execution of the input program."
    zk, zkconfig : String;   "The ZKConfig to use for symbolic execution (f11,g64). Default is f11."
    m, main : String;        "The main function for symbolic execution (default: main)"
    o, output : String;      "The output file. If not provided, the standard output is used."
    smt2, smt2_format : String;  "The format of the SMT output (smtlib,json). Default is smtlib."
    boolscm, boolean_scheme : String; "Encoding of boolean variables for bits (range, mul). \
    Default is range."
  ARGS:
    input : String;      "The input program"
  EXTENSIONS:
    defaultValues! #[("zkconfig", "f11"),
                     ("main", "main"),
                     ("smt2_format", "smtlib"),
                     ("boolean_scheme", "range")
                    ]
]


/-- Main entry point for symbolic execution from command line -/
def main (args : List String) : IO UInt32 := do
  corellzk2smtCli.validate args
