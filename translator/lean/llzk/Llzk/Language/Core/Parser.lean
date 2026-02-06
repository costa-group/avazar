import Llzk.Basic
import Llzk.Language.Core.Syntax


/- A parser for the core language.

   It is very simple, just to do some testing. It assumes the input
   program is given as a string. Later should be replaced by one that
   is based on a tokenizer, etc.
-/

namespace Llzk.Language.Core.Parser


open Llzk.Language.Core

/- Parser core -/


/- The state of the parser. It contains the input string
   and a counter for generating fresh ids.
-/
structure ParserState where
  input : Substring.Raw
  counter : ℕ
  deriving Repr, Inhabited

/- The parser type. It uses a state transformer monad with a state of type `ParserState`
   and the possibility of failure with an error message (Except String).
-/
abbrev ParserT (α : Type) := StateT ParserState (Except String) α

/- Tries parser `p`. If it fails, runs `q` -/
def or_else {α : Type} (p : ParserT α) (q : ParserT α) : ParserT α := do
  let s ← get
  match (StateT.run p s) with
  | Except.ok (res, newState) =>
      set newState
      return res
  | Except.error _ =>
      q

/- Check if input is empty -/
def is_done (s : Substring.Raw) : Bool :=
  s.startPos == s.stopPos

/- Helper: Peek at the first char without moving cursor -/
def peek : ParserT Char := do
  let s ← get
  if is_done s.input then throw "Unexpected EOF"
  else pure (s.input.get 0)

/- Helper: Move cursor forward by n chars -/
def advance (n : ℕ := 1) : ParserT Unit := do
  let s ← get
  if is_done s.input then throw "Unexpected EOF"
  else set { s with input := s.input.drop n }

/- Helper: Parse a character satisfying a predicate -/
def satisfy (p : Char → Bool) : ParserT Char := do
  let c ← peek
  if p c then
    advance 1
    pure c
  else
    throw s!"Unexpected '{c}'"

/- Parse zero or more units using `p` -/
partial def many (p : ParserT α) : ParserT (List α) := do
  let s ← get
  try
    let x ← p
    let xs ← many p
    pure (x :: xs)
  catch _ =>
    set s -- Reset state on failure (Backtrack local only)
    pure []

/- Parse one or more units using `p` -/
def many1 (p : ParserT α) : ParserT (List α) := do
  let x ← p
  let xs ← many p
  pure (x :: xs)

/- Kind of a grammar for the core language -/

/- A comment -/
def comment : ParserT Unit := do
  _ ← satisfy (· == '#')
  _ ← many (satisfy (· != '\n')) -- Consume everything until newline (or EOF)
  pure ()

/- Matches a single unit of "skippable" content (whitespace OR comment) -/
def ignorable : ParserT Unit :=
  or_else (satisfy Char.isWhitespace *> pure ()) comment

/- Skip zero or more ignorable units -/
def skip_ignorable : ParserT Unit := do
  _ ← many ignorable
  pure ()

/- Expect and consume a specific string `t` -/
def token (t : String) : ParserT Unit := do
  skip_ignorable
  let s ← get
  if s.input.toString.startsWith t then
    set { s with input := s.input.drop t.length }
  else
    throw s!"Expected '{t}'"

/- Returns a fresh id -/
def fresh_id : ParserT ℕ := do
  let s ← get
  let id := s.counter
  set { s with counter := s.counter + 1 }
  return id

/- Parse an integer value -/
def pInt : ParserT Int := do
  skip_ignorable
  -- 1. Check for optional minus sign
  let s ← get
  let isNeg ← if !is_done s.input && s.input.get 0 == '-' then
      advance 1 -- Consume the '-'
      pure true
    else
      pure false
  -- 2. Parse the digits (absolute value)
  let digits ← many1 (satisfy Char.isDigit)
  let str := String.ofList digits -- Converts List Char -> String

  -- 3. Convert to Int and apply sign
  match str.toNat? with
  | some n =>
      let i : Int := n
      if isNeg then pure (-i) else pure i
  | none   => throw "Invalid number"

/- Parse a natural number -/
def pNat : ParserT ℕ := do
  skip_ignorable
  let digits ← many1 (satisfy Char.isDigit)
  let str := String.ofList digits
  match str.toNat? with
  | some n => pure n
  | none   => throw "Invalid number"

/- Parse an identifier -/
def pIdent : ParserT String := do
  skip_ignorable
  let c ← satisfy Char.isAlpha
  let cs ← many (satisfy Char.isAlphanum)
  pure (String.ofList (c :: cs))

/- Parse a simple expression -/
def pSimpleExpr {c : ZKConfig} : ParserT (SimpleExpr c) := do
  skip_ignorable
  let char ← peek
  if char.isDigit then
    let n ← pInt; pure (.inr n)
  else
    let s ← pIdent; pure (.inl s)

/- The main part of the grammar, using mutual recursion -/
partial def pProg {c : ZKConfig} : ParserT (Prog c) := do
  skip_ignorable
  let s ← get
  if is_done s.input then throw "Unexpected EOF"
  let p ← pBlock
  skip_ignorable
  let s' ← get
  if !(is_done s'.input) then throw s!"Couldn't parse {s'.input}"
  pure p
where
  -- The Block Parser
  pBlock {c : ZKConfig} : ParserT (Prog c):= do
    -- Parse commands
    let cmds ← many (do let cmd ← pCommand; pure cmd)
    pure cmds
  -- The Command Parser (No Backtracking)
  pCommand {c : ZKConfig} : ParserT (Com c) := do
    skip_ignorable
    let s ← get
    let md : CmdMetaData := { src_info := { line := (← fresh_id)}}
    if is_done s.input then throw "Unexpected EOF"
    -- 1. Read the Identifier first (e.g. "if", "skip", "x", "val")
    -- Note: We assume commands start with letters.
    -- If it starts with '{', pCom handles it before calling pCommand.
    let ident ← pIdent
    -- 2. Branch based on what the identifier WAS
    if ident == "if" then
      -- It was the keyword 'if'. Continue parsing the if-structure.
      token "("
      let cvar ← pIdent
      token ")"
      token "{"
      let tb ← pBlock
      token "}"
      token "else"
      token "{"
      let eb ← pBlock
      token "}"
      pure (Com.ifst md cvar tb eb)
    else if ident == "skip" then
      -- It was the keyword 'skip'.
      pure (Com.skip md)
    else
      -- It was a variable name. This MUST be an assignment/operation.
      token ":="
      let op1 ← pSimpleExpr
      -- Check for operator
      skip_ignorable
      let s2 ← get
      if is_done s2.input then
         pure (Com.assign md ident op1)
      else
         let nextC := s2.input.get 0
         if nextC == '+' then
            token "+"; let op2 ← pSimpleExpr; pure (Com.add md ident op1 op2)
         else if nextC == '*' then
            token "*"; let op2 ← pSimpleExpr; pure (Com.mul md ident op1 op2)
         else if nextC == '/' then
            token "/"; let op2 ← pSimpleExpr; pure (Com.div md ident op1 op2)
         else if nextC == '<' then
            token "<<"; let bits ← pNat; pure (Com.shl md ident op1 bits)
         else
            pure (Com.assign md ident op1)

/- The main parsing function  -/
def parse {c : ZKConfig} (s : String) : Except String (Prog c) := do
  match StateT.run pProg { input:= s.toRawSubstring, counter := 1 }  with
  | .ok (c, _) => return c
  | .error e => throw s!"PARSE ERROR: {e}"

/- Just for testing -/
def parse_test (p : String) (h : IO.FS.Stream) : IO Unit := do
  match @parse goldilocks64 p with
  | Except.ok prog => print_prog h prog 0
  | Except.error e => IO.println s!"Parsing error: {e}"
  h.flush



end Llzk.Language.Core.Parser
