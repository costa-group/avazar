import Init.System.IO

namespace Llzk.Language.Core.Syntax.Lexer

/- A structure to keep track of the lexer's state, including a buffer,
 position, and error reporting information -/
structure Lexer where
  handle : IO.FS.Handle -- Where we read from (file handle)
  buffer : String       -- Buffer of text read from the file
  pos    : Nat          -- We store position strictly as a Nat
  line   : Nat          -- For error reporting: current line number
  col    : Nat          -- For error reporting: current column number

/- Create a Lexer from a file path -/
def Lexer.fromFile (path : System.FilePath) : IO Lexer := do
  let h ← IO.FS.Handle.mk path IO.FS.Mode.read
  return {
    handle := h,
    buffer := "",
    pos := 0,
    line := 1,
    col := 0
  }

/- This function ensures that the lexer has data to read -/
partial def Lexer.ensureData (st : Lexer) : IO (Bool × Lexer) := do
  if st.pos < st.buffer.utf8ByteSize then -- if we still have data in the buffer
    return (true, st)
  else  -- we don't have data, try to read more
    let moreBytes ← st.handle.read 4096 -- Read the next 4KB chunk
    if moreBytes.isEmpty then
      return (false, st)
    else -- convert bytes to string and update the buffer
      match String.fromUTF8? moreBytes with
      | some moreText =>
          return (true, { st with buffer := moreText, pos := 0 })
      | none =>
        throw <| .userError "Tried to read from handle containing non UTF-8 data."

/- Peek at the next character without consuming it, and update the
   lexer state if necessary (needed if we had to read more data
   into the buffer)
-/
def Lexer.peek (st : Lexer) : IO (Option Char × Lexer) := do
  let (hasData, st) ← st.ensureData -- ensure we have data to read
  if hasData then
    return (some (String.Pos.Raw.get st.buffer ⟨st.pos⟩), st)
  else
    return (none, st)

/- Consume the next character and update the lexer's state -/
def Lexer.next (st : Lexer) : IO (Option Char × Lexer) := do
  let (hasData, st) ← st.ensureData -- ensure we have data to read
  if hasData then
    let c := String.Pos.Raw.get st.buffer ⟨st.pos⟩ -- Get the current character
    let ⟨newPosNat⟩ := String.Pos.Raw.next st.buffer ⟨st.pos⟩ -- Move to the next position
    let (newLine, newCol) := if c == '\n' then (st.line + 1, 0) else (st.line, st.col + 1) -- Update line/col
    return (some c, { st with
      pos := newPosNat,
      line := newLine,
      col := newCol
    })
  else
    return (none, st)


/- Scan characters while the predicate holds -/
partial def Lexer.scanWhile (st : Lexer) (pred : Char → Bool) (acc : String := "") : IO (String × Lexer) := do
  let (hasData, st) ← st.ensureData -- ensure we have data to read
  if not hasData then return (acc, st) -- No more data, return what we have

  let bufSize := st.buffer.utf8ByteSize
  let startPos := st.pos

  -- A loop that advances 'p' while the predicate holds, and updates 'l' and 'c' accordingly.
  let rec loop (p : Nat) (l : Nat) (c : Nat) : Nat × Nat × Nat :=
    if p < bufSize then
      let char := String.Pos.Raw.get st.buffer (String.Pos.Raw.mk p)
      if pred char then
        let ⟨nextP⟩ := String.Pos.Raw.next st.buffer (String.Pos.Raw.mk p)
        let (newL, newC) := -- update col/row
          if char == '\n' then (l + 1, 0) else (l, c + 1)
        loop nextP newL newC -- keep matching
      else
        (p, l, c) -- Predicate failed, return current state
    else
      (p, l, c) -- End of buffer, return current state

  -- Run the loop
  let (endPos, finalLine, finalCol) := loop startPos st.line st.col

  -- Extract the string
  let chunk := String.Pos.Raw.extract st.buffer (String.Pos.Raw.mk startPos) (String.Pos.Raw.mk endPos)

  -- Append to accumulator if we had one (e.g., from a previous buffer). This is important for tokens
  -- that span across buffer boundaries, it should not happen often, so we do not append often.
  let currentWord := if acc.isEmpty then chunk else acc ++ chunk

  -- Update state with the values we already calculated
  let st' := { st with pos := endPos, line := finalLine, col := finalCol }

  -- If the loop stopped because it has reached the end, we try call recursively
  -- to read more data and continue scanning.
  if endPos == bufSize then
    scanWhile st' pred currentWord
  else
    return (currentWord, st')

/- Token definitions. It includes all possible tokens in the language -/
inductive Token where
  | ident    : String → Token    -- variables, functions names, e.g., "%x", "%foo"
  | cvar     : String → Token    -- constant variable, e.g., "$x"
  | keyword  : String → Token    -- keyword, e.g., "if", "for", etc.
  | number   : String → Token    -- number, e.g., 123
  | eq       : Token             -- '=' symbol
  | neq      : Token             -- '!=' symbol
  | symbol   : Char → Token      -- symbol, e.g., '+', '=', '{'
  | eof      : Token             -- End of File
  deriving Repr, BEq, Inhabited

/- Convert a token to its string representation -/
def Token.toString (tk : Token) : String :=
  match tk with
  | Token.ident v => s!"%{v} (var)"
  | Token.cvar v => s!"${v} (cvar)"
  | Token.keyword i => s!"{i} (keyword)"
  | Token.number n => s!"{n} (number)"
  | Token.eq => "'==' (symbol)"
  | Token.neq => "'!=' (symbol)"
  | Token.symbol c => s!"'{c}' (symbol)"
  | Token.eof => "<EOF>"

/- Register ToString instance for Token -/
instance : ToString Token where
  toString := Token.toString

/- Token information, including its position in the source code -/
structure TokenInfo where
  token : Token
  col: Nat
  row : Nat
  deriving Repr, Inhabited

/- Convert token information to its string representation -/
def TokenInfo.toString (info : TokenInfo) : String :=
  s!"{info.token} at line {info.row}, column {info.col}"

/- Register ToString instance for TokenInfo -/
instance : ToString TokenInfo where
  toString := TokenInfo.toString

/-- Skip whitespace characters -/
def Lexer.skipWhitespace (st : Lexer) : IO Lexer := do
  let (_, st) ← st.scanWhile (fun c => c.isWhitespace)
  return st

/- Main Tokenizer: Converts the char-stream into a token.

   In principle, it is like a DFA that is the product of all DFAs for
   different token types. -/
partial def Lexer.nextToken (st : Lexer) : IO (TokenInfo × Lexer) := do
  let st ← skipWhitespace st -- Skip leading whitespace
  let (optChar,st) ← st.peek -- peek at the next character to decide what to do
  match optChar with
  | none => return (⟨ Token.eof, st.col, st.line ⟩, st)
  | some c =>
  let col := st.col
  let row := st.line
    -- Comment: Start with '#', skip until the end of the line and return the next token after that
    if c == '#' then
      let (_, st) ← st.next -- consume the '#' character
      let (_, st) ← st.scanWhile (fun x => x != '\n') -- skip until the end of the line
      nextToken st -- After skipping comment, get the next token

    -- Variable: Start with '%', read while alphanumeric or underscore
    else if c == '%' then
      let (_, st) ← st.next -- consume the '%' character
      let (s, st) ← st.scanWhile (fun x => x.isAlphanum || x == '_') -- read the variable name
      return (⟨ Token.ident s, col, row ⟩, st)

    -- Constant Variable: Start with '@', read while alphanumeric or underscore
    else if c == '$' then
      let (_, st) ← st.next -- consume the '@' character
      let (s, st) ← st.scanWhile (fun x => x.isAlphanum || x == '_') -- read the constant variable name
      return (⟨ Token.cvar s, col, row ⟩, st)

    -- Equality sign: '=='
    else if c == '=' then
      let (_, st) ← st.next -- consume the '=' character
      let (nextCharOpt, st) ← st.peek
      if nextCharOpt == some '=' then
        let (_, st) ← st.next -- consume the second '=' character
        return (⟨ Token.eq, col, row ⟩, st)
      else
        return (⟨ Token.symbol '=', col, row ⟩, st)

    -- Not equal sign: '!='
    else if c == '!' then
      let (_, st) ← st.next -- consume the '!' character
      let (nextCharOpt, st) ← st.peek
      if nextCharOpt == some '=' then
        let (_, st) ← st.next -- consume the '=' character
        return (⟨ Token.neq, col, row ⟩, st)
      else
        return (⟨ Token.symbol '!', col, row ⟩, st)

    -- Keyword: any sequence starting with a letter or underscore, followed by letters, digits, or underscore.
    else if c.isAlpha then
      let (s, st) ← scanWhile st (fun x => x.isAlpha || x == '.' || x == '_') -- read the identifier
      return (⟨ Token.keyword s, col, row ⟩, st)

    -- Number: any sequence of digits (for negative numbers, the sign is supposed to be handled
    -- by the parser as a different token)
    else if c.isDigit then
      let (s, st) ← scanWhile st (fun x => x.isDigit) -- read the number
      return (⟨ Token.number s, col, row ⟩, st)

    -- If none of the above, we treat it as a single character symbol (e.g., '=', '{', '}', etc.)
    else
      let (_, st) ← st.next -- consume the symbol character
      return (⟨ Token.symbol c, col, row ⟩, st)

end Llzk.Language.Core.Syntax.Lexer
