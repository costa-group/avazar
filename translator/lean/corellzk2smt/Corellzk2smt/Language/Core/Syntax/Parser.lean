import Corellzk2smt.Basic
import Corellzk2smt.Config
import Corellzk2smt.Language.Core.Syntax.AST
import Corellzk2smt.Language.Core.Syntax.Printer
import Corellzk2smt.Language.Core.Syntax.Lexer

/- A parser for the core language.
-/

namespace Corellzk2smt.Language.Core.Syntax.Parser


open Corellzk2smt.Config
open Corellzk2smt.Language.Core.Syntax.AST
open Corellzk2smt.Language.Core.Syntax.Lexer

/- Parser state, which include a Lexer and a lookahead tokens buffer -/
structure ParserState (c : ZKConfig) where
  lexer : Lexer
  buffer : List TokenInfo -- Lookahead buffer for tokens, should use queue later
  gconf : GlobalConfig c

/- The Parser Monad -/
abbrev ParserM (c : ZKConfig) (α : Type) := StateT (ParserState c) IO α

/- Initialize the parser from a file -/
def ParserM.fromFile {c : ZKConfig} (gconf : GlobalConfig c := default)
  (path : System.FilePath) : IO (ParserState c) := do
  let lexer ← Lexer.fromFile path
  return ⟨ lexer, [], gconf ⟩

/- Make sure we have at least 'n' tokens in the lookahead buffer -/
partial def fillBuffer {c : ZKConfig} (n : Nat) : ParserM c Unit := do
  let st ← get
  if st.buffer.length >= n then
    return ()
  else
    let (tk, newLexer) ← liftM (st.lexer.nextToken)
    if tk.token == Token.eof then
      -- If EOF, simply don't add more (or add EOF markers if you prefer)
      set { st with lexer := newLexer, buffer := st.buffer ++ [tk] }
    else
      set { st with lexer := newLexer, buffer := st.buffer ++ [tk] }
      fillBuffer n

/- Peek at the k-th token ahead (0 = immediate next token) -/
def peekToken {c : ZKConfig} (k : Nat := 0) : ParserM c TokenInfo := do
  fillBuffer (k + 1)
  let st ← get
  match st.buffer[k]? with
  | some tk => return tk
  | none    => return ⟨ Token.eof, st.lexer.col, st.lexer.row ⟩  -- No more tokens

/- Consume the next token -/
def advance {c : ZKConfig} : ParserM c TokenInfo := do
  fillBuffer 1
  let st ← get
  match st.buffer with
  | tk :: rest =>
      set { st with buffer := rest }
      return tk
  | [] => return ⟨ Token.eof, st.lexer.col, st.lexer.row ⟩ -- No more tokens

/- Consumes the next token if it matches the expected character,
   otherwise fails. -/
def expectSymbol {c : ZKConfig} (expected : Char) : ParserM c Unit := do
  let tk ← advance
  if tk.token != Token.symbol expected then
    throw (IO.userError s!"Expected '{expected}', got {tk}")

/- Matches a sequence of identifiers separated by commas. It can return
   an empty list if no identifiers are found (useful for function call)
-/
partial def parseIdentSeq {c : ZKConfig} : ParserM c (List String) := do
  let rec loop (acc : List String) : ParserM c (List String) := do
    let tk ← peekToken 0
    match tk.token with
    | Token.ident v =>    -- first token is an identifier
        let _ ← advance   -- consume the identifier
        let commaTk ← peekToken 0 -- check if the next token is a comma
        if commaTk.token == Token.symbol ',' then
          let _ ← advance -- consume the comma
          loop (v :: acc) -- continue parsing the next identifier
        else
          return (v :: acc).reverse -- no more commas, return the list
    | _ => return acc.reverse -- not an identifier, return what we have
  loop []

/- Parses a simple expression, which can be either a variable or a
   constant (number).
-/
def parseSimpleExpr {c : ZKConfig} : ParserM c (SimpleExpr c):= do
  let tk ← peekToken 0
  let hasMinus := tk.token == Token.symbol '-'
  if hasMinus then
    let _ ← advance -- consume the '-' symbol
    let tk ← advance
    match tk.token with
    | Token.number n =>
      if hasMinus then
        return SimpleExpr.val (-n.toInt!)
      else
        return SimpleExpr.val n.toInt!
    | _ => throw <| .userError s!"Parser error: expected a number after '-' at \
    ({tk.col}, {tk.row}), got {tk.token}"
  else
    let tk ← advance
    match tk.token with
    | Token.ident v => return SimpleExpr.var v
    | Token.number n => return SimpleExpr.val n.toInt!
    | _ => throw <| .userError s!"Parser error: expected a simple expression at \
    ({tk.col}, {tk.row}), got {tk.token}"

/- Parse an expression, which includes all arithmetic, bitwise and boolean expression.
-/
def parseExpr {c : ZKConfig} : ParserM c (Expr c) := do
  let tk ← peekToken 0
  match tk.token with
  -- Arithmeric
  | Token.ident "felt.neg" =>
    let _ ← advance -- consume the 'felt.neg' keyword
    let op1 ← parseSimpleExpr
    return Expr.uop UnOp.neg op1
  | Token.ident "felt.add" =>
    let _ ← advance -- consume the 'felt.add' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.bop BinOp.add op1 op2
  | Token.ident "felt.sub" =>
    let _ ← advance -- consume the 'felt.sub' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.bop BinOp.sub op1 op2
  | Token.ident "felt.mul" =>
    let _ ← advance -- consume the 'felt.mul' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.bop BinOp.mul op1 op2
  | Token.ident "felt.div" =>
    let _ ← advance -- consume the 'felt.div' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.bop BinOp.div op1 op2
  | Token.ident "felt.pow" =>
    let _ ← advance -- consume the 'felt.pow' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.bop BinOp.pow op1 op2
  -- Bitwise
  | Token.ident "bit.shl" =>
    let _ ← advance -- consume the 'bit.shl' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.bop BinOp.shl op1 op2
  | Token.ident "bit.shr" =>
    let _ ← advance -- consume the 'bit.shr' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.bop BinOp.shr op1 op2
  | Token.ident "bit.and" =>
    let _ ← advance -- consume the 'bit.and' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.bop BinOp.and op1 op2
  | Token.ident "bit.or" =>
    let _ ← advance -- consume the 'bit.or' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.bop BinOp.or op1 op2
  | Token.ident "bit.xor" =>
    let _ ← advance -- consume the 'bit.xor' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.bop BinOp.xor op1 op2
  | Token.ident "bit.not" =>
    let _ ← advance -- consume the 'bit.not' keyword
    let op1 ← parseSimpleExpr
    return Expr.uop UnOp.not op1
  -- Comparison
  | Token.ident "bool.eq" =>
    let _ ← advance -- consume the 'bool.eq' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.bop BinOp.eq op1 op2
  | Token.ident "bool.neq" =>
    let _ ← advance -- consume the 'bool.neq' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.bop BinOp.neq op1 op2
  | Token.ident "bool.lt" =>
    let _ ← advance -- consume the 'bool.lt' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.bop BinOp.lt op1 op2
  | Token.ident "bool.gt" =>
    let _ ← advance -- consume the 'bool.gt' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.bop BinOp.gt op1 op2
  | Token.ident "bool.le" =>
    let _ ← advance -- consume the 'bool.le' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.bop BinOp.le op1 op2
  | Token.ident "bool.ge" =>
    let _ ← advance -- consume the 'bool.ge' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.bop BinOp.ge op1 op2
  | Token.ident "bool.and" =>
    let _ ← advance -- consume the 'bool.and' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.bop BinOp.band op1 op2
  | Token.ident "bool.or" =>
    let _ ← advance -- consume the 'bool.or' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.bop BinOp.bor op1 op2
  | Token.ident "bool.not" =>
    let _ ← advance -- consume the 'bool.not' keyword
    let op1 ← parseSimpleExpr
    return Expr.uop UnOp.bneg op1
  | _ => -- must be a simple expression
    let op1 ← parseSimpleExpr
    return Expr.id op1

/- Parses a condition -/
def parseCond {c : ZKConfig} : ParserM c (Cond c) := do
  let l ← parseSimpleExpr
  let sym ← advance
  match sym.token with
  | Token.eq =>
    let r ←  parseSimpleExpr
    return Cond.eq l r
  | _ =>
    throw <| .userError s!"Parser error: expected a '==' at ({sym.col}, {sym.row}), got {sym.token}"

/-- Parses a variable type -/
partial def parseVarType {c : ZKConfig} : ParserM c VarType := do
  let tk ← advance
  match tk.token with
  | Token.ident "ff" => return VarType.ff
  | Token.ident "arr" =>
    let _ ← expectSymbol '<'
    let sizeToken ← advance
    match sizeToken.token with
    | Token.number size =>
      let _ ← expectSymbol '>'
      return (VarType.array size.toNat!)
    | _ => throw <| .userError s!"Parser error: expected a number for array size at \
    ({sizeToken.col}, {sizeToken.row}), got {sizeToken}"
  | _ => throw <| .userError s!"Parser error: expected a variable type at \
  ({tk.col}, {tk.row}), got {tk}"

/-- Parses a function parameter -/
partial def parseParam {c : ZKConfig} : ParserM c Param := do
  let tk ← advance
  match tk.token with
  | Token.ident v =>
    let _ ← expectSymbol ':'
    let varType ← parseVarType
    return ⟨v, varType ⟩
  | _ => throw <| .userError s!"Parser error: expected a parameter at \
  ({tk.col}, {tk.row}), got {tk}"


/- Matches a sequence of parameters separated by commas. It can return
   an empty list if no parameters are found (used for function definitions) -/
partial def parseParamSeq {c : ZKConfig} : ParserM c (List Param) := do
  let rec loop (acc : List Param) : ParserM c (List Param) := do
    let tk ← peekToken 0
    match tk.token with
    | Token.ident _ =>    -- first token is an identifier (of the parameter)
        let p ← parseParam   -- consume the parameter
        let commaTk ← peekToken 0 -- check if the next token is a comma
        if commaTk.token == Token.symbol ',' then
          let _ ← advance -- consume the comma
          loop (p :: acc) -- continue parsing the next identifier
        else
          return (p :: acc).reverse -- no more commas, return the list
    | _ => return acc.reverse -- not an identifier, return what we have
  loop []


/- Matches a sequence of simple expressions separated by commas. It can return
   an empty list if no expressions are found (used for function call) -/
partial def parseSimpExprSeq {c : ZKConfig} : ParserM c (List (SimpleExpr c)) := do
  let rec loop (acc : List (SimpleExpr c)) : ParserM c (List (SimpleExpr c)) := do
    let tk ← peekToken 0
    match tk.token with
    | Token.ident _
    | Token.number _ =>    -- first token is an identifier (of the parameter)
        let s ← parseSimpleExpr   -- consume the parameter
        let commaTk ← peekToken 0 -- check if the next token is a comma
        if commaTk.token == Token.symbol ',' then
          let _ ← advance -- consume the comma
          loop (s :: acc) -- continue parsing the next identifier
        else
          return (s :: acc).reverse -- no more commas, return the list
    | _ => return acc.reverse -- not an identifier, return what we have
  loop []


/- Parsing the different commands, and a sequence of commands-/

mutual

  partial def parseLoop {c: ZKConfig}: ParserM c (Com c) := do
    let _ ← advance -- Consume the 'for' keyword. We should have seen it already.
    let rep ← parseSimpleExpr
    let body ← parseBlock
    return (Com.loop_exp rep body)

  partial def parseIf {c: ZKConfig}: ParserM c (Com c) := do
    let _ ← advance -- Consume the 'if' keyword. We should have seen it already.
    let _ ← expectSymbol '('
    let cond ← parseCond
    let _ ← expectSymbol ')'
    let thenBranch ← parseBlock
    let elseBranch ← do
      let tk ← peekToken 0
      if tk.token == Token.ident "else" then do
        let _ ← advance -- consume 'else'
        parseBlock
      else pure []
    return (Com.if_stmt cond thenBranch elseBranch)

  partial def parseFunCall {c: ZKConfig}: ParserM c (Com c) := do
    let _ ← advance -- Consume the 'call' keyword. We should have seen it already.
    let nameTk ← advance
    match nameTk.token with
    | Token.ident fname =>
      let _ ← expectSymbol '('
      let args ← parseSimpExprSeq
      let _ ← expectSymbol ')'
      let toTk ← peekToken 0
      let outs ← match toTk.token with
        | Token.ident "to" =>
          let _ ← advance -- consume 'to'
          parseIdentSeq
        | _ => pure []
      return (Com.func_call outs fname args)
    | _ => throw <| IO.userError s!"Parser error: expected a function name after 'call' at \
    ({nameTk.col}, {nameTk.row}), got {nameTk.token}"

  partial def parseAssignment {c: ZKConfig}: ParserM c (Com c) := do
    let varTk ← advance
    match varTk.token with
    | Token.ident v =>
      let _ ← expectSymbol '='
      let expr ← parseExpr
      return (Com.assign v expr)
    | _ => throw <| IO.userError s!"Parser error: expected a variable on the left-hand side of \
    assignment at ({varTk.col}, {varTk.row}), got {varTk.token}"

  partial def parseArrayNew {c: ZKConfig}: ParserM c (Com c) := do
    let _ ← advance -- consume 'array.new' keyword. We should have seen it already.
    let sizeTk ← parseSimpleExpr
    let outTk ← advance
    match outTk.token with
    | Token.ident out =>
      return (Com.new_array out sizeTk)
    | _ => throw <| IO.userError s!"Parser error: expected an identifier for output variable at \
    ({outTk.col}, {outTk.row}), got {outTk.token}"

  partial def parseArrayRead {c: ZKConfig}: ParserM c (Com c) := do
    let _ ← advance -- consume 'array.read' keyword. We should have seen it already.
    let arrayVarTk ← advance
    match arrayVarTk.token with
    | Token.ident a =>
      let _ ← expectSymbol '['
      let indexExpr ← parseSimpleExpr
      let _ ← expectSymbol ']'
      let outTk ← advance
      match outTk.token with
      | Token.ident out =>
        return (Com.read_array out a indexExpr)
      | _ => throw <| IO.userError s!"Parser error: expected an identifier for output variable at \
      ({outTk.col}, {outTk.row}), got {outTk.token}"
    | _ => throw <| IO.userError s!"Parser error: expected an identifier for array variable at \
    ({arrayVarTk.col}, {arrayVarTk.row}), got {arrayVarTk.token}"

  partial def parseArrayWrite {c: ZKConfig}: ParserM c (Com c) := do
    let _ ← advance -- consume 'array.write' keyword. We should have seen it already.
    let seTk ← parseSimpleExpr
    let arrayVarTk ← advance
    match arrayVarTk.token with
    | Token.ident a =>
      let _ ← expectSymbol '['
      let indexExpr ← parseSimpleExpr
      let _ ← expectSymbol ']'
      return (Com.write_array a indexExpr seTk)
    | _ => throw <| IO.userError s!"Parser error: expected an identifier for array variable at \
    ({arrayVarTk.col}, {arrayVarTk.row}), got {arrayVarTk.token}"

  partial def parseArrayCopy {c: ZKConfig}: ParserM c (Com c) := do
    let _ ← advance -- consume 'array.copy' keyword. We should have seen it already.
    let inTk ← advance
    let outTk ← advance
    match outTk.token, inTk.token with
    | Token.ident out, Token.ident a =>
      return (Com.copy_array out a)
    | _,_ => throw <| IO.userError s!"Parser error: expected identifiers for array variables at \
    ({outTk.col}, {outTk.row}) and ({inTk.col}, {inTk.row}), got {outTk.token} and {inTk.token}"

  /-- Parse a command -/
  partial def parseCommand {c : ZKConfig}: ParserM c (Com c) := do
    let t0 ← peekToken 0
    let t1 ← peekToken 1
    match t0.token, t1.token with
    | Token.ident "if", _ =>
        let ast ← parseIf
        return ast
    | Token.ident "repeat", _ =>
        let ast ← parseLoop
        return ast
    | Token.ident "call", _ =>
        let ast ← parseFunCall
        return ast
    | Token.ident "array.new", _ =>
        let ast ← parseArrayNew
        return ast
    | Token.ident "array.read", _ =>
        let ast ← parseArrayRead
        return ast
    | Token.ident "array.write", _ =>
        let ast ← parseArrayWrite
        return ast
    | Token.ident "array.copy", _ =>
        let ast ← parseArrayCopy
        return ast

    -- must be assignment or function call, we can distinguish them by looking at the second token
    | _, Token.symbol '=' =>
        let ast ← parseAssignment
        return ast
    | _, _ =>
        throw (IO.userError s!"Unexpected token {t0} when parsing command")

  /-- Parses a list of statements until it hits a '}' -/
  partial def parseBlock {c : ZKConfig} : ParserM c (List (ComWithMD c)) := do

    expectSymbol '{' -- We expect the opening '{'

    let rec loop (acc : List (ComWithMD c)) : ParserM c (List (ComWithMD c)) := do
      let tk ← peekToken 0
      if tk.token == Token.symbol '}' then
        let _ ← advance -- Consume the '}'
        return acc.reverse
      else
      let (row, col) := (tk.row, tk.col)
        let ast ← parseCommand
        loop ( (ComWithMD.mk { src_info := ⟨row, col⟩ } ast) :: acc)

    loop []

  partial def parseFunction {c: ZKConfig}: ParserM c (Func c) := do
    let _ ← advance -- consume 'func' keyword
    let nameTk ← advance
    match nameTk.token with
    | Token.ident name =>
      let _ ← expectSymbol '('
      let params ← parseParamSeq
      let _ ← expectSymbol ')'
      let colonTk ← peekToken 0
      let rets ← match colonTk.token with
          | Token.arrow =>
              let _ ← advance -- consume '->' symbol
              parseParamSeq
          | _ => pure []
      let body ← parseBlock
      return (Func.mk name params rets body)
    | _ => throw (IO.userError s!"Expected a function name after 'func', got {nameTk}")
end

partial def parseProg {c : ZKConfig}
  (acc : List (FuncWithMD c) := []) : ParserM c (ProgWithMD c) := do
  let t0 ← peekToken 0
  if t0.token == Token.eof then
    return ProgWithMD.mk {} acc
  else
    let (row, col) := (t0.row, t0.col)
    let ast ← parseFunction
    parseProg ( (FuncWithMD.mk { src_info := ⟨row, col⟩ } ast) :: acc)




end Corellzk2smt.Language.Core.Syntax.Parser
