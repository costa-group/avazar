import Llzk.Basic
import Llzk.Language.Core.Syntax.AST
import Llzk.Language.Core.Syntax.Lexer

/- A parser for the core language.
-/

namespace Llzk.Language.Core.Syntax.Parser


open Llzk.Language.Core.Syntax.AST
open Llzk.Language.Core.Syntax.Lexer

/- Parser state, which include a Lexer and a lookahead tokens buffer -/
structure ParserState where
  lexer : Lexer
  buffer : List TokenInfo -- Lookahead buffer for tokens, should use queue later

/- The Parser Monad -/
abbrev ParserM (α : Type) := StateT ParserState IO α

/- Initialize the parser from a file -/
def ParserM.fromFile (path : System.FilePath) : IO ParserState := do
  let lexer ← Lexer.fromFile path
  return ⟨ lexer, [] ⟩

/- Make sure we have at least 'n' tokens in the lookahead buffer -/
partial def fillBuffer (n : Nat) : ParserM Unit := do
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
def peekToken (k : Nat := 0) : ParserM TokenInfo := do
  fillBuffer (k + 1)
  let st ← get
  match st.buffer[k]? with
  | some tk => return tk
  | none    => return ⟨ Token.eof, st.lexer.col, st.lexer.line ⟩  -- No more tokens

/- Consume the next token -/
def advance : ParserM TokenInfo := do
  fillBuffer 1
  let st ← get
  match st.buffer with
  | tk :: rest =>
      set { st with buffer := rest }
      return tk
  | [] => return ⟨ Token.eof, st.lexer.col, st.lexer.line ⟩ -- No more tokens

/- Consumes the next token if it matches the expected character,
   otherwise fails. -/
def expectSymbol (expected : Char) : ParserM Unit := do
  let tk ← advance
  if tk.token != Token.symbol expected then
    throw (IO.userError s!"Expected '{expected}', got {tk}")

/- Matches a sequence of identifiers separated by commas. It can return
   an empty list if no identifiers are found (useful for function call) -/
partial def parseIdentSeq : ParserM (List String) := do
  let rec loop (acc : List String) : ParserM (List String) := do
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


def parseSimpleExpr {c : ZKConfig} : ParserM (SimpleExpr c):= do
  let tk ← peekToken 0
  let hasMinus := tk.token == Token.symbol '-'
  if hasMinus then
    let _ ← advance -- consume the '-'
    let tk ← advance
    match tk.token with
    | Token.number n =>
      if hasMinus then
        return SimpleExpr.val (-n.toInt!)
      else
        return SimpleExpr.val n.toInt!
    | _ => throw (IO.userError s!"Expected a number after '-', got {tk.token}")
  else
    let tk ← advance
    match tk.token with
    | Token.ident v => return SimpleExpr.var v
    | Token.cvar v => return SimpleExpr.cvar v
    | Token.number n => return SimpleExpr.val n.toInt!
    | _ => throw (IO.userError s!"Expected a simple expression, got {tk.token}")

def parseExpr {c : ZKConfig} : ParserM (Expr c) := do
  let tk ← peekToken 0
  match tk.token with
  -- Arithmeric
  -- | Token.keyword "felt.id" =>
  --   let op1 ← parseSimpleExpr
  --   return Expr.id op1
  | Token.keyword "felt.neg" =>
    let _ ← advance -- consume the 'felt.neg' keyword
    let op1 ← parseSimpleExpr
    return Expr.neg op1
  | Token.keyword "felt.add" =>
    let _ ← advance -- consume the 'felt.add' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.add op1 op2
  | Token.keyword "felt.sub" =>
    let _ ← advance -- consume the 'felt.sub' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.sub op1 op2
  | Token.keyword "felt.mul" =>
    let _ ← advance -- consume the 'felt.mul' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.mul op1 op2
  | Token.keyword "felt.div" =>
    let _ ← advance -- consume the 'felt.div' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.div op1 op2
  -- Bitwise
  | Token.keyword "bit.shl" =>
    let _ ← advance -- consume the 'bit.shl' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.shl op1 op2
  | Token.keyword "bit.shr" =>
    let _ ← advance -- consume the 'bit.shr' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.shr op1 op2
  | Token.keyword "bit.and" =>
    let _ ← advance -- consume the 'bit.and' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.and op1 op2
  | Token.keyword "bit.or" =>
    let _ ← advance -- consume the 'bit.or' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.or op1 op2
  | Token.keyword "bit.xor" =>
    let _ ← advance -- consume the 'bit.xor' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.xor op1 op2
  | Token.keyword "bit.not" =>
    let _ ← advance -- consume the 'bit.not' keyword
    let op1 ← parseSimpleExpr
    return Expr.not op1
  -- Comparison
  | Token.keyword "bool.True" =>
    let _ ← advance -- consume the 'bool.True' keyword
    return Expr.True
  | Token.keyword "bool.False" =>
    let _ ← advance -- consume the 'bool.False' keyword
    return Expr.False
  | Token.keyword "bool.eq" =>
    let _ ← advance -- consume the 'bool.eq' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.eq op1 op2
  | Token.keyword "bool.neq" =>
    let _ ← advance -- consume the 'bool.neq' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.neq op1 op2
  | Token.keyword "bool.lt" =>
    let _ ← advance -- consume the 'bool.lt' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.lt op1 op2
  | Token.keyword "bool.gt" =>
    let _ ← advance -- consume the 'bool.gt' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.gt op1 op2
  | Token.keyword "bool.le" =>
    let _ ← advance -- consume the 'bool.le' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.le op1 op2
  | Token.keyword "bool.ge" =>
    let _ ← advance -- consume the 'bool.ge' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.ge op1 op2
  | Token.keyword "bool.and" =>
    let _ ← advance -- consume the 'bool.and' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.band op1 op2
  | Token.keyword "bool.or" =>
    let _ ← advance -- consume the 'bool.or' keyword
    let op1 ← parseSimpleExpr
    let op2 ← parseSimpleExpr
    return Expr.bor op1 op2
  | Token.keyword "bool.not" =>
    let _ ← advance -- consume the 'bool.not' keyword
    let op1 ← parseSimpleExpr
    return Expr.bneg op1
  | _ => -- must be a simple expression
    let op1 ← parseSimpleExpr
    return Expr.id op1

def parseCond {c : ZKConfig} : ParserM (Cond c) := do
  let l ← parseSimpleExpr
  let sym ← advance
  let r ←  parseSimpleExpr
  match sym.token with
  | Token.eq=>
    return Cond.eq l r
  | Token.neq=>
    return Cond.neq l r
  | _ =>
    throw (IO.userError s!"Expected a condition, got {l} {sym} {r}")


partial def parseVarType : ParserM VarType := do
  let tk ← advance
  match tk.token with
  | Token.keyword "ff" => return VarType.ff
  | Token.keyword "arr" =>
    let _ ← expectSymbol '<'
    let sizeToken ← advance
    match sizeToken.token with
    | Token.number size =>
      let _ ← expectSymbol '>'
      return (VarType.array size.toNat!)
    | _ => throw (IO.userError s!"Expected a number for array size, got {sizeToken}")
  | _ => throw (IO.userError s!"Expected a variable type, got {tk}")


partial def parseParam : ParserM Param := do
  let tk ← advance
  match tk.token with
  | Token.ident v =>
    let _ ← expectSymbol ':'
    let varType ← parseVarType
    return (v,varType)
  | _ => throw (IO.userError s!"Expected a parameter, got {tk}")


/- Matches a sequence of identifiers separated by commas. It can return
   an empty list if no identifiers are found (useful for function call) -/
partial def parseParamSeq : ParserM (List Param) := do
  let rec loop (acc : List Param) : ParserM (List Param) := do
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
   an empty list if no expressions are found (useful for function call) -/
partial def parseSimpExprSeq {c : ZKConfig} : ParserM (List (SimpleExpr c)) := do
  let rec loop (acc : List (SimpleExpr c)) : ParserM (List (SimpleExpr c)) := do
    let tk ← peekToken 0
    match tk.token with
    | Token.ident _
    | Token.cvar _
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

mutual

  partial def parseWithConst {c: ZKConfig}: ParserM (Com c) := do
    let _ ← advance -- Consume the 'with_const' keyword
    let varTk ← advance
    match varTk.token with
    | Token.cvar v =>
        let _ ← expectSymbol '='
        let expr ← parseExpr
        let body ← parseBlock
        return (Com.with_const emptyCMD v expr body)
    | _ => throw (IO.userError s!"Expected a constant variable after 'with_const', got {varTk}")

  partial def parseFor {c: ZKConfig}: ParserM (Com c) := do
    let _ ← advance -- Consume the 'for' keyword
    let _ ← expectSymbol '('
    let varTk ← advance
    match varTk.token with
    | Token.cvar v =>
        let _ ← expectSymbol ','
        let startExpr ← parseExpr
        let _ ← expectSymbol ','
        let repExpr ← parseExpr
        let _ ← expectSymbol ','
        let stepExpr ← parseExpr
        let _ ← expectSymbol ')'
        let body ← parseBlock
        return (Com.loop_exp emptyCMD v startExpr repExpr stepExpr body)
    | _ => throw (IO.userError s!"Expected a constant variable after 'for(', got {varTk.token}")

  partial def parseIf {c: ZKConfig}: ParserM (Com c) := do
    let _ ← advance -- Consume the 'if' keyword
      let _ ← expectSymbol '('
    let cond ← parseCond
    let _ ← expectSymbol ')'
    let thenBranch ← parseBlock
    let elseBranch ← do
      let tk ← peekToken 0
      if tk.token == Token.keyword "else" then do
        let _ ← advance -- consume 'else'
        parseBlock
      else pure []
    return (Com.if_stmt emptyCMD cond thenBranch elseBranch)

  partial def parseFunCall {c: ZKConfig}: ParserM (Com c) := do
    let _ ← advance -- Consume the 'call' keyword
    let nameTk ← advance
    match nameTk.token with
    | Token.ident fname =>
      let _ ← expectSymbol '('
      let args ← parseSimpExprSeq
      let _ ← expectSymbol ')'
      let toTk ← peekToken 0
      let outs ← match toTk.token with
        | Token.keyword "to" =>
          let _ ← advance -- consume 'to'
          parseIdentSeq
        | _ => pure []
      return (Com.func_call emptyCMD outs fname args)
    | _ => throw (IO.userError s!"Expected a function name after 'call', got {nameTk.token}")

  partial def parseAssignment {c: ZKConfig}: ParserM (Com c) := do
    let varTk ← advance
    match varTk.token with
    | Token.ident v =>
      let _ ← expectSymbol '='
      let expr ← parseExpr
      return (Com.assign emptyCMD v expr)
    | _ => throw (IO.userError
                  s!"Expected a variable on the left-hand side of assignment, got {varTk.token}")

  partial def parseArrayNew {c: ZKConfig}: ParserM (Com c) := do
    let _ ← advance -- consume 'array.new' keyword
    let sizeTk ← parseSimpleExpr
    let outTk ← advance
    match outTk.token with
    | Token.ident out =>
      return (Com.new_array emptyCMD out sizeTk)
    | _ => throw (IO.userError
                    s!"Expected an identifier for output variable, got {outTk.token}")

  partial def parseArrayRead {c: ZKConfig}: ParserM (Com c) := do
    let _ ← advance -- consume 'array.read' keyword
    let arrayVarTk ← advance
    match arrayVarTk.token with
    | Token.ident a =>
      let _ ← expectSymbol '['
      let indexExpr ← parseSimpleExpr
      let _ ← expectSymbol ']'
      let outTk ← advance
      match outTk.token with
      | Token.ident out =>
        return (Com.read_array emptyCMD out a indexExpr)
      | _ => throw (IO.userError s!"Expected an identifier for output variable, got {outTk.token}")
    | _ => throw (IO.userError
                    s!"Expected an identifier for array variable, got {arrayVarTk.token}")

  partial def parseArrayWrite {c: ZKConfig}: ParserM (Com c) := do
    let _ ← advance -- consume 'array.write' keyword
    let seTk ← parseSimpleExpr
    let arrayVarTk ← advance
    match arrayVarTk.token with
    | Token.ident a =>
      let _ ← expectSymbol '['
      let indexExpr ← parseSimpleExpr
      let _ ← expectSymbol ']'
      return (Com.write_array emptyCMD a indexExpr seTk)
    | _ => throw (IO.userError
                    s!"Expected an identifier for array variable, got {arrayVarTk.token}")

  partial def parseArrayCopy {c: ZKConfig}: ParserM (Com c) := do
    let _ ← advance -- consume 'array.copy' keyword
    let inTk ← advance
    let outTk ← advance
    match outTk.token, inTk.token with
    | Token.ident out, Token.ident a =>
      return (Com.copy_array emptyCMD out a)
    | _,_ => throw
               (IO.userError
                  s!"Expected identifiers for array variables, got {outTk.token} and {inTk.token}")

  partial def parseSkip {c: ZKConfig}: ParserM (Com c) := do
    let _ ← advance -- consume 'skip' keyword
    return (Com.skip emptyCMD) -- TODO: implement this

  /-- Parse a command -/
  partial def parseCommand {c : ZKConfig}: ParserM (Com c) := do
    let t0 ← peekToken 0
    let t1 ← peekToken 1
    match t0.token, t1.token with
    | Token.keyword "if", _ =>
        let ast ← parseIf
        return ast
    | Token.keyword "with_const",_ =>
        let ast ← parseWithConst
        return ast
    | Token.keyword "for", _ =>
        let ast ← parseFor
        return ast
    | Token.keyword "call", _ =>
        let ast ← parseFunCall
        return ast
    | Token.keyword "array.new", _ =>
        let ast ← parseArrayNew
        return ast
    | Token.keyword "array.read", _ =>
        let ast ← parseArrayRead
        return ast
    | Token.keyword "array.write", _ =>
        let ast ← parseArrayWrite
        return ast
    | Token.keyword "array.copy", _ =>
        let ast ← parseArrayCopy
        return ast

    -- must be assignment or function call, we can distinguish them by looking at the second token
    | _, Token.symbol '=' =>
        let ast ← parseAssignment
        return ast
    | _, _ =>
        throw (IO.userError s!"Unexpected token {t0} when parsing command")

  /-- Parses a list of statements until it hits a '}' -/
  partial def parseBlock {c : ZKConfig} : ParserM (List (Com c)) := do

    expectSymbol '{' -- We expect the opening '{'

    let rec loop (acc : List (Com c)) : ParserM (List (Com c)) := do
      let tk ← peekToken 0
      if tk.token == Token.symbol '}' then
        let _ ← advance -- Consume the '}'
        return acc.reverse
      else
        let ast ← parseCommand
        loop (ast :: acc)

    loop []

  partial def parseFunction {c: ZKConfig}: ParserM (Function c) := do
    let _ ← advance -- consume 'func' keyword
    let nameTk ← advance
    match nameTk.token with
    | Token.ident name =>
      let _ ← expectSymbol '('
      let params ← parseParamSeq
      let _ ← expectSymbol ')'
      let colonTk ← peekToken 0
      let rets ← match colonTk.token with
          | Token.symbol ':' =>
              let _ ← advance -- consume ':'
              parseParamSeq
          | _ => pure []
      let body ← parseBlock
      return { md := emptyCMD, name := name, params := params, rets := rets, body := body }
    | _ => throw (IO.userError s!"Expected a function name after 'func', got {nameTk}")
end

partial def parseProg {c : ZKConfig} (acc : List (Function c)) : ParserM (List (Function c)) := do
  let t0 ← peekToken 0
  if t0.token == Token.eof then
    return acc
  else
    let ast ← parseFunction
    parseProg (ast :: acc)




end Llzk.Language.Core.Syntax.Parser
