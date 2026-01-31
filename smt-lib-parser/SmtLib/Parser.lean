/-
  SmtLib/Parser.lean
  ==================
  S-expression parser and AST conversion for SMT-LIB 2.6
-/

import Std
import SmtLib.AST

open Std
open Std.Internal.Parsec
open Std.Internal.Parsec.String

namespace SmtLib


def opOfString : String → Op
  | "+" => Op.plus
  | "-" => Op.minus
  | "*" => Op.mul
  | "div" => Op.div
  | "mod" => Op.mod
  | "not" => Op.not
  | "and" => Op.and
  | "or" => Op.or
  | "xor" => Op.xor
  | "=>" => Op.imp
  | "=" => Op.eq
  | "<" => Op.lt
  | ">" => Op.gt
  | "<=" => Op.le
  | ">=" => Op.ge
  | "ite" => Op.ite
  | "distinct" => Op.distinct
  | s => Op.custom s

/- ==========================================
   PARSER PRIMITIVES
   ========================================== -/

abbrev Parser (α : Type) := Std.Internal.Parsec.String.Parser α

def runParser {α} (p : Parser α) (input : String) : Except String α :=
  p.run input

def attempt {α} (p : Parser α) : Parser α := fun it =>
  match p it with
  | .success rem a => .success rem a
  | .error _ err   => .error it err

/- ==========================================
   LEXER
   ========================================== -/

def comment : Parser Unit := do
  skipChar ';'
  let _ ← many (satisfy (fun c => c ≠ '\n'))
  pure ()

def spaces : Parser Unit := do
  let spaceChar : Parser Unit :=
    (satisfy (fun c => c = ' ' || c = '\t' || c = '\r' || c = '\n')) *> pure ()
  let one : Parser Unit := spaceChar <|> comment
  let _ ← many one
  pure ()

def lexeme {α} (p : Parser α) : Parser α := attempt (spaces *> p)

def isSymbolChar (c : Char) : Bool :=
  !c.isWhitespace && c ≠ '(' && c ≠ ')' && c ≠ ';'

def symbol : Parser String :=
  many1Chars (satisfy isSymbolChar)

def intLit : Parser Int := do
  let sign : Int ← (skipChar '-' *> pure (-1)) <|> (pure 1)
  let first ← String.digit
  let restStr ← manyChars String.digit
  let nStr := String.singleton first ++ restStr
  match nStr.toInt? with
  | some n => pure (sign * n)
  | none   => fail s!"invalid integer literal: {nStr}"
where
  manyChars (p : Parser Char) : Parser String := do
    let chars ← many p
    pure chars.toList.asString

def stringLit : Parser String := do
  skipChar '"'
  let chars ← (satisfy (fun c => c ≠ '"')).manyChars
  skipChar '"'
  pure chars

def lparen : Parser Unit := lexeme (skipChar '(')
def rparen : Parser Unit := lexeme (skipChar ')')

/- ==========================================
   S-EXPRESSION PARSER
   ========================================== -/

mutual
  partial def sexp : Parser SExp :=
    parseList <|> parseAtom

  partial def parseList : Parser SExp := do
    lparen
    let xsArr ← many sexp
    rparen
    pure (SExp.list xsArr.toList)

  partial def parseAtom : Parser SExp := do
    lexeme (parseNum <|> parseStr <|> parseSym)

  partial def parseNum : Parser SExp := do
    let n ← intLit
    pure (SExp.num n)

  partial def parseStr : Parser SExp := do
    let s ← stringLit
    pure (SExp.str s)

  partial def parseSym : Parser SExp := do
    let s ← symbol
    pure (SExp.sym s)
end

def sexpScript : Parser (List SExp) := do
  spaces
  let xsArr ← many sexp
  spaces
  eof
  pure xsArr.toList

/- ==========================================
   SEXP -> AST CONVERSION (with error messages)
   ========================================== -/

/-- Convert S-expression to Sort with error messages -/
def sortOfSExpE : SExp → Except String Srt
  | .sym "Bool"   => .ok Srt.bool
  | .sym "Int"    => .ok Srt.int
  | .sym "String" => .ok Srt.string
  | .sym s        => .ok (Srt.ident s)
  | other         => .error s!"Expected sort (Bool, Int, String, or identifier), got: {repr other}"

/-- Convert S-expression to Term with error messages -/
def termOfSExpE : SExp → Except String Term
  | .num n   => .ok (Term.intLit n)
  | .sym s   => .ok (Term.var s)
  | .str s   => .ok (Term.stringLit s)
  | .list [] => .error "Empty list cannot be converted to term"
  | .list (f :: args) =>
      match SExp.asSym f with
      | some fn =>
          match args.mapM termOfSExpE with
          | .ok ts   => .ok (Term.app (opOfString fn) ts)
          | .error e => .error s!"In arguments of '{fn}': {e}"
      | none => .error s!"Expected function symbol, got: {repr f}"

/-- Parse sorted variable like (x Int) with error messages -/
def parseSortedVarE : SExp → Except String (String × Srt)
  | SExp.list [SExp.sym name, s] =>
      match sortOfSExpE s with
      | .ok srt  => .ok (name, srt)
      | .error e => .error s!"In variable '{name}': {e}"
  | other => .error s!"Expected (name Sort), got: {repr other}"

/-- Convert S-expression to Command with error messages -/
def commandOfSExpE : SExp → Except String Command
  | SExp.list [SExp.sym "set-logic", SExp.sym name] =>
      .ok (Command.setLogic name)

  | SExp.list [SExp.sym "declare-const", SExp.sym name, sortSExp] =>
      match sortOfSExpE sortSExp with
      | .ok s    => .ok (Command.declareConst name s)
      | .error e => .error s!"In declare-const '{name}': {e}"

  | SExp.list [SExp.sym "declare-fun", SExp.sym f, SExp.list argSortsS, resS] =>
      match argSortsS.mapM sortOfSExpE with
      | .error e => .error s!"In declare-fun '{f}' argument sorts: {e}"
      | .ok argSorts =>
          match sortOfSExpE resS with
          | .ok resSort => .ok (Command.declareFun f argSorts resSort)
          | .error e    => .error s!"In declare-fun '{f}' return sort: {e}"

  | SExp.list [SExp.sym "define-fun", SExp.sym name, SExp.list argsS, resS, bodyS] =>
      match argsS.mapM parseSortedVarE with
      | .error e => .error s!"In define-fun '{name}' parameters: {e}"
      | .ok args =>
          match sortOfSExpE resS with
          | .error e => .error s!"In define-fun '{name}' return sort: {e}"
          | .ok resSort =>
              match termOfSExpE bodyS with
              | .ok body   => .ok (Command.defineFun name args resSort body)
              | .error e   => .error s!"In define-fun '{name}' body: {e}"

  | SExp.list [SExp.sym "assert", t] =>
      match termOfSExpE t with
      | .ok tt   => .ok (Command.assert tt)
      | .error e => .error s!"In assert: {e}"

  | SExp.list [SExp.sym "check-sat"] =>
      .ok Command.checkSat

  | SExp.list [SExp.sym "get-model"] =>
      .ok Command.getModel

  | SExp.list [SExp.sym "get-value", SExp.list termsS] =>
      match termsS.mapM termOfSExpE with
      | .ok terms => .ok (Command.getValue terms)
      | .error e  => .error s!"In get-value: {e}"

  | SExp.list [SExp.sym "exit"] =>
      .ok Command.exit

  | SExp.list (SExp.sym cmd :: _) =>
      .error s!"Unknown or malformed command: {cmd}"

  | other =>
      .error s!"Invalid command syntax: {repr other}"

/-- Convert list of S-expressions to Problem with error messages -/
def problemOfSExpsE (xs : List SExp) : Except String Problem := do
  let cmds ← xs.mapM commandOfSExpE
  pure { commands := cmds }

/- ==========================================
   LEGACY OPTION-BASED API (for backwards compatibility)
   ========================================== -/

def sortOfSExp (s : SExp) : Option Srt := (sortOfSExpE s).toOption
def termOfSExp (s : SExp) : Option Term := (termOfSExpE s).toOption
def parseSortedVar (s : SExp) : Option (String × Srt) := (parseSortedVarE s).toOption
def commandOfSExp (s : SExp) : Option Command := (commandOfSExpE s).toOption
def problemOfSExps (xs : List SExp) : Option Problem := (problemOfSExpsE xs).toOption

/- ==========================================
   PUBLIC API
   ========================================== -/

/-- Parse an SMT-LIB script from a string (with error messages) -/
def parseE (s : String) : Except String Problem :=
  match runParser sexpScript s with
  | .ok xs    => problemOfSExpsE xs
  | .error e  => .error s!"Syntax error: {e}"

/-- Parse a single command from a string (with error messages) -/
def parseCommandE (s : String) : Except String Command :=
  match runParser sexp s with
  | .ok xs    => commandOfSExpE xs
  | .error e  => .error s!"Syntax error: {e}"

/-- Parse an SMT-LIB script from a string (legacy Option API) -/
def parse (s : String) : Option Problem := (parseE s).toOption

/-- Parse a single command from a string (legacy Option API) -/
def parseCommand (s : String) : Option Command := (parseCommandE s).toOption

/-- Parse a single S-expression from a string -/
def parseSExp (s : String) : Except String SExp :=
  runParser sexp s

end SmtLib
