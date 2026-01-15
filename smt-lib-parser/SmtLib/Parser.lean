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
   SEXP -> AST CONVERSION
   ========================================== -/

def sortOfSExp : SExp → Option Srt
  | .sym "Bool" => some Srt.bool
  | .sym "Int"  => some Srt.int
  | .sym "String" => some Srt.string
  | .sym s      => some (Srt.ident s)
  | _           => none

partial def termOfSExp : SExp → Option Term
  | .num n      => some (Term.intLit n)
  | .sym s      => some (Term.var s)
  | .str s      => some (Term.stringLit s)
  | .list []    => none
  | .list (f :: args) =>
      match SExp.asSym f with
      | some fn =>
          match args.mapM termOfSExp with
          | some ts => some (Term.app fn ts)
          | none    => none
      | none => none

def parseSortedVar : SExp → Option (String × Srt)
  | SExp.list [SExp.sym name, s] =>
      match sortOfSExp s with
      | some srt => some (name, srt)
      | none => none
  | _ => none

def commandOfSExp : SExp → Option Command
  | SExp.list [SExp.sym "set-logic", SExp.sym name] =>
      some (Command.setLogic name)

  | SExp.list [SExp.sym "declare-const", SExp.sym name, sortSExp] => do
      let s ← sortOfSExp sortSExp
      pure (Command.declareConst name s)

  | SExp.list [SExp.sym "declare-fun", SExp.sym f, SExp.list argSortsS, resS] => do
      let argSorts ← argSortsS.mapM sortOfSExp
      let resSort  ← sortOfSExp resS
      pure (Command.declareFun f argSorts resSort)

  | SExp.list [SExp.sym "define-fun", SExp.sym name, SExp.list argsS, resS, bodyS] => do
      let args ← argsS.mapM parseSortedVar
      let resSort ← sortOfSExp resS
      let body ← termOfSExp bodyS
      pure (Command.defineFun name args resSort body)

  | SExp.list [SExp.sym "assert", t] => do
      let tt ← termOfSExp t
      pure (Command.assert tt)

  | SExp.list [SExp.sym "check-sat"] =>
      some Command.checkSat

  | SExp.list [SExp.sym "exit"] =>
      some Command.exit

  | _ => none

def problemOfSExps (xs : List SExp) : Option Problem := do
  let cmds ← xs.mapM commandOfSExp
  pure { commands := cmds }

/- ==========================================
   PUBLIC API
   ========================================== -/

/-- Parse an SMT-LIB script from a string -/
def parse (s : String) : Option Problem :=
  match runParser sexpScript s with
  | .ok xs    => problemOfSExps xs
  | .error _  => none

/-- Parse a single command from a string -/
def parseCommand (s : String) : Option Command :=
  match runParser sexp s with
  | .ok xs    => commandOfSExp xs
  | .error _  => none

/-- Parse a single S-expression from a string -/
def parseSExp (s : String) : Except String SExp :=
  runParser sexp s

end SmtLib
