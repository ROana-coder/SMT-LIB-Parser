import Std

open Std
open Std.Internal.Parsec
open Std.Internal.Parsec.String

namespace SmtLib

/-
  AST de nivel înalt pentru un script SMT-LIB.
  Poți extinde foarte ușor sorturile, termenii și comenzile.
-/

inductive sort where
  | bool
  | int
  | ident (name : String)
  deriving Repr, BEq

inductive Term where
  | var    (name : String)
  | intLit (val  : Int)
  | app    (fn   : String) (args : List Term)
  deriving Repr, BEq

inductive Command where
  | setLogic   (name : String)
  | declareFun (name : String) (argSorts : List Sort) (resSort : Sort)
  | assert     (t : Term)
  | checkSat
  | exit
  deriving Repr, BEq

structure Problem where
  commands : List Command
  deriving BEq

/-
  1. Parser generic de s-expr (SExp)
  2. Traducere SExp -> AST SMT-LIB (Command, Term, Sort)
  3. parse : String -> Option Problem
-/

inductive SExp where
  | sym  (s : String)
  | num  (n : Int)
  | str  (s : String)
  | list (xs : List SExp)
  deriving Repr, BEq

abbrev Parser (α : Type) := Std.Internal.Parsec.String.Parser α

/-- Helper: rulează un parser pe un string. -/
def runParser {α} (p : Parser α) (input : String) : Except String α :=
  p.run input

/-- Comentarii SMT-LIB: `;` până la sfârșitul liniei. -/
def comment : Parser Unit := do
  skipChar ';'
  let _ ← many (satisfy (fun c => c ≠ '\n')) -- ignorăm restul liniei
  pure ()

/-- Spații + comentarii, repetat. -/
def spaces : Parser Unit := do
  let spaceChar : Parser Unit := do
    let c ← any
    if c = ' ' || c = '\t' || c = '\r' || c = '\n' then
      pure ()
    else
      fail "whitespace expected"
  let one : Parser Unit :=
    (spaceChar *> pure ()) <|> (comment *> pure ())
  let _ ← many one
  pure ()

/-- Caracter de simbol SMT-LIB (foarte permissive, dar excludem spații, paranteze și `;`). -/
def isSymbolChar (c : Char) : Bool :=
  !c.isWhitespace && c ≠ '(' && c ≠ ')' && c ≠ ';'

def symChar : Parser Char :=
  satisfy isSymbolChar

/-- Symbol SMT-LIB (de ex: `set-logic`, `QF_LIA`, `x`, `<=`, etc.). -/
def symbol : Parser String :=
  Std.Internal.Parsec.many1Chars symChar

/-- Literal întreg (opțional sem, urmat de cifre). -/
def intLit : Parser Int := do
  let sign : Int ←
    (skipChar '-' *> pure (-1)) <|> (pure 1)
  let first ← String.digit
  let restStr ← manyChars String.digit
  let nStr := String.singleton first ++ restStr
  match nStr.toInt? with
  | some n => pure (sign * n)
  | none   => fail s!"invalid integer literal: {nStr}"

where
  /-- Helper: repetă un parser de Char într-un String. -/
  manyChars (p : Parser Char) : Parser String := do
    let chars ← many p
    pure chars.toList.asString

/-- String literal SMT-LIB simplificat (nu tratăm escape-uri sofisticate). -/
def stringLit : Parser String := do
  skipChar '"'
  let chars ← (satisfy (fun c => c ≠ '"')).manyChars
  skipChar '"'
  pure chars

/-- Paranteze: '(' și ')'. -/
def lparen : Parser Unit := skipChar '('
def rparen : Parser Unit := skipChar ')'

mutual

  /-- Parser principal pentru SExp. -/
  partial def sexp : Parser SExp := do
    spaces
    (parseList <|> parseAtom)

  /-- Listă s-expr: `(e1 e2 ... en)`. -/
  partial def parseList : Parser SExp := do
    lparen
    spaces
    let xsArr ← many sexp
    spaces
    rparen
    pure (SExp.list xsArr.toList)

  /-- Atom: simbol, număr, string. -/
  partial def parseAtom : Parser SExp := do
    spaces
    (parseNum <|> parseStr <|> parseSym)

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

/-- Parsează un script SMT-LIB ca o listă de SExp (comenzi top-level). -/
def sexpScript : Parser (List SExp) := do
  spaces
  let xsArr ← many sexp
  spaces
  eof
  pure xsArr.toList

/-
  Conversie SExp -> AST SMT-LIB
-/

namespace SExp

def asSym : SExp → Option String
  | .sym s => some s
  | _      => none

def asList : SExp → Option (List SExp)
  | .list xs => some xs
  | _        => none

end SExp

/-- Parsează un `Sort` din SExp (Bool, Int, sau identificator generic). -/
def sortOfSExp : SExp → Option sort
  | .sym "Bool" => some sort.bool
  | .sym "Int"  => some sort.int
  | .sym s      => some (sort.ident s)
  | _           => none

/-- Termen generic: variabilă, literal întreg sau aplicație. -/
mutual
  partial def termOfSExp : SExp → Option Term
    | .num n      => some (Term.intLit n)
    | .sym s      => some (Term.var s)
    | .str s      => some (Term.app s []) -- foarte simplificat
    | .list []    => none
    | .list (f :: args) =>
        match SExp.asSym f with
        | some fn =>
            let recArgs := args.mapM termOfSExp
            match recArgs with
            | some ts => some (Term.app fn ts)
            | none    => none
        | none => none

end

/-- Parsează o singură comandă SMT-LIB dintr-un SExp de top-level. -/
def commandOfSExp : SExp → Option Command
  | SExp.list (SExp.sym "set-logic" :: SExp.sym name :: []) =>
      some (Command.setLogic name)

  | SExp.list (SExp.sym "declare-fun" :: SExp.sym f
               :: SExp.list argSortsS :: resS :: []) =>
      do
        let argSorts ← argSortsS.mapM sortOfSExp
        let resSort  ← sortOfSExp resS
        pure (Command.declareFun f argSorts resSort)

  | SExp.list (SExp.sym "assert" :: t :: []) =>
      do
        let tt ← termOfSExp t
        pure (Command.assert tt)

  | SExp.list [SExp.sym "check-sat"] =>
      some Command.checkSat

  | SExp.list [SExp.sym "exit"] =>
      some Command.exit

  | _ => none

/-- Parsează un întreg script SMT-LIB într-un `Problem`. -/
def problemOfSExps (xs : List SExp) : Option Problem := do
  let cmds ← xs.mapM commandOfSExp
  pure { commands := cmds }

/-- Funcția cerută în enunț: `String → Option Problem`. -/
def parse (s : String) : Option Problem :=
  match runParser sexpScript s with
  | .ok xs     => problemOfSExps xs
  | .error _e  => none

/-
  SPECIFICAȚIE (pasul 2): Problem → Prop

  Interpretare: un script e "bine format" dacă:
    * cel mult un `set-logic`
    * niciun `declare-fun` după primul `assert` / `check-sat`
    * există cel puțin un `check-sat`
-/

def Command.isSetLogic : Command → Bool
  | .setLogic _ => true
  | _           => false

def Command.isDeclareFun : Command → Bool
  | .declareFun .. => true
  | _              => false

def Command.isAssertOrCheck : Command → Bool
  | .assert _  => true
  | .checkSat  => true
  | _          => false

def countSetLogic (p : Problem) : Nat :=
  p.commands.foldl (fun acc c => if c.isSetLogic then acc + 1 else acc) 0

def hasCheckSat (p : Problem) : Bool :=
  p.commands.any (fun c => match c with | .checkSat => true | _ => false)

/-- Nu există `declare-fun` după primul `assert` sau `check-sat`. -/
def noLateDecls (p : Problem) : Prop :=
  let rec go (phase : Bool) (cs : List Command) : Prop :=
    match cs with
    | []        => True
    | c :: rest =>
        if phase then
          -- suntem în faza "după assert/check-sat"
          if c.isDeclareFun then False else go true rest
        else
          -- înainte de primul assert/check-sat
          if c.isAssertOrCheck then go true rest else go false rest
  go false p.commands

/-- Specificația globală pentru un `Problem`. -/
def specification (p : Problem) : Prop :=
  countSetLogic p ≤ 1 ∧
  hasCheckSat p = true ∧
  noLateDecls p

/-
  Exemple de utilizare (poți pune în fișier pentru test):

  #eval parse "(set-logic QF_LIA)
               (declare-fun x () Int)
               (assert (> x 0))
               (check-sat)
               (exit)"

  #eval match parse "(check-sat)" with
        | some prob => specification prob
        | none      => False
-/

end SmtLib
