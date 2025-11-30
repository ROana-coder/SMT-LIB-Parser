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
  | declareFun (name : String) (argSorts : List sort) (resSort : sort)
  | assert     (t : Term)
  | checkSat
  | exit
  deriving Repr, BEq

structure Problem where
  commands : List Command
  deriving BEq, Repr

inductive SExp where
  | sym  (s : String)
  | num  (n : Int)
  | str  (s : String)
  | list (xs : List SExp)
  deriving Repr, BEq

abbrev Parser (α : Type) := Std.Internal.Parsec.String.Parser α

def runParser {α} (p : Parser α) (input : String) : Except String α :=
  p.run input

/-- IMPLEMENTARE ATTEMPT:
    Dacă parserul `p` eșuează, resetăm cursorul la poziția inițială `it`.
    Acest lucru este critic pentru a permite spații opționale înainte de ')' -/
def attempt {α} (p : Parser α) : Parser α := fun it =>
  match p it with
  | .success rem a => .success rem a
  | .error _ err   => .error it err

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

/-- Helper: Consumă spații, apoi încearcă parserul cu backtracking.
    Dacă `p` eșuează după ce a consumat spații, spațiile sunt puse la loc. -/
def lexeme {α} (p : Parser α) : Parser α := attempt (spaces *> p)

def parse_spaces (s : String) :=
   runParser spaces s

#eval parse_spaces ";\n "
#eval parse_spaces " 42"

/-- Caracter de simbol SMT-LIB (foarte permissive, dar excludem spații, paranteze și `;`). -/
def isSymbolChar (c : Char) : Bool :=
  !c.isWhitespace && c ≠ '(' && c ≠ ')' && c ≠ ';'

/-- Symbol SMT-LIB (de ex: `set-logic`, `QF_LIA`, `x`, `<=`, etc.). -/
def symbol : Parser String :=
  many1Chars (satisfy isSymbolChar)


#eval runParser symbol "<="

/-- Parsează un int, dar NU consumă spațiile din jur (e low-level). -/
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

#eval runParser intLit "-12345"

/-- String literal SMT-LIB simplificat (nu tratăm escape-uri sofisticate). -/
def stringLit : Parser String := do
  skipChar '"'
  let chars ← (satisfy (fun c => c ≠ '"')).manyChars
  skipChar '"'
  pure chars

-- Folosim 'lexeme' pentru paranteze ca să "înghițim" spațiul de după ele
def lparen : Parser Unit := lexeme (skipChar '(')
def rparen : Parser Unit := lexeme (skipChar ')')

#eval runParser lparen "( "
#eval runParser rparen ") "
#eval runParser lparen " ( "
#eval runParser rparen " ) "


mutual

  /-- Parser principal SExp. NU consumă spații la început! -/
  partial def sexp : Parser SExp :=
    parseList <|> parseAtom

  partial def parseList : Parser SExp := do
    lparen              -- mănâncă '(' și spațiile de după
    let xsArr ← many sexp -- fiecare sexp mănâncă spațiile de după el (via parseAtom sau parseList)
    rparen              -- mănâncă ')' și spațiile de după
    pure (SExp.list xsArr.toList)

  partial def parseAtom : Parser SExp := do
    -- Aici folosim lexeme! Citim atomul și mâncăm spațiul de după.
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

#eval runParser parseAtom " -42"
#eval runParser parseNum "-42 "

#eval runParser sexp " ( asdf  1  2 ) "
#eval runParser sexp " ( asdf  1  2) "



/-- Parsează un script SMT-LIB ca o listă de SExp (comenzi top-level). -/
def sexpScript : Parser (List SExp) := do
  spaces -- <--- AICI curățăm spațiile de la începutul fișierului
  let xsArr ← many sexp
  spaces
  eof
  pure xsArr.toList

/-
  Conversie SExp -> AST SMT-LIB
-/

def testScript := "
                 (set-logic QF_LIA)
                 (declare-fun x () Int)
                 (assert (> x 0))
                 (check-sat)
                 (exit)"

#eval runParser sexpScript testScript

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
-- FIXAT: 'mutual' a fost șters
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
  SPECIFICAȚIE (pasul 2): Problem → Bool (schimbat din Prop)

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
def noLateDecls (p : Problem) : Bool := -- FIXAT: Prop -> Bool
  let rec go (phase : Bool) (cs : List Command) : Bool := -- FIXAT: Prop -> Bool
    match cs with
    | []        => true -- FIXAT: True -> true
    | c :: rest =>
        if phase then
          -- suntem în faza "după assert/check-sat"
          if c.isDeclareFun then false else go true rest -- FIXAT: False -> false
        else
          -- înainte de primul assert/check-sat
          if c.isAssertOrCheck then go true rest else go false rest
  go false p.commands

/-- Specificația globală pentru un `Problem`. -/
def specification (p : Problem) : Bool := -- FIXAT: Prop -> Bool
  countSetLogic p ≤ 1 && -- FIXAT: ∧ -> &&
  hasCheckSat p == true && -- FIXAT: ∧ -> &&
  noLateDecls p

/-
  Exemple de utilizare (poți pune în fișier pentru test):
-/

#eval parse testScript

def testProb := parse testScript
def specResult := match testProb with
                  | some prob => specification prob
                  | none      => false

#eval specResult -- Ar trebui să afișeze 'true'

def testScriptLateDecl := "(set-logic QF_LIA)
                           (assert true)
                           (declare-fun x () Int)
                           (check-sat)"

#eval match parse testScriptLateDecl with
        | some prob => specification prob
        | none      => false -- Ar trebui să afișeze 'false'

def testScriptNoCheckSat := "(set-logic QF_LIA)
                             (declare-fun x () Int)"

#eval match parse testScriptNoCheckSat with
        | some prob => specification prob
        | none      => false -- Ar trebui să afișeze 'false'

end SmtLib
