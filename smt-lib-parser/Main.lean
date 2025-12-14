import Std

open Std
open Std.Internal.Parsec
open Std.Internal.Parsec.String

namespace SmtLib

/- ==========================================
   1. DEFINIȚII AST
   ========================================== -/

inductive sort where
  | bool
  | int
  | ident (name : String)
  deriving Repr, BEq

inductive SmtTerm where
  | var    (name : String)
  | intLit (val  : Int)
  | app    (fn   : String) (args : List SmtTerm)
  deriving Repr, BEq


inductive Command where
  | setLogic   (name : String)
  | declareFun (name : String) (argSorts : List sort) (resSort : sort)
  | assert     (t : SmtTerm)
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

/- ==========================================
   2. CONTEXT ȘI SEMNĂTURI
   ========================================== -/

structure Signature where
  args : List sort
  res  : sort
  deriving Repr, BEq

abbrev Context := List (String × Signature)

def lookup (ctx : Context) (name : String) : Option Signature :=
  ctx.lookup name

def initialContext : Context := [
  -- Teoria Core
  ("true",  Signature.mk [] sort.bool),
  ("false", Signature.mk [] sort.bool),
  ("not",   Signature.mk [sort.bool] sort.bool),
  ("and",   Signature.mk [sort.bool, sort.bool] sort.bool),
  ("or",    Signature.mk [sort.bool, sort.bool] sort.bool),
  ("xor",   Signature.mk [sort.bool, sort.bool] sort.bool),
  ("=>",    Signature.mk [sort.bool, sort.bool] sort.bool),

  -- Teoria Ints
  ("+",     Signature.mk [sort.int, sort.int] sort.int),
  ("-",     Signature.mk [sort.int, sort.int] sort.int),
  ("*",     Signature.mk [sort.int, sort.int] sort.int),
  ("div",   Signature.mk [sort.int, sort.int] sort.int),
  ("<",     Signature.mk [sort.int, sort.int] sort.bool),
  (">",     Signature.mk [sort.int, sort.int] sort.bool),
  ("<=",    Signature.mk [sort.int, sort.int] sort.bool),
  (">=",    Signature.mk [sort.int, sort.int] sort.bool),
  ("=",     Signature.mk [sort.int, sort.int] sort.bool) -- Simplificare pt start
]

/- ==========================================
   3. PARSER CORE
   ========================================== -/

abbrev Parser (α : Type) := Std.Internal.Parsec.String.Parser α

def runParser {α} (p : Parser α) (input : String) : Except String α :=
  p.run input

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
   4. CONVERSIE SEXP -> AST
   ========================================== -/

namespace SExp
def asSym : SExp → Option String | .sym s => some s | _ => none
def asList : SExp → Option (List SExp) | .list xs => some xs | _ => none
end SExp

def sortOfSExp : SExp → Option sort
  | .sym "Bool" => some sort.bool
  | .sym "Int"  => some sort.int
  | .sym s      => some (sort.ident s)
  | _           => none

partial def SmtTermOfSExp : SExp → Option SmtTerm
  | .num n      => some (SmtTerm.intLit n)
  | .sym s      => some (SmtTerm.var s)
  | .str s      => some (SmtTerm.app s [])
  | .list []    => none
  | .list (f :: args) =>
      match SExp.asSym f with
      | some fn =>
          let recArgs := args.mapM SmtTermOfSExp
          match recArgs with
          | some ts => some (SmtTerm.app fn ts)
          | none    => none
      | none => none

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
        let tt ← SmtTermOfSExp t
        pure (Command.assert tt)
  | SExp.list [SExp.sym "check-sat"] => some Command.checkSat
  | SExp.list [SExp.sym "exit"] => some Command.exit
  | _ => none

def problemOfSExps (xs : List SExp) : Option Problem := do
  let cmds ← xs.mapM commandOfSExp
  pure { commands := cmds }

def parse (s : String) : Option Problem :=
  match runParser sexpScript s with
  | .ok xs     => problemOfSExps xs
  | .error _e  => none

/- ==========================================
   5. SEMANTICĂ (CHECKER TIPURI)
   ========================================== -/

-- Pasul 3: Inferența Tipurilor
partial def inferSort (ctx : Context) (t : SmtTerm) : Option sort :=
  match t with
  | SmtTerm.intLit _ => some sort.int

  | SmtTerm.var name =>
      match lookup ctx name with
      | some sig => if sig.args.isEmpty then some sig.res else none
      | none     => none

  | SmtTerm.app "=" [t1, t2] => do
      let s1 ← inferSort ctx t1
      let s2 ← inferSort ctx t2
      if s1 == s2 then some sort.bool else none

  | SmtTerm.app fn args => do
      let sig ← lookup ctx fn
      if sig.args.length != args.length then none
      else
        let argSorts ← args.mapM (inferSort ctx)
        if argSorts == sig.args then some sig.res else none

-- Pasul 4: Validarea Secvențială
def checkCommand (ctx : Context) (cmd : Command) : Option Context :=
  match cmd with
  | Command.declareFun name args res =>
      let newSig := Signature.mk args res
      some ((name, newSig) :: ctx)

  | Command.assert t =>
      match inferSort ctx t with
      | some sort.bool => some ctx
      | _ => none

  | _ => some ctx

def checkScript (cmds : List Command) : Bool :=
  let result := cmds.foldl (fun ctxOpt cmd =>
    match ctxOpt with
    | some ctx => checkCommand ctx cmd
    | none     => none
  ) (some initialContext)

  result.isSome

/- ==========================================
   6. SPECIFICAȚIE FINALĂ
   ========================================== -/

def Command.isSetLogic : Command → Bool | .setLogic _ => true | _ => false
def Command.isDeclareFun : Command → Bool | .declareFun .. => true | _ => false
def Command.isAssertOrCheck : Command → Bool | .assert _ => true | .checkSat => true | _ => false
def countSetLogic (p : Problem) : Nat := p.commands.foldl (fun acc c => if c.isSetLogic then acc + 1 else acc) 0
def hasCheckSat (p : Problem) : Bool := p.commands.any (fun c => match c with | .checkSat => true | _ => false)

def noLateDecls (p : Problem) : Bool :=
  let rec go (phase : Bool) (cs : List Command) : Bool :=
    match cs with
    | []        => true
    | c :: rest =>
        if phase then if c.isDeclareFun then false else go true rest
        else if c.isAssertOrCheck then go true rest else go false rest
  go false p.commands

def specification (p : Problem) : Bool :=
  countSetLogic p ≤ 1 &&
  hasCheckSat p == true &&
  noLateDecls p &&
  checkScript p.commands -- <--- Validarea Semantică Integrată

/- ==========================================
   7. TESTE
   ========================================== -/

/- ==========================================
   HELPER PENTRU TESTARE RAPIDĂ
   ========================================== -/

/-- Funcție ajutătoare care parsează și verifică specificația într-un singur pas. -/
def runTest (script : String) : String :=
  match parse script with
  | some prob =>
      if specification prob then "✅ VALID (Semantic Corect)"
      else "❌ INVALID (Eroare Semantică sau de Structură)"
  | none => "💥 EROARE PARSARE (Sintaxă Greșită)"

/- ==========================================
   SUITĂ DE TESTE PENTRU EGALITATE (=)
   ========================================== -/

-- 1. Test Egalitate Variabile INT (x, y : Int) -> AR TREBUI SĂ FIE VALID
-- Verifică: (= Int Int) -> Bool
def testIntEq := "
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= x y))
(check-sat)"

#eval runTest testIntEq


-- 2. Test Egalitate Variabile BOOL (p, q : Bool) -> AR TREBUI SĂ FIE VALID
-- Verifică: (= Bool Bool) -> Bool
def testBoolEq := "
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (= p q))
(check-sat)"

#eval runTest testBoolEq


-- 3. Test MIX Tipurilor (Int == Bool) -> AR TREBUI SĂ FIE INVALID
-- Verifică: (= Int Bool) -> Error
def testMixedEq := "
(declare-fun x () Int)
(declare-fun p () Bool)
(assert (= x p))
(check-sat)"

#eval runTest testMixedEq


-- 4. Test Literal cu Variabilă (Int == IntLit) -> AR TREBUI SĂ FIE VALID
-- Verifică: (= Int Int) -> Bool
def testLitEq := "
(declare-fun x () Int)
(assert (= x 42))
(check-sat)"

#eval runTest testLitEq


-- 5. Test Literal Greșit (Int == BoolLit) -> AR TREBUI SĂ FIE INVALID
-- Verifică: (= Int Bool) -> Error
def testLitError := "
(declare-fun x () Int)
(assert (= x true))
(check-sat)"

#eval runTest testLitError


-- 6. Test Nested (Egalitate în Egalitate) -> AR TREBUI SĂ FIE INVALID
-- Explicatie: (= x y) returnează Bool.
-- Deci expresia devine (= Bool 5), adică (= Bool Int), ceea ce e greșit.
def testNestedError := "
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (= x y) 5))
(check-sat)"

#eval runTest testNestedError


/- ==========================================
   8. INTERPRETARE LOGICĂ (Execuție Simbolică)
   Transformăm AST-ul SmtTerm direct în Prop Lean.
   ========================================== -/

/-- Helper: Parsează un string direct într-o comandă (fără a face listă). -/
def parseAssert (s : String) : Option Command :=
  match runParser sexp s with
  | .ok xs     => commandOfSExp xs
  | .error _e  => none

-- Testare parsing assert
def testAssertStr := "(assert (> 7 0))"
#eval runParser sexp testAssertStr -- Verificăm S-Expression-ul brut
#eval parseAssert testAssertStr    -- Verificăm Command-ul parsat

/-- Interpretează un SmtTerm ca o Prop Lean (marcată ca reducible pentru #reduce).
    Aici facem legătura între sintaxa SMT și matematica din Lean. -/
@[reducible]
def termToProp : SmtTerm → Option Prop
  | SmtTerm.app ">" [SmtTerm.intLit a, SmtTerm.intLit b] => some (a > b)
  | SmtTerm.app "<" [SmtTerm.intLit a, SmtTerm.intLit b] => some (a < b)
  | SmtTerm.app "=" [SmtTerm.intLit a, SmtTerm.intLit b] => some (a = b)
  | SmtTerm.app ">=" [SmtTerm.intLit a, SmtTerm.intLit b] => some (a ≥ b)
  | SmtTerm.app "<=" [SmtTerm.intLit a, SmtTerm.intLit b] => some (a ≤ b)
  -- Putem adăuga și True/False explicit
  | SmtTerm.app "true" []  => some True
  | SmtTerm.app "false" [] => some False
  | _ => none

/-- Extrage propoziția logică dintr-o comandă assert. -/
@[reducible]
def specAssert (c : Command) : Option Prop :=
  match c with
  | .assert t => termToProp t
  | _         => none

/-
   DEMONSTRAȚIE #reduce
   Lean va evalua expresia matematică 7 > 0.
-/
#reduce specAssert (Command.assert (SmtTerm.app ">" [SmtTerm.intLit 7, SmtTerm.intLit 0]))
-- Rezultat așteptat: some (7 > 0)
-- Deoarece 7 > 0 este decidabil, Lean știe că este adevărat.

#reduce specAssert (Command.assert (SmtTerm.app "<" [SmtTerm.intLit 10, SmtTerm.intLit 2]))
-- Rezultat așteptat: some (10 < 2) (care este False matematic)

end SmtLib
