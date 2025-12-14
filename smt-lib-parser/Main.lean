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
  | defineFun  (name : String) (args : List (String × sort)) (resSort : sort) (body : SmtTerm)
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

def parseSortedVar : SExp → Option (String × sort)
  | SExp.list [SExp.sym name, s] =>
      match sortOfSExp s with
      | some srt => some (name, srt)
      | none => none
  | _ => none

def commandOfSExp : SExp → Option Command
  | SExp.list (SExp.sym "set-logic" :: SExp.sym name :: []) =>
      some (Command.setLogic name)
  | SExp.list (SExp.sym "declare-fun" :: SExp.sym f
               :: SExp.list argSortsS :: resS :: []) =>
      do
        let argSorts ← argSortsS.mapM sortOfSExp
        let resSort  ← sortOfSExp resS
        pure (Command.declareFun f argSorts resSort)
  | SExp.list (SExp.sym "define-fun" :: SExp.sym name
               :: SExp.list argsS :: resS :: bodyS :: []) =>
      do
        let args ← argsS.mapM parseSortedVar -- Parsează lista de argumente ((x Int)...)
        let resSort ← sortOfSExp resS        -- Parsează tipul returnat
        let body ← SmtTermOfSExp bodyS       -- Parsează corpul funcției
        pure (Command.defineFun name args resSort body)
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
def inferSort (ctx : Context) (t : SmtTerm) : Option sort :=
  match t with
  | SmtTerm.intLit _ => some sort.int

  | SmtTerm.var name =>
      match lookup ctx name with
      | some sig => if sig.args.isEmpty then some sig.res else none
      | none     => none

  -- Cazul special: Egalitatea (= a b)
  | SmtTerm.app "=" [t1, t2] => do
      let s1 ← inferSort ctx t1
      let s2 ← inferSort ctx t2
      if s1 == s2 then some sort.bool else none

  -- NOU: Cazul special IF-THEN-ELSE (ite cond then else)
  | SmtTerm.app "ite" [cond, t1, t2] => do
      let sCond ← inferSort ctx cond -- 1. Condiția trebuie să aibă un tip
      let s1    ← inferSort ctx t1   -- 2. Ramura then
      let s2    ← inferSort ctx t2   -- 3. Ramura else

      -- Regula SMT-LIB: Condiția e Bool, și ramurile sunt identice ca tip
      if sCond == sort.bool && s1 == s2 then
        some s1
      else
        none

  -- Cazul general: Aplicarea unei funcții standard
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
  -- LOGICA NOUĂ PENTRU define-fun
  | Command.defineFun name args resSort body =>
      -- 1. Creăm un context local: Adăugăm argumentele (x, y) peste contextul global
      --    Astfel, corpul funcției va ști că 'x' este un Int.
      let localCtx := args.foldl (fun c (argName, argSort) =>
          (argName, Signature.mk [] argSort) :: c
      ) ctx

      -- 2. Verificăm tipul corpului în contextul local
      match inferSort localCtx body with
      | some bodySort =>
          -- 3. Corpul trebuie să returneze exact ce a promis funcția (resSort)
          if bodySort == resSort then
             -- 4. Succes! Adăugăm funcția în contextul global (fără numele argumentelor, doar tipurile)
             let argTypes := args.map (·.2)
             let newSig := Signature.mk argTypes resSort
             some ((name, newSig) :: ctx)
          else
             none -- Eroare: Corpul are alt tip decât cel declarat
      | none => none -- Eroare: Corpul este invalid (ex: variabilă necunoscută)

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

/-- Helper pentru a combina o listă de propoziții cu AND/OR logic din Lean. -/
def foldProp (op : Prop → Prop → Prop) (base : Prop) (args : List Prop) : Prop :=
  args.foldr op base

/-- Interpretează un SmtTerm ca o Prop Lean (marcată ca reducible pentru #reduce).
    Aici facem legătura între sintaxa SMT și matematica din Lean. -/
@[reducible]
def termToProp : SmtTerm → Option Prop
  -- 1. Constante Booleene (Verificăm întâi Variabilele, cum le scoate parserul)
  | SmtTerm.var "true"   => some True
  | SmtTerm.var "false"  => some False

  -- 1.1 Constante Booleene (Cazul rar când sunt scrise ca aplicații: (true))
  | SmtTerm.app "true" []  => some True
  | SmtTerm.app "false" [] => some False

  -- 2. Aritmetică
  | SmtTerm.app ">" [SmtTerm.intLit a, SmtTerm.intLit b] => some (a > b)
  | SmtTerm.app "<" [SmtTerm.intLit a, SmtTerm.intLit b] => some (a < b)
  | SmtTerm.app "=" [SmtTerm.intLit a, SmtTerm.intLit b] => some (a = b)
  | SmtTerm.app ">=" [SmtTerm.intLit a, SmtTerm.intLit b] => some (a ≥ b)
  | SmtTerm.app "<=" [SmtTerm.intLit a, SmtTerm.intLit b] => some (a ≤ b)

  -- 3. Operatori Logici
  | SmtTerm.app "not" [t] =>
      match termToProp t with
      | some p => some (¬p)
      | none => none

  | SmtTerm.app "and" args =>
      match args.mapM termToProp with
      | some ps => some (foldProp And True ps)
      | none => none

  | SmtTerm.app "or" args =>
      match args.mapM termToProp with
      | some ps => some (foldProp Or False ps)
      | none => none

  -- 4. Implicația (Fixat eroarea 'Expected 2')
  | SmtTerm.app "=>" [t1, t2] =>
      match termToProp t1, termToProp t2 with
      | some p1, some p2 => some (p1 → p2)
      | _, _ => none -- Aici folosim două underscore-uri!

  -- 5. If-Then-Else
  | SmtTerm.app "ite" [c, t, e] =>
      match termToProp c, termToProp t, termToProp e with
      | some pc, some pt, some pe => some ((pc → pt) ∧ (¬pc → pe))
      | _, _, _ => none -- Aici folosim trei underscore-uri!

  -- 6. Catch-All (TREBUIE SĂ FIE ULTIMUL!)
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


/-- Transformă un SmtTerm înapoi într-un String citibil (matematic & logic). -/
partial def termToString (t : SmtTerm) : String :=
  match t with
  | SmtTerm.intLit n => toString n
  | SmtTerm.var s    => s

  -- 1. Logică Booleană (Simboluri Matematice)
  | SmtTerm.app "not" [x] => s!"(¬ {termToString x})"
  | SmtTerm.app "and" args => s!"({String.intercalate " ∧ " (args.map termToString)})"
  | SmtTerm.app "or"  args => s!"({String.intercalate " ∨ " (args.map termToString)})"
  | SmtTerm.app "=>"  [a, b] => s!"({termToString a} → {termToString b})"

  -- 2. If-Then-Else
  | SmtTerm.app "ite" [c, t, e] => s!"(if {termToString c} then {termToString t} else {termToString e})"

  -- 3. Aritmetică (Infix)
  | SmtTerm.app op [a, b] =>
      if ["=", ">", "<", ">=", "<=", "+", "-", "*"].contains op then
        s!"({termToString a} {op} {termToString b})"
      else
        -- Default Prefix: (f x y)
        s!"({op} {termToString a} {termToString b})"

  -- 4. General
  | SmtTerm.app fn args =>
      s!"({fn} {String.intercalate " " (args.map termToString)})"


/-- Extrage și afișează condiția dintr-un assert. -/
def showCondition (input : String) : String :=
  match parseAssert input with
  | none => "Eroare Parsare"
  | some cmd =>
      match cmd with
      | Command.assert t => termToString t
      | _ => "Nu este o comandă assert"

-- 1. Test simplu
#eval showCondition "(assert (> 10 2))"
-- Rezultat: "Condiția este: (10 > 2)"

-- 2. Test cu variabile (acum le poți vedea!)
#eval showCondition "(assert (= x y))"
-- Rezultat: "Condiția este: (x = y)"

-- 3. Test complex (imbricat)
#eval showCondition "(assert (> (+ x 1) 10))"
-- Rezultat: "Condiția este: ((x + 1) > 10)"


-- TEST DEFINE-FUN + ASSERT
def testDefine := "
(define-fun inc ((x Int)) Int (+ x 1))
(assert (= (inc 5) 6))
(check-sat)"

-- Ar trebui să fie VALID (Semantic)
#eval match parse testDefine with
      | some prob => specification prob
      | none      => false
-- Rezultat: true


-- TEST EROARE (Corp greșit)
-- Funcția promite Int, dar returnează Bool (> x 1)
def testDefineError := "
(define-fun bad ((x Int)) Int (> x 1))
(check-sat)"

#eval match parse testDefineError with
      | some prob => specification prob
      | none      => false
-- Rezultat: false

/-- Helper pentru evaluarea booleană a listelor (pentru AND/OR) -/
def foldBool (op : Bool → Bool → Bool) (base : Bool) (args : List Bool) : Bool :=
  args.foldr op base

/-- Evaluator Boolean complet (Aritmetică + Logică) -/
partial def evalTerm : SmtTerm → Option Bool
  -- Constante
  | SmtTerm.var "true"   => some true
  | SmtTerm.var "false"  => some false
  | SmtTerm.app "true" [] => some true
  | SmtTerm.app "false" [] => some false

  -- Aritmetică
  | SmtTerm.app ">" [SmtTerm.intLit a, SmtTerm.intLit b] => some (a > b)
  | SmtTerm.app "<" [SmtTerm.intLit a, SmtTerm.intLit b] => some (a < b)
  | SmtTerm.app "=" [SmtTerm.intLit a, SmtTerm.intLit b] => some (a == b)

  -- NOU: IF-THEN-ELSE (Doar boolean)
  | SmtTerm.app "ite" [c, t, e] =>
      match evalTerm c with
      | some condVal =>
          if condVal then evalTerm t else evalTerm e
      | none => none

  -- Logică
  | SmtTerm.app "not" [t] =>
      match evalTerm t with | some b => some (!b) | _ => none
  | SmtTerm.app "and" args =>
      match args.mapM evalTerm with | some bs => some (foldBool (· && ·) true bs) | _ => none
  | SmtTerm.app "or" args =>
      match args.mapM evalTerm with | some bs => some (foldBool (· || ·) false bs) | _ => none

  | _ => none


-- Testează parserul cu un simbol boolean
#reduce specAssert (Command.assert (SmtTerm.var "true"))
-- Rezultat: some True

/-- Testează folosind #eval (mult mai rapid și fără erori de recursivitate) -/
def testLogicComplex := Command.assert
  (SmtTerm.app "or" [
      SmtTerm.var "true",
      SmtTerm.app ">" [SmtTerm.intLit 1, SmtTerm.intLit 5]
  ])

#eval match testLogicComplex with
      | .assert t => evalTerm t
      | _ => none
-- Rezultat: some true

-- Definim un string SMT complex
def complexLogicTest := "
(assert
  (=>
    (and (> x 0) (< x 10))
    (or (= x 100) (not (= x 5)))
  )
)"

-- Afișăm cum l-a înțeles parserul
#eval showCondition complexLogicTest


-- 1. Test Vizualizare (Formatare)
def iteString := "(assert (ite (> x 0) (= y 1) (= y 2)))"
#eval showCondition iteString
-- Rezultat: "Condiția este: (if (x > 0) then (y = 1) else (y = 2))"


-- 2. Test Semantic (Tipuri)
-- Verificăm un ITE valid: (ite Bool Int Int) -> Int
def testIteValid := "
(declare-fun x () Int)
(assert
   (=
     (ite (> x 0) 10 20)
     10
   )
)
(check-sat)"

#eval runTest testIteValid
-- Rezultat: "✅ VALID (Semantic Corect)"


-- 3. Test Semantic Invalid
-- Verificăm (ite Bool Int Bool) -> Eroare (ramuri diferite)
def testIteInvalid := "
(declare-fun x () Int)
(assert
   (ite (> x 0) 10 true)
)
(check-sat)"

#eval runTest testIteInvalid
-- Rezultat: "❌ INVALID (Eroare Semantică...)"

/-- Extrage valoarea booleană dintr-o comandă assert. -/
def evalAssert (c : Command) : Option Bool :=
  match c with
  | .assert t => evalTerm t
  | _         => none

/-- Parsează, Interpretează și Evaluează. -/
def evaluateAssert (input : String) : String :=
  match parseAssert input with
  | none => "💥 Eroare Parsare"
  | some cmd =>
      match evalAssert cmd with
      | none => "❌ Nu am putut evalua (variabile necunoscute sau tipuri ne-booleene)"
      | some b =>
          if b then "✅ TRUE" else "❌ FALSE"

-- 4. Test Execuție (Evaluare Logică)
-- (if true then false else true) -> false
#eval evaluateAssert "(assert (ite true false true))"
-- Rezultat: "❌ FALSE" (Corect!)

#eval evaluateAssert "(assert (ite false false true))"
-- Rezultat: "✅ TRUE" (Corect!)

#eval evaluateAssert "(assert (ite false 2 3))" -- TO DO: make this work
-- Rezultat: "❌ Nu am putut evalua..."


/- ==========================================
   10. PIPELINE-UL DE SIGURANȚĂ (RunSafe)
   ========================================== -/

-- 1. Definim un helper pentru a parsa rapid un string într-o comandă
def parseHelper (s : String) : Option Command :=
  match runParser sexp s with
  | .ok xs     => commandOfSExp xs
  | .error _e  => none

-- 2. Funcția RunSafe - Leagă componentele existente
def runSafe (input : String) : String :=
  -- PASUL 1: Parser
  match parseHelper input with
  | none => "💥 Eroare Sintactică (Parser)"
  | some cmd =>
      -- PASUL 2: Checker (Verifică tipurile folosind initialContext)
      -- Aici se verifică dacă (assert ...) primește un Bool.
      match checkCommand initialContext cmd with
      | none => "⛔ EROARE SEMANTICĂ: Tipuri greșite (Checker a respins comanda)!"
      | some _ =>
          -- PASUL 3: Evaluator (Execută doar dacă Checker-ul a zis DA)
          -- Folosim funcția ta existentă 'evalAssert' care returnează Option Bool
          match evalAssert cmd with
          | some true  => "✅ TRUE"
          | some false => "❌ FALSE"
          | none       => "❓ Eroare Runtime (Evaluatorul nu a putut calcula)"

/- ==========================================
   TESTE FINALE
   ========================================== -/

-- 1. Test Valid (Trece prin tot pipeline-ul)
#eval runSafe "(assert (> 10 5))"
-- Rezultat: "✅ TRUE"

-- 2. Test Invalid Semantic (Respins de Checker)
-- Deși 10+32 e un calcul valid, un 'assert' cere Bool.
-- Checker-ul tău ('checkCommand') funcționează corect și respinge asta!
#eval runSafe "(assert (+ 10 32))"
-- Rezultat: "⛔ EROARE SEMANTICĂ..."

-- 3. Test Invalid Semantic (Mix de tipuri)
#eval runSafe "(assert (ite true 10 false))"
-- Rezultat: "⛔ EROARE SEMANTICĂ..."

#eval runSafe "(assert (ite true true false))"

-- test pentru conditie complexa
def complexCondition := "
(assert
  (ite
    (and (> 2 0) (< 2 10))
    (or (= 2 5) (= 2 7))
    false
  )
)"
#eval runSafe complexCondition

end SmtLib
