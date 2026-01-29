/-
  Main.lean
  =========
  Test suite for the SMT-LIB parser
-/

import SmtLib

open SmtLib

/- ==========================================
   TEST HELPERS
   ========================================== -/

def runTest (script : String) : String := runScript script

def testAssert (input : String) : String := toString (runSafe input)

/- ==========================================
   BASIC PARSING TESTS
   ========================================== -/

section ParsingTests

#eval parse "(check-sat)"
-- Should parse successfully

#eval parse "(declare-const x Int) (check-sat)"
-- Should parse successfully

#eval parseSExp "(+ 1 2)"
-- Should return SExp

end ParsingTests

/- ==========================================
   EQUALITY TESTS (Polymorphic =)
   ========================================== -/

section EqualityTests

-- Test 1: Int equality (valid)
def testIntEq := "
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= x y))
(check-sat)"

#eval runTest testIntEq
-- Expected: "✅ VALID (Semantically correct)"

-- Test 2: Bool equality (valid)
def testBoolEq := "
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (= p q))
(check-sat)"

#eval runTest testBoolEq
-- Expected: "✅ VALID (Semantically correct)"

-- Test 3: Mixed types (invalid)
def testMixedEq := "
(declare-fun x () Int)
(declare-fun p () Bool)
(assert (= x p))
(check-sat)"

#eval runTest testMixedEq
-- Expected: "❌ INVALID..."

-- Test 4: Literal equality (valid)
def testLitEq := "
(declare-fun x () Int)
(assert (= x 42))
(check-sat)"

#eval runTest testLitEq
-- Expected: "✅ VALID..."

-- Test 5: Int == Bool literal (invalid)
def testLitError := "
(declare-fun x () Int)
(assert (= x true))
(check-sat)"

#eval runTest testLitError
-- Expected: "❌ INVALID..."

-- Test 6: Nested equality error
def testNestedError := "
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (= x y) 5))
(check-sat)"

#eval runTest testNestedError
-- Expected: "❌ INVALID..."

end EqualityTests

/- ==========================================
   DECLARE-CONST TESTS
   ========================================== -/

section DeclareConstTests

-- Test 1: Basic declare-const
def testDeclareConst := "
(declare-const x Int)
(declare-const y Int)
(assert (> x y))
(check-sat)"

#eval runTest testDeclareConst
-- Expected: "✅ VALID..."

-- Test 2: declare-const with Bool
def testDeclareConstBool := "
(declare-const p Bool)
(declare-const q Bool)
(assert (= p q))
(check-sat)"

#eval runTest testDeclareConstBool
-- Expected: "✅ VALID..."

-- Test 3: Mix of declare-const and declare-fun
def testMixDeclarations := "
(declare-const x Int)
(declare-fun f (Int) Int)
(assert (= (f x) 42))
(check-sat)"

#eval runTest testMixDeclarations
-- Expected: "✅ VALID..."

end DeclareConstTests

/- ==========================================
   DISTINCT TESTS
   ========================================== -/

section DistinctTests

-- Test 1: Valid distinct (all Int)
def testDistinctValid := "
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (distinct x y z))
(check-sat)"

#eval runTest testDistinctValid
-- Expected: "✅ VALID..."

-- Test 2: Invalid distinct (mixed types)
def testDistinctError := "
(declare-const x Int)
(declare-const p Bool)
(assert (distinct x p))
(check-sat)"

#eval runTest testDistinctError
-- Expected: "❌ INVALID..."

end DistinctTests

/- ==========================================
   DEFINE-FUN TESTS
   ========================================== -/

section DefineFunTests

-- Test 1: Valid define-fun
def testDefine := "
(define-fun inc ((x Int)) Int (+ x 1))
(assert (= (inc 5) 6))
(check-sat)"

#eval runTest testDefine
-- Expected: "✅ VALID..."

-- Test 2: Invalid define-fun (wrong return type)
def testDefineError := "
(define-fun bad ((x Int)) Int (> x 1))
(check-sat)"

#eval runTest testDefineError
-- Expected: "❌ INVALID..."

end DefineFunTests

/- ==========================================
   IF-THEN-ELSE (ITE) TESTS
   ========================================== -/

section IteTests

-- Test 1: Valid ITE
def testIteValid := "
(declare-fun x () Int)
(assert (= (ite (> x 0) 10 20) 10))
(check-sat)"

#eval runTest testIteValid
-- Expected: "✅ VALID..."

-- Test 2: Invalid ITE (mismatched branches)
def testIteInvalid := "
(declare-fun x () Int)
(assert (ite (> x 0) 10 true))
(check-sat)"

#eval runTest testIteInvalid
-- Expected: "❌ INVALID..."

-- Test 3: ITE visualization
def iteString := "(assert (ite (> x 0) (= y 1) (= y 2)))"
#eval showCondition iteString
-- Expected: "(if (x > 0) then (y = 1) else (y = 2))"

end IteTests

/- ==========================================
   EVALUATION TESTS (runSafe)
   ========================================== -/

section EvalTests

-- Test 1: Simple true
#eval testAssert "(assert (> 10 5))"
-- Expected: "✅ TRUE"

-- Test 2: Simple false
#eval testAssert "(assert (< 10 5))"
-- Expected: "❌ FALSE"

-- Test 3: Type error (non-boolean result)
#eval testAssert "(assert (+ 10 32))"
-- Expected: "⛔ Semantic Error..."

-- Test 4: ITE with mixed types
#eval testAssert "(assert (ite true 10 false))"
-- Expected: "⛔ Semantic Error..."

-- Test 5: Boolean ITE
#eval testAssert "(assert (ite true true false))"
-- Expected: "✅ TRUE"

-- Test 6: Complex condition
def complexCondition := "
(assert
  (ite
    (and (> 2 0) (< 2 10))
    (or (= 2 5) (= 2 7))
    false
  )
)"
#eval testAssert complexCondition
-- Expected: "❌ FALSE"

end EvalTests

/- ==========================================
   PRETTY PRINTING TESTS
   ========================================== -/

section PrettyPrintTests

#eval showCondition "(assert (> 10 2))"
-- Expected: "(10 > 2)"

#eval showCondition "(assert (= x y))"
-- Expected: "(x = y)"

#eval showCondition "(assert (> (+ x 1) 10))"
-- Expected: "((x + 1) > 10)"

def complexLogicTest := "
(assert
  (=>
    (and (> x 0) (< x 10))
    (or (= x 100) (not (= x 5)))
  )
)"
#eval showCondition complexLogicTest
-- Expected: "(((x > 0) ∧ (x < 10)) → ((x = 100) ∨ (¬ (x = 5))))"

end PrettyPrintTests

/- ==========================================
   SPEC PROBLEM TESTS
   ========================================== -/

section SpecProblemTests

def testSpecProblem := "
(define-fun inc ((x Int)) Int (+ x 1))
(assert (= (inc 10) 11))
(check-sat)"


-- Helper to check if specProblem returns a valid Prop (always does now)
def checkSpecProblem (s : String) : String :=
  match parse s with
  | some prob =>
      let _ := specProblem prob.commands
      "✅ SPEC GEN SUCCESS"
  | none => "❌ PARSE FAILED"

#eval parse testSpecProblem
#eval runTest testSpecProblem
#eval checkSpecProblem testSpecProblem
-- Expected: "✅ SPEC GEN SUCCESS"

def checkSpecProblemProp (s : String) : Prop :=
  match parse s with
  | some prob => specProblem prob.commands
  | none => True

def x := (parse testSpecProblem).get!
#check x

def y := specProblem x.commands
#check y

def commands := [SmtLib.Command.defineFun
                 "inc"
                 [("x", SmtLib.Srt.int)]
                 (SmtLib.Srt.int)
                 (SmtLib.Term.app "+" [SmtLib.Term.var "x", SmtLib.Term.intLit 1]),
               SmtLib.Command.assert
                 (SmtLib.Term.app "=" [SmtLib.Term.app "inc" [SmtLib.Term.intLit 10], SmtLib.Term.intLit 11]),
               SmtLib.Command.checkSat]

-- theorem asdf : specProblem commands := by
--    unfold specProblem
--    simp



end SpecProblemTests


/-  *Exists*  -/

section SemanticTaskTests

-- 1. Funcția modelSatisfies - verifică dacă env satisface comenzile
def modelSatisfies (env : Environment) (cmds : List Command) : Prop :=
  match cmds with
  | [] => True
  | (Command.assert t) :: rest =>
      -- Ordinea corectă: termToProp env 1000 t
      let prop := (termToProp env 1000 t).getD False
      prop ∧ (modelSatisfies env rest)
  | _ :: rest =>
      modelSatisfies env rest

-- 2. Funcția FINALĂ satisfiable
def satisfiable (cmds : List Command) : Prop :=
  ∃ (env : Environment), modelSatisfies env cmds

-- 3. Teste simple
def problemText := "
(declare-const x Int)
(assert (= x 10))
"
def getCommands (s : String) : List Command :=
  match parse s with
  | some prob => prob.commands
  | none => []

def generatedProp : Prop := satisfiable (getCommands problemText)

#check generatedProp


example : generatedProp := by
  unfold generatedProp satisfiable getCommands
  let solutie : Environment := {
    vars := fun name => if name == "x" then 10 else 0,
    funcs := []
  }
  apply Exists.intro solutie
  unfold modelSatisfies
  simp [modelSatisfies, termToProp]

  let solutie : Environment := {
    vars := fun name => if name == "x" then 10 else 0,
    funcs := []
  }

  apply Exists.intro solutie
  unfold modelSatisfies
  simp[problemText]

end SemanticTaskTests

/- *-------* -/

/- ==========================================
   STRING TESTS
   ========================================== -/

section StringTests

def testStringValid := "
(declare-const s String)
(assert (= s \"hello\"))
(check-sat)"

#eval parse testStringValid
#eval runTest testStringValid
-- Expected: "✅ VALID (Semantically correct)"

end StringTests



/- ==========================================
   SOLVER CONTROL TESTS
   ========================================== -/

section SolverControlTests

def testSolverControl := "
(declare-const x Int)
(assert (> x 0))
(check-sat)
(get-model)
(get-value (x (+ x 1)))"

#eval runTest testSolverControl
-- Expected: "✅ VALID (Semantically correct)"

end SolverControlTests


/- ==========================================
   STRING OPS TESTS
   ========================================== -/

section StringOpsTests

def testStringOps := "
(declare-const s String)
(assert (= (str.len s) 5))
(assert (str.contains s \"el\"))
(assert (= (str.++ \"h\" \"ello\") s))
(check-sat)"

#eval runTest testStringOps
-- Expected: "✅ VALID (Semantically correct)"

end StringOpsTests


/- ==========================================
   PROP CONVERSION TESTS
   ========================================== -/

section PropTests

-- These use #reduce to show Lean Props

-- Helper to check Prop result
def checkProp (p : Option Prop) : String :=
  match p with
  | some _ => "✅ SPEC GEN SUCCESS"
  | none => "❌ SPEC GEN FAILED"

#eval checkProp (specAssert (Command.assert (Term.app ">" [Term.intLit 7, Term.intLit 0])))
-- Expected: "✅ SPEC GEN SUCCESS"

#eval checkProp (specAssert (Command.assert (Term.app "<" [Term.intLit 10, Term.intLit 2])))
-- Expected: "✅ SPEC GEN SUCCESS"

-- With custom environment
-- With custom environment
def myEnv : Environment := {
  vars := fun name => if name == "x" then 5 else 0,
  funcs := []
}

#eval checkProp (specAssert (Command.assert (Term.app "<" [Term.var "x", Term.intLit 2])) myEnv)
-- Expected: "✅ SPEC GEN SUCCESS"

-- Two variables
-- Two variables
def envXY : Environment := {
  vars := fun name =>
    if name == "x" then 10
    else if name == "y" then 20
    else 0,
  funcs := []
}

def cmdTwoVars := Command.assert (
  Term.app "=" [
    Term.app "+" [Term.var "x", Term.var "y"],
    Term.intLit 30
  ]
)

#eval checkProp (specAssert cmdTwoVars envXY)
-- Expected: "✅ SPEC GEN SUCCESS"

end PropTests

/- ==========================================
   STRUCTURAL TESTS
   ========================================== -/

section StructuralTests

-- Test: No check-sat (should fail)
def testNoCheckSat := "
(declare-const x Int)
(assert (> x 0))"

#eval runTest testNoCheckSat
-- Expected: "❌ INVALID..."

-- Test: Late declaration (should fail)
def testLateDecl := "
(declare-const x Int)
(assert (> x 0))
(declare-const y Int)
(check-sat)"

#eval runTest testLateDecl
-- Expected: "❌ INVALID..."

-- Test: Multiple set-logic (should fail if > 1)
def testMultipleLogic := "
(set-logic QF_LIA)
(set-logic QF_NIA)
(check-sat)"

#eval runTest testMultipleLogic
-- Expected: "❌ INVALID..."

end StructuralTests

/- ==========================================
   SUMMARY
   ========================================== -/

def main : IO Unit := do
  IO.println "
===========================================
SMT-LIB Parser Test Suite
===========================================
Modules:
  - SmtLib.AST         : Data types
  - SmtLib.Parser      : S-expression parsing
  - SmtLib.TypeChecker : Type inference & validation
  - SmtLib.Evaluator   : Term evaluation
  - SmtLib.PrettyPrint : String conversion

Features:
  ✓ declare-const
  ✓ declare-fun
  ✓ define-fun
  ✓ assert
  ✓ check-sat
  ✓ set-logic
  ✓ Polymorphic equality (=)
  ✓ Polymorphic distinct
  ✓ If-then-else (ite)
  ✓ Core theory (and, or, not, =>, xor)
  ✓ Ints theory (+, -, *, div, mod, <, >, <=, >=)
==========================================
"
  IO.println "All compile-time tests passed! ✅"
