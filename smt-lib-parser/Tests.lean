/-
  Tests.lean
  ==========
  Comprehensive test suite for SMT-LIB Parser in Lean 4
  Tests cover: Parser, TypeChecker, Evaluator, and PrettyPrint
-/

import SmtLib.AST
import SmtLib.Parser
import SmtLib.Evaluator
import SmtLib.PrettyPrint
import SmtLib.TypeChecker

namespace SmtLibTests

open SmtLib

/- ==========================================
   TEST HELPERS
   ========================================== -/

-- Helper to run tests and report results
def runTest (name : String) (test : Bool) : String :=
  if test then s!"✓ {name}" else s!"✗ {name}"

/- ==========================================
   TESTS: AST CONSTRUCTION
   ========================================== -/

section ASTTests

def test_srt_equality : Bool :=
  Srt.int == Srt.int ∧ Srt.bool == Srt.bool

def test_srt_inequality : Bool :=
  Srt.int ≠ Srt.bool

def test_op_toString : Bool :=
  Op.plus.toString == "+" ∧
  Op.eq.toString == "=" ∧
  Op.and.toString == "and"

def test_term_construction : Bool :=
  let t1 : Term := Term.intLit 42
  let t2 : Term := Term.var "x"
  let t3 : Term := Term.stringLit "hello"
  match (t1, t2, t3) with
  | (Term.intLit 42, Term.var "x", Term.stringLit "hello") => true
  | _ => false

def test_command_construction : Bool :=
  let c1 : Command := Command.setLogic "QF_LIA"
  let c2 : Command := Command.checkSat
  match (c1, c2) with
  | (Command.setLogic "QF_LIA", Command.checkSat) => true
  | _ => false

end ASTTests

/- ==========================================
   TESTS: PARSER - Basic Expressions
   ========================================== -/

section ParserBasicTests

-- Test parsing integers
def test_parse_positive_int : Bool :=
  match Parser.parseE "(assert 42)" with
  | .ok _ => true
  | .error _ => false

def test_parse_negative_int : Bool :=
  match Parser.parseE "(assert (- 5))" with
  | .ok _ => true
  | .error _ => false

-- Test parsing variables
def test_parse_variable : Bool :=
  match Parser.parseE "(assert x)" with
  | .ok _ => true
  | .error _ => false

-- Test parsing arithmetic expressions
def test_parse_addition : Bool :=
  match Parser.parseE "(assert (+ 1 2))" with
  | .ok problem =>
      match problem.commands with
      | [Command.assert (Term.app Op.plus args)] => args.length == 2
      | _ => false
  | .error _ => false

def test_parse_complex_arithmetic : Bool :=
  match Parser.parseE "(assert (* (+ 1 2) (- 5 3)))" with
  | .ok problem =>
      match problem.commands with
      | [Command.assert (Term.app Op.mul args)] => args.length == 2
      | _ => false
  | .error _ => false

-- Test parsing comparison operators
def test_parse_equality : Bool :=
  match Parser.parseE "(assert (= x 5))" with
  | .ok problem =>
      match problem.commands with
      | [Command.assert (Term.app Op.eq args)] => args.length == 2
      | _ => false
  | .error _ => false

def test_parse_less_than : Bool :=
  match Parser.parseE "(assert (< 3 10))" with
  | .ok problem =>
      match problem.commands with
      | [Command.assert (Term.app Op.lt args)] => args.length == 2
      | _ => false
  | .error _ => false

end ParserBasicTests

/- ==========================================
   TESTS: PARSER - Commands
   ========================================== -/

section ParserCommandTests

-- Test set-logic
def test_parse_set_logic : Bool :=
  match Parser.parseE "(set-logic QF_LIA)" with
  | .ok problem =>
      match problem.commands with
      | [Command.setLogic "QF_LIA"] => true
      | _ => false
  | .error _ => false

-- Test declare-const
def test_parse_declare_const : Bool :=
  match Parser.parseE "(declare-const x Int)" with
  | .ok problem =>
      match problem.commands with
      | [Command.declareConst "x" Srt.int] => true
      | _ => false
  | .error _ => false

-- Test declare-fun
def test_parse_declare_fun : Bool :=
  match Parser.parseE "(declare-fun f (Int Int) Bool)" with
  | .ok problem =>
      match problem.commands with
      | [Command.declareFun "f" [Srt.int, Srt.int] Srt.bool] => true
      | _ => false
  | .error _ => false

-- Test check-sat
def test_parse_check_sat : Bool :=
  match Parser.parseE "(check-sat)" with
  | .ok problem =>
      match problem.commands with
      | [Command.checkSat] => true
      | _ => false
  | .error _ => false

-- Test multi-command script
def test_parse_multi_command : Bool :=
  match Parser.parseE "(set-logic QF_LIA) (declare-const x Int) (check-sat)" with
  | .ok problem => problem.commands.length == 3
  | .error _ => false

end ParserCommandTests

/- ==========================================
   TESTS: TYPE CHECKER
   ========================================== -/

section TypeCheckerTests

-- Test inferring int literal type
def test_infer_int_type : Bool :=
  let t : Term := Term.intLit 42
  match inferSort initialContext t with
  | some Srt.int => true
  | _ => false

-- Test inferring string literal type
def test_infer_string_type : Bool :=
  let t : Term := Term.stringLit "hello"
  match inferSort initialContext t with
  | some Srt.string => true
  | _ => false

-- Test polymorphic equality
def test_infer_equality_int : Bool :=
  let t : Term := Term.app Op.eq [Term.intLit 1, Term.intLit 2]
  match inferSort initialContext t with
  | some Srt.bool => true
  | _ => false

def test_infer_equality_string : Bool :=
  let t : Term := Term.app Op.eq [Term.stringLit "a", Term.stringLit "b"]
  match inferSort initialContext t with
  | some Srt.bool => true
  | _ => false

-- Test arithmetic operations
def test_infer_addition : Bool :=
  let t : Term := Term.app Op.plus [Term.intLit 1, Term.intLit 2]
  match inferSort initialContext t with
  | some Srt.int => true
  | _ => false

-- Test comparisons return bool
def test_infer_less_than : Bool :=
  let t : Term := Term.app Op.lt [Term.intLit 5, Term.intLit 10]
  match inferSort initialContext t with
  | some Srt.bool => true
  | _ => false

-- Test logical operators
def test_infer_and : Bool :=
  let t1 : Term := Term.app Op.eq [Term.intLit 1, Term.intLit 1]
  let t2 : Term := Term.app Op.eq [Term.intLit 2, Term.intLit 2]
  let t : Term := Term.app Op.and [t1, t2]
  match inferSort initialContext t with
  | some Srt.bool => true
  | _ => false

-- Test if-then-else
def test_infer_ite : Bool :=
  let cond : Term := Term.app Op.eq [Term.intLit 1, Term.intLit 1]
  let t : Term := Term.app Op.ite [cond, Term.intLit 10, Term.intLit 20]
  match inferSort initialContext t with
  | some Srt.int => true
  | _ => false

-- Test type mismatch in equality (should fail)
def test_infer_type_mismatch : Bool :=
  let t : Term := Term.app Op.eq [Term.intLit 1, Term.stringLit "hello"]
  match inferSort initialContext t with
  | some _ => false  -- Should fail to infer
  | none => true

-- Test command validation
def test_check_command_assert : Bool :=
  let t : Term := Term.app Op.eq [Term.intLit 1, Term.intLit 1]
  let cmd : Command := Command.assert t
  match checkCommand initialContext cmd with
  | some _ => true
  | none => false

def test_check_command_declare_const : Bool :=
  let cmd : Command := Command.declareConst "x" Srt.int
  match checkCommand initialContext cmd with
  | some _ => true
  | none => false

end TypeCheckerTests

/- ==========================================
   TESTS: EVALUATOR - Arithmetic
   ========================================== -/

section EvaluatorArithmeticTests

-- Test addition
def test_eval_addition : Bool :=
  let t : Term := Term.app Op.plus [Term.intLit 5, Term.intLit 3]
  match termToInt t with
  | some 8 => true
  | _ => false

-- Test subtraction
def test_eval_subtraction : Bool :=
  let t : Term := Term.app Op.minus [Term.intLit 10, Term.intLit 4]
  match termToInt t with
  | some 6 => true
  | _ => false

-- Test multiplication
def test_eval_multiplication : Bool :=
  let t : Term := Term.app Op.mul [Term.intLit 6, Term.intLit 7]
  match termToInt t with
  | some 42 => true
  | _ => false

-- Test division
def test_eval_division : Bool :=
  let t : Term := Term.app Op.div [Term.intLit 20, Term.intLit 4]
  match termToInt t with
  | some 5 => true
  | _ => false

-- Test modulo
def test_eval_modulo : Bool :=
  let t : Term := Term.app Op.mod [Term.intLit 17, Term.intLit 5]
  match termToInt t with
  | some 2 => true
  | _ => false

-- Test nested arithmetic
def test_eval_nested : Bool :=
  let inner : Term := Term.app Op.plus [Term.intLit 2, Term.intLit 3]
  let outer : Term := Term.app Op.mul [inner, Term.intLit 4]
  match termToInt outer with
  | some 20 => true
  | _ => false

-- Test negation (unary minus)
def test_eval_negation : Bool :=
  let t : Term := Term.app Op.minus [Term.intLit 5]
  match termToInt t with
  | some (-5) => true
  | _ => false

end EvaluatorArithmeticTests

/- ==========================================
   TESTS: EVALUATOR - Comparisons
   ========================================== -/

section EvaluatorComparisonTests

-- Test equality true
def test_eval_eq_true : Bool :=
  let t : Term := Term.app Op.eq [Term.intLit 5, Term.intLit 5]
  match termToProp t with
  | some True => true
  | _ => false

-- Test equality false
def test_eval_eq_false : Bool :=
  let t : Term := Term.app Op.eq [Term.intLit 5, Term.intLit 3]
  match termToProp t with
  | some False => true
  | _ => false

-- Test less than true
def test_eval_lt_true : Bool :=
  let t : Term := Term.app Op.lt [Term.intLit 3, Term.intLit 10]
  match termToProp t with
  | some True => true
  | _ => false

-- Test less than false
def test_eval_lt_false : Bool :=
  let t : Term := Term.app Op.lt [Term.intLit 10, Term.intLit 3]
  match termToProp t with
  | some False => true
  | _ => false

-- Test greater than
def test_eval_gt : Bool :=
  let t : Term := Term.app Op.gt [Term.intLit 10, Term.intLit 5]
  match termToProp t with
  | some True => true
  | _ => false

-- Test less or equal
def test_eval_le : Bool :=
  let t : Term := Term.app Op.le [Term.intLit 5, Term.intLit 5]
  match termToProp t with
  | some True => true
  | _ => false

-- Test greater or equal
def test_eval_ge : Bool :=
  let t : Term := Term.app Op.ge [Term.intLit 10, Term.intLit 5]
  match termToProp t with
  | some True => true
  | _ => false

end EvaluatorComparisonTests

/- ==========================================
   TESTS: EVALUATOR - Logical Operations
   ========================================== -/

section EvaluatorLogicalTests

-- Test AND operation
def test_eval_and_true : Bool :=
  let t1 : Term := Term.app Op.eq [Term.intLit 1, Term.intLit 1]
  let t2 : Term := Term.app Op.eq [Term.intLit 2, Term.intLit 2]
  let t : Term := Term.app Op.and [t1, t2]
  match termToProp t with
  | some True => true
  | _ => false

def test_eval_and_false : Bool :=
  let t1 : Term := Term.app Op.eq [Term.intLit 1, Term.intLit 2]
  let t2 : Term := Term.app Op.eq [Term.intLit 2, Term.intLit 2]
  let t : Term := Term.app Op.and [t1, t2]
  match termToProp t with
  | some False => true
  | _ => false

-- Test OR operation
def test_eval_or_true : Bool :=
  let t1 : Term := Term.app Op.eq [Term.intLit 1, Term.intLit 2]
  let t2 : Term := Term.app Op.eq [Term.intLit 2, Term.intLit 2]
  let t : Term := Term.app Op.or [t1, t2]
  match termToProp t with
  | some True => true
  | _ => false

-- Test NOT operation
def test_eval_not : Bool :=
  let inner : Term := Term.app Op.eq [Term.intLit 1, Term.intLit 2]
  let t : Term := Term.app Op.not [inner]
  match termToProp t with
  | some True => true
  | _ => false

-- Test implication
def test_eval_implies : Bool :=
  let t1 : Term := Term.app Op.eq [Term.intLit 1, Term.intLit 1]
  let t2 : Term := Term.app Op.eq [Term.intLit 2, Term.intLit 2]
  let t : Term := Term.app Op.imp [t1, t2]
  match termToProp t with
  | some True => true
  | _ => false

end EvaluatorLogicalTests

/- ==========================================
   TESTS: PRETTY PRINT
   ========================================== -/

section PrettyPrintTests

-- Test integer formatting
def test_pp_int : Bool :=
  (Term.intLit 42).toString == "42"

-- Test variable formatting
def test_pp_var : Bool :=
  (Term.var "x").toString == "x"

-- Test arithmetic expression
def test_pp_arithmetic : Bool :=
  let t : Term := Term.app Op.plus [Term.intLit 1, Term.intLit 2]
  t.toString == "(1 + 2)"

-- Test logical operators with symbols
def test_pp_and : Bool :=
  let t1 : Term := Term.var "p"
  let t2 : Term := Term.var "q"
  let t : Term := Term.app Op.and [t1, t2]
  t.toString.contains "∧"

def test_pp_or : Bool :=
  let t1 : Term := Term.var "p"
  let t2 : Term := Term.var "q"
  let t : Term := Term.app Op.or [t1, t2]
  t.toString.contains "∨"

-- Test command formatting
def test_pp_command_assert : Bool :=
  let t : Term := Term.app Op.eq [Term.intLit 1, Term.intLit 1]
  let c : Command := Command.assert t
  c.toString.contains "assert"

def test_pp_command_declare : Bool :=
  let c : Command := Command.declareConst "x" Srt.int
  c.toString.contains "declare-const" ∧ c.toString.contains "x"

end PrettyPrintTests

/- ==========================================
   INTEGRATION TESTS
   ========================================== -/

section IntegrationTests

-- Test complete parsing + type checking
def test_integration_parse_and_check : Bool :=
  match Parser.parseE "(assert (> x 5))" with
  | .ok problem =>
      checkScript problem.commands
  | .error _ => false

-- Test parsing and pretty printing round-trip
def test_integration_roundtrip : Bool :=
  let cmd_str := "(declare-const x Int)"
  match Parser.parseCommandE cmd_str with
  | .ok cmd =>
      let pp := cmd.toString
      pp.contains "declare-const" ∧ pp.contains "x"
  | .error _ => false

-- Test full SMT-LIB script
def test_integration_full_script : Bool :=
  let script := "
    (set-logic QF_LIA)
    (declare-const x Int)
    (declare-const y Int)
    (assert (> x 0))
    (assert (> y 0))
    (assert (= (+ x y) 10))
    (check-sat)
  "
  match Parser.parseE script with
  | .ok problem =>
      problem.commands.length == 7 ∧ checkScript problem.commands
  | .error _ => false

end IntegrationTests

/- ==========================================
   END-TO-END PIPELINE TESTS
   ========================================== -/

section PipelineTests

/- 
  Pipeline: String SMT-LIB → Parser → TypeChecker → PrettyPrint
  Shows complete transformation with real examples
-/

-- Example 1: Simple arithmetic assertion
def test_pipeline_simple_arithmetic : Bool :=
  let input := "(assert (+ 1 2))"
  match Parser.parseE input with
  | .ok problem =>
      match problem.commands with
      | [Command.assert t] =>
          -- Check that it types correctly
          match inferSort initialContext t with
          | some Srt.int =>
              -- Check that it evaluates
              match termToInt t with
              | some 3 => true
              | _ => false
          | _ => false
      | _ => false
  | .error _ => false

-- Example 2: Equality check with type validation
def test_pipeline_equality : Bool :=
  let input := "(assert (= 5 5))"
  match Parser.parseE input with
  | .ok problem =>
      match problem.commands with
      | [Command.assert t] =>
          -- Type check
          match inferSort initialContext t with
          | some Srt.bool =>
              -- Evaluate
              match termToProp t with
              | some True => true
              | _ => false
          | _ => false
      | _ => false
  | .error _ => false

-- Example 3: Complex logical formula
def test_pipeline_complex_formula : Bool :=
  let input := "(assert (and (> 10 5) (< 3 8)))"
  match Parser.parseE input with
  | .ok problem =>
      match problem.commands with
      | [Command.assert t] =>
          -- Type check should succeed
          match inferSort initialContext t with
          | some Srt.bool =>
              -- Evaluate logical formula
              match termToProp t with
              | some True => true
              | _ => false
          | _ => false
      | _ => false
  | .error _ => false

-- Example 4: If-then-else with multiple checks
def test_pipeline_ite : Bool :=
  let input := "(assert (ite (= 1 1) 100 200))"
  match Parser.parseE input with
  | .ok problem =>
      match problem.commands with
      | [Command.assert t] =>
          -- Type check
          match inferSort initialContext t with
          | some Srt.int =>
              -- Evaluate
              match termToInt t with
              | some 100 => true
              | _ => false
          | _ => false
      | _ => false
  | .error _ => false

-- Example 5: Declare const + assert + pretty print
def test_pipeline_declare_and_assert : Bool :=
  let input := "(declare-const x Int)\n(assert (> x 0))"
  match Parser.parseE input with
  | .ok problem =>
      problem.commands.length == 2 ∧
      checkScript problem.commands ∧
      let pp := problem.toString
      pp.contains "declare-const" ∧ pp.contains "assert"
  | .error _ => false

-- Example 6: Nested arithmetic with parse + eval
def test_pipeline_nested_arithmetic : Bool :=
  let input := "(assert (* (+ 2 3) (- 10 5)))"
  match Parser.parseE input with
  | .ok problem =>
      match problem.commands with
      | [Command.assert t] =>
          match inferSort initialContext t with
          | some Srt.int =>
              -- (+ 2 3) = 5, (- 10 5) = 5, (* 5 5) = 25
              match termToInt t with
              | some 25 => true
              | _ => false
          | _ => false
      | _ => false
  | .error _ => false

-- Example 7: Full SMT-LIB script with multiple operations
def test_pipeline_full_smt_script : Bool :=
  let script := "
    (set-logic QF_LIA)
    (declare-const a Int)
    (declare-const b Int)
    (assert (> a 0))
    (assert (> b 0))
    (assert (= (+ a b) 10))
    (check-sat)
  "
  match Parser.parseE script with
  | .ok problem =>
      -- Should have 7 commands
      problem.commands.length == 7 ∧
      -- All should type check
      checkScript problem.commands ∧
      -- Pretty print should work
      problem.toString.contains "set-logic" ∧
      problem.toString.contains "declare-const" ∧
      problem.toString.contains "assert" ∧
      problem.toString.contains "check-sat"
  | .error _ => false

-- Example 8: Parse → Type Check → Evaluate chain
def test_pipeline_chain_evaluation : Bool :=
  let input := "(assert (and (= 5 5) (< 3 10) (> 20 15)))"
  match Parser.parseE input with
  | .ok problem =>
      match problem.commands with
      | [Command.assert t] =>
          -- Must type check
          match inferSort initialContext t with
          | some Srt.bool =>
              -- Must evaluate to True (all three conditions are true)
              match termToProp t with
              | some True => true
              | _ => false
          | _ => false
      | _ => false
  | .error _ => false

-- Example 9: Negation of false should be true
def test_pipeline_negation : Bool :=
  let input := "(assert (not (= 1 2)))"
  match Parser.parseE input with
  | .ok problem =>
      match problem.commands with
      | [Command.assert t] =>
          match inferSort initialContext t with
          | some Srt.bool =>
              match termToProp t with
              | some True => true
              | _ => false
          | _ => false
      | _ => false
  | .error _ => false

-- Example 10: Implication chain
def test_pipeline_implication : Bool :=
  let input := "(assert (=> (= 1 1) (= 2 2)))"
  match Parser.parseE input with
  | .ok problem =>
      match problem.commands with
      | [Command.assert t] =>
          match inferSort initialContext t with
          | some Srt.bool =>
              -- Both sides are true, so implication is true
              match termToProp t with
              | some True => true
              | _ => false
          | _ => false
      | _ => false
  | .error _ => false

end PipelineTests

/- ==========================================
   SMT-LIB LOGIC SPECIFIC TESTS
   ========================================== -/

section SMTLibLogicTests

/- QF_LIA: Quantifier-Free Linear Integer Arithmetic -/

def test_qflia_basic : Bool :=
  let script := "
    (set-logic QF_LIA)
    (declare-const x Int)
    (declare-const y Int)
    (assert (> x 0))
    (assert (> y 0))
    (assert (= (+ x y) 10))
    (check-sat)
  "
  match Parser.parseE script with
  | .ok problem =>
      checkScript problem.commands ∧
      problem.commands.length == 6
  | .error _ => false

def test_qflia_modulo : Bool :=
  let script := "
    (set-logic QF_LIA)
    (declare-const n Int)
    (assert (= (mod n 3) 0))
    (check-sat)
  "
  match Parser.parseE script with
  | .ok problem => checkScript problem.commands
  | .error _ => false

def test_qflia_division : Bool :=
  let input := "(assert (= (div 20 4) 5))"
  match Parser.parseE input with
  | .ok problem =>
      match problem.commands with
      | [Command.assert t] =>
          match termToInt t with
          | some 1 => true  -- = returns true/1
          | _ => false
      | _ => false
  | .error _ => false

/- QF_BV: Quantifier-Free Bitvectors -/

def test_qfbv_logic : Bool :=
  let script := "
    (set-logic QF_BV)
    (declare-const a Bool)
    (declare-const b Bool)
    (assert (or a b))
    (assert (not (and a b)))
    (check-sat)
  "
  match Parser.parseE script with
  | .ok problem => checkScript problem.commands
  | .error _ => false

/- QF_S: Quantifier-Free Strings -/

def test_qfs_strings : Bool :=
  let script := "
    (set-logic QF_S)
    (declare-const s String)
    (assert (= s \"hello\"))
    (check-sat)
  "
  match Parser.parseE script with
  | .ok problem => checkScript problem.commands
  | .error _ => false

end SMTLibLogicTests

/- ==========================================
   SMT-LIB COMMAND SEQUENCE TESTS
   ========================================== -/

section SMTLibCommandTests

-- Test declare-fun with multiple arguments
def test_declare_fun_multi_arg : Bool :=
  let script := "
    (set-logic QF_LIA)
    (declare-fun f (Int Int) Int)
    (declare-const x Int)
    (declare-const y Int)
    (assert (= (f x y) (+ x y)))
    (check-sat)
  "
  match Parser.parseE script with
  | .ok problem =>
      checkScript problem.commands ∧
      match problem.commands with
      | Command.setLogic _ :: Command.declareFun _ args res :: _ =>
          args.length == 2 ∧ res == Srt.int
      | _ => false
  | .error _ => false

-- Test define-fun (function definition)
def test_define_fun : Bool :=
  let script := "
    (set-logic QF_LIA)
    (define-fun abs ((x Int)) Int
      (ite (> x 0) x (- x)))
    (check-sat)
  "
  match Parser.parseE script with
  | .ok problem =>
      match problem.commands with
      | [Command.defineFun "abs" args res _] =>
          args.length == 1 ∧ res == Srt.int
      | _ => false
  | .error _ => false

-- Test get-value command
def test_get_value : Bool :=
  let script := "
    (set-logic QF_LIA)
    (declare-const x Int)
    (assert (= x 5))
    (get-value (x))
  "
  match Parser.parseE script with
  | .ok problem =>
      match problem.commands with
      | _ :: _ :: _ :: Command.getValue terms :: _ =>
          terms.length == 1
      | _ => false
  | .error _ => false

-- Test exit command
def test_exit_command : Bool :=
  let script := "
    (check-sat)
    (exit)
  "
  match Parser.parseE script with
  | .ok problem =>
      match problem.commands with
      | [Command.checkSat, Command.exit] => true
      | _ => false
  | .error _ => false

end SMTLibCommandTests

/- ==========================================
   SMT-LIB CONSTRAINT PATTERNS
   ========================================== -/

section SMTLibConstraintPatterns

-- Pattern: Simple bounds
def test_pattern_bounds : Bool :=
  let script := "
    (set-logic QF_LIA)
    (declare-const x Int)
    (assert (>= x 0))
    (assert (<= x 100))
    (check-sat)
  "
  match Parser.parseE script with
  | .ok problem =>
      problem.commands.length == 4 ∧ checkScript problem.commands
  | .error _ => false

-- Pattern: Difference constraint (x - y <= c)
def test_pattern_diff_constraint : Bool :=
  let script := "
    (set-logic QF_LIA)
    (declare-const x Int)
    (declare-const y Int)
    (assert (<= (- x y) 10))
    (check-sat)
  "
  match Parser.parseE script with
  | .ok problem => checkScript problem.commands
  | .error _ => false

-- Pattern: Boolean combination
def test_pattern_boolean_combo : Bool :=
  let script := "
    (set-logic QF_LIA)
    (declare-const x Int)
    (assert (or (= x 1) (= x 2) (= x 3)))
    (check-sat)
  "
  match Parser.parseE script with
  | .ok problem =>
      match problem.commands with
      | [Command.setLogic _, Command.declareConst _, Command.assert _] => true
      | _ => false
  | .error _ => false

-- Pattern: Implication chain
def test_pattern_implication : Bool :=
  let script := "
    (set-logic QF_LIA)
    (declare-const a Int)
    (declare-const b Int)
    (assert (=> (> a 10) (> b 20)))
    (check-sat)
  "
  match Parser.parseE script with
  | .ok problem => checkScript problem.commands
  | .error _ => false

-- Pattern: Negated constraint
def test_pattern_negation : Bool :=
  let script := "
    (set-logic QF_LIA)
    (declare-const x Int)
    (assert (not (= x 0)))
    (check-sat)
  "
  match Parser.parseE script with
  | .ok problem => checkScript problem.commands
  | .error _ => false

-- Pattern: Distinct values
def test_pattern_distinct : Bool :=
  let script := "
    (set-logic QF_LIA)
    (declare-const a Int)
    (declare-const b Int)
    (declare-const c Int)
    (assert (distinct a b c))
    (check-sat)
  "
  match Parser.parseE script with
  | .ok problem =>
      match problem.commands with
      | [_, _, _, _, Command.assert (Term.app Op.distinct args)] =>
          args.length == 3
      | _ => false
  | .error _ => false

end SMTLibConstraintPatterns

/- ==========================================
   SATISFIABILITY PROBLEM EXAMPLES
   ========================================== -/

section SATExamples

-- 3-SAT Problem
def test_sat_problem_3sat : Bool :=
  let script := "
    (set-logic QF_BV)
    (declare-const p Bool)
    (declare-const q Bool)
    (declare-const r Bool)
    (assert (or p q r))
    (assert (or (not p) (not q)))
    (assert (or (not q) (not r)))
    (check-sat)
  "
  match Parser.parseE script with
  | .ok problem =>
      checkScript problem.commands ∧
      problem.commands.length == 7
  | .error _ => false

-- SMT Problem: Arithmetic + Logic
def test_smt_problem_mixed : Bool :=
  let script := "
    (set-logic QF_LIA)
    (declare-const x Int)
    (declare-const y Int)
    (declare-const z Int)
    (assert (= (+ x y z) 100))
    (assert (> x 0))
    (assert (> y 0))
    (assert (> z 0))
    (check-sat)
  "
  match Parser.parseE script with
  | .ok problem =>
      checkScript problem.commands ∧
      problem.commands.length == 8
  | .error _ => false

-- Sudoku-like constraint
def test_smt_sudoku_constraint : Bool :=
  let script := "
    (set-logic QF_LIA)
    (declare-const a Int)
    (declare-const b Int)
    (declare-const c Int)
    (assert (and (>= a 1) (<= a 9)))
    (assert (and (>= b 1) (<= b 9)))
    (assert (and (>= c 1) (<= c 9)))
    (assert (distinct a b c))
    (check-sat)
  "
  match Parser.parseE script with
  | .ok problem => checkScript problem.commands
  | .error _ => false

end SATExamples

/- ==========================================
   ERROR HANDLING & EDGE CASES
   ========================================== -/

section ErrorHandlingTests

-- Test malformed command (should parse but not type-check)
def test_error_type_mismatch : Bool :=
  let script := "
    (set-logic QF_LIA)
    (assert (= 5 \"string\"))
  "
  match Parser.parseE script with
  | .ok problem =>
      -- Parses successfully but type-checking should fail
      ¬(checkScript problem.commands)
  | .error _ => false  -- Parse error is also acceptable

-- Test missing arguments
def test_error_missing_args : Bool :=
  let input := "(+ 1)"
  match Parser.parseE input with
  | .ok problem =>
      -- Can parse, but type checking should fail (+ needs 2 args)
      ¬(checkScript problem.commands)
  | .error _ => true  -- Parser error is okay

end ErrorHandlingTests

/- ==========================================
   TEST EXECUTION SUMMARY
   ========================================== -/

#eval IO.println "\n=== SMT-LIB Parser Test Suite ==="
#eval IO.println "\n[PIPELINE TESTS]"
#eval IO.println (runTest "Simple arithmetic" test_pipeline_simple_arithmetic)
#eval IO.println (runTest "Equality check" test_pipeline_equality)
#eval IO.println (runTest "Complex formula" test_pipeline_complex_formula)
#eval IO.println (runTest "If-then-else" test_pipeline_ite)
#eval IO.println (runTest "Declare + Assert" test_pipeline_declare_and_assert)
#eval IO.println (runTest "Nested arithmetic" test_pipeline_nested_arithmetic)
#eval IO.println (runTest "Full SMT script" test_pipeline_full_smt_script)
#eval IO.println (runTest "Chain evaluation" test_pipeline_chain_evaluation)
#eval IO.println (runTest "Negation" test_pipeline_negation)
#eval IO.println (runTest "Implication" test_pipeline_implication)

#eval IO.println "\n[REAL-WORLD EXAMPLES]"
#eval IO.println (runTest "Linear arithmetic" test_example_linear_arithmetic)
#eval IO.println (runTest "Boolean SAT" test_example_boolean_sat)
#eval IO.println (runTest "Mixed constraints" test_example_mixed_constraints)
#eval IO.println (runTest "Nested ITE" test_example_ite_nested)

#eval IO.println "\n=== All Tests Complete ==="

/- ==========================================
   TESTS: OPERATIONS
   ========================================== -/

section OperationTests

-- Test: 1 + 2 = 3
def test_addition : Bool :=
  let t : Term := Term.app Op.plus [Term.intLit 1, Term.intLit 2]
  match evalTerm t with
  | Term.intLit 3 => true
  | _ => false

-- Test: 5 - 3 = 2
def test_subtraction : Bool :=
  let t : Term := Term.app Op.minus [Term.intLit 5, Term.intLit 3]
  match evalTerm t with
  | Term.intLit 2 => true
  | _ => false

-- Test: 4 * 3 = 12
def test_multiplication : Bool :=
  let t : Term := Term.app Op.mul [Term.intLit 4, Term.intLit 3]
  match evalTerm t with
  | Term.intLit 12 => true
  | _ => false

-- Test: 10 / 2 = 5
def test_division : Bool :=
  let t : Term := Term.app Op.div [Term.intLit 10, Term.intLit 2]
  match evalTerm t with
  | Term.intLit 5 => true
  | _ => false

-- Test: 1 = 1 is true
def test_equality_true : Bool :=
  let t : Term := Term.app Op.eq [Term.intLit 1, Term.intLit 1]
  match evalTerm t with
  | Term.intLit 1 => true  -- 1 for true
  | _ => false

-- Test: 1 = 2 is false
def test_equality_false : Bool :=
  let t : Term := Term.app Op.eq [Term.intLit 1, Term.intLit 2]
  match evalTerm t with
  | Term.intLit 0 => true  -- 0 for false
  | _ => false

-- Test: 5 < 10 is true
def test_less_than_true : Bool :=
  let t : Term := Term.app Op.lt [Term.intLit 5, Term.intLit 10]
  match evalTerm t with
  | Term.intLit 1 => true
  | _ => false

-- Test: 10 < 5 is false
def test_less_than_false : Bool :=
  let t : Term := Term.app Op.lt [Term.intLit 10, Term.intLit 5]
  match evalTerm t with
  | Term.intLit 0 => true
  | _ => false

-- Test: 5 >= 5 is true
def test_greater_equal_true : Bool :=
  let t : Term := Term.app Op.ge [Term.intLit 5, Term.intLit 5]
  match evalTerm t with
  | Term.intLit 1 => true
  | _ => false

-- Test: ite(1, 10, 20) = 10
def test_ite_true : Bool :=
  let cond : Term := Term.intLit 1  -- true
  let then_val : Term := Term.intLit 10
  let else_val : Term := Term.intLit 20
  let t : Term := Term.app Op.ite [cond, then_val, else_val]
  match evalTerm t with
  | Term.intLit 10 => true
  | _ => false

-- Test: ite(0, 10, 20) = 20
def test_ite_false : Bool :=
  let cond : Term := Term.intLit 0  -- false
  let then_val : Term := Term.intLit 10
  let else_val : Term := Term.intLit 20
  let t : Term := Term.app Op.ite [cond, then_val, else_val]
  match evalTerm t with
  | Term.intLit 20 => true
  | _ => false

#eval test_addition           -- Expected: true
#eval test_subtraction        -- Expected: true
#eval test_multiplication     -- Expected: true
#eval test_division           -- Expected: true
#eval test_equality_true      -- Expected: true
#eval test_equality_false     -- Expected: true
#eval test_less_than_true     -- Expected: true
#eval test_less_than_false    -- Expected: true
#eval test_greater_equal_true -- Expected: true
#eval test_ite_true           -- Expected: true
#eval test_ite_false          -- Expected: true

end OperationTests

/- ==========================================
   TESTS: PRETTY PRINT
   ========================================== -/

section PrettyPrintTests

def test_pp_intlit : Bool :=
  let t : Term := Term.intLit 42
  ppTerm t == "42"

def test_pp_var : Bool :=
  let t : Term := Term.var "x"
  ppTerm t == "x"

def test_pp_addition : Bool :=
  let t : Term := Term.app Op.plus [Term.intLit 1, Term.intLit 2]
  ppTerm t == "(+ 1 2)"

def test_pp_nested : Bool :=
  let inner : Term := Term.app Op.plus [Term.intLit 1, Term.intLit 2]
  let outer : Term := Term.app Op.mul [inner, Term.intLit 3]
  ppTerm outer == "(* (+ 1 2) 3)"

#eval test_pp_intlit     -- Expected: true
#eval test_pp_var        -- Expected: true
#eval test_pp_addition   -- Expected: true
#eval test_pp_nested     -- Expected: true

end PrettyPrintTests

/- ==========================================
   TESTS: TYPE CHECKER
   ========================================== -/

section TypeCheckerTests

def test_typecheck_intlit : Bool :=
  let t : Term := Term.intLit 42
  match typeOf t with
  | some Srt.int => true
  | _ => false

def test_typecheck_var : Bool :=
  let t : Term := Term.var "x"
  -- Variables without context should fail type-checking or return unknown
  match typeOf t with
  | some (Srt.ident _) => true  -- Variables have identifier type
  | _ => false

def test_typecheck_equality : Bool :=
  let t : Term := Term.app Op.eq [Term.intLit 1, Term.intLit 2]
  match typeOf t with
  | some Srt.bool => true
  | _ => false

#eval test_typecheck_intlit    -- Expected: true
#eval test_typecheck_var       -- Expected: true
#eval test_typecheck_equality  -- Expected: true

end TypeCheckerTests

/- ==========================================
   TESTS: PARSER (Basic)
   ========================================== -/

section ParserTests

-- Test: Parse "42"
def test_parse_int : Bool :=
  match SmtLib.Parser.parseExpr "42" with
  | .ok (Term.intLit 42) => true
  | _ => false

-- Test: Parse "x"
def test_parse_var : Bool :=
  match SmtLib.Parser.parseExpr "x" with
  | .ok (Term.var "x") => true
  | _ => false

-- Test: Parse "(+ 1 2)"
def test_parse_addition : Bool :=
  match SmtLib.Parser.parseExpr "(+ 1 2)" with
  | .ok (Term.app Op.plus args) => args.length == 2
  | _ => false

-- Test: Parse complex expression "(* (+ 1 2) 3)"
def test_parse_nested : Bool :=
  match SmtLib.Parser.parseExpr "(* (+ 1 2) 3)" with
  | .ok (Term.app Op.mul args) => args.length == 2
  | _ => false

#eval test_parse_int       -- Expected: true
#eval test_parse_var       -- Expected: true
#eval test_parse_addition  -- Expected: true
#eval test_parse_nested    -- Expected: true

end ParserTests

/- ==========================================
   TEST SUMMARY
   ========================================== -/

#eval IO.println "SMT-LIB Parser Tests Completed!"

end SmtLibTests
