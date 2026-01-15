/-
  SmtLib.lean
  ===========
  Main module that re-exports all SmtLib components
-/

import SmtLib.AST
import SmtLib.Parser
import SmtLib.TypeChecker
import SmtLib.Evaluator
import SmtLib.PrettyPrint

namespace SmtLib

/- ==========================================
   HIGH-LEVEL API
   ========================================== -/

/-- Parse and validate an SMT-LIB script -/
def parseAndCheck (s : String) : Option Problem := do
  let prob ← parse s
  if specification prob then some prob else none

/-- Result type for the safe runner -/
inductive RunResult where
  | syntaxError   : String → RunResult
  | semanticError : String → RunResult
  | evalError     : String → RunResult
  | success       : Bool → RunResult
  deriving Repr

instance : ToString RunResult where
  toString
    | .syntaxError msg   => s!"💥 Syntax Error: {msg}"
    | .semanticError msg => s!"⛔ Semantic Error: {msg}"
    | .evalError msg     => s!"❓ Evaluation Error: {msg}"
    | .success true      => "✅ TRUE"
    | .success false     => "❌ FALSE"

/-- Run a single assert command through the full pipeline -/
def runSafe (input : String) : RunResult :=
  match parseCommand input with
  | none => .syntaxError "Failed to parse command"
  | some cmd =>
      match checkCommand initialContext cmd with
      | none => .semanticError "Type check failed"
      | some _ =>
          match evalAssert cmd with
          | some b => .success b
          | none   => .evalError "Could not evaluate (variables or non-boolean)"

/-- Run a full script and return validation result -/
def runScript (input : String) : String :=
  match parse input with
  | none => "💥 PARSE ERROR (Invalid syntax)"
  | some prob =>
      if specification prob then
        "✅ VALID (Semantically correct)"
      else
        "❌ INVALID (Semantic or structural error)"

/-- Extract and display the condition from an assert command -/
def showCondition (input : String) : String :=
  match parseCommand input with
  | none => "Parse Error"
  | some cmd =>
      match cmd with
      | Command.assert t => t.toString
      | _ => "Not an assert command"

end SmtLib
