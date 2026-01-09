# SMT-LIB Parser for Lean 4

A type-checked parser and evaluator for SMT-LIB 2.6 scripts written in Lean 4.

## Features

- **Full parsing** of SMT-LIB S-expressions
- **Type checking** with polymorphic equality and distinct
- **Evaluation** of ground terms to Lean `Prop`
- **Pretty printing** with mathematical notation

### Supported Commands

| Command | Description |
|---------|-------------|
| `(set-logic <logic>)` | Set the logic (e.g., `QF_LIA`) |
| `(declare-const <name> <sort>)` | Declare a constant |
| `(declare-fun <name> (<sorts>) <sort>)` | Declare a function |
| `(define-fun <name> ((<params>)) <sort> <term>)` | Define a function |
| `(assert <term>)` | Assert a formula |
| `(check-sat)` | Check satisfiability |

### Supported Theories

**Core Theory:**
- Boolean: `true`, `false`, `and`, `or`, `not`, `=>`, `xor`
- Polymorphic: `=`, `distinct`, `ite`

**Ints Theory:**
- Arithmetic: `+`, `-`, `*`, `div`, `mod`
- Comparison: `<`, `>`, `<=`, `>=`

## Project Structure

```
smt-lib-parser/
├── lakefile.toml           # Build configuration
├── SmtLib.lean             # Main module (re-exports all)
├── Main.lean               # Test suite
└── SmtLib/
    ├── AST.lean            # Data types (Srt, Term, Command, etc.)
    ├── Parser.lean         # S-expression parsing
    ├── TypeChecker.lean    # Type inference & validation
    ├── Evaluator.lean      # Term evaluation to Prop
    └── PrettyPrint.lean    # ToString instances
```

## Building

```bash
# Build the library
lake build

# Run the test suite
lake exe tests
```

## Usage

### Basic Parsing

```lean
import SmtLib

open SmtLib

-- Parse a full SMT-LIB script
#eval parse "(declare-const x Int) (assert (> x 0)) (check-sat)"

-- Parse a single S-expression
#eval parseSExp "(+ 1 2)"
```

### Validation

```lean
-- Parse and type-check a script
def script := "
(declare-const x Int)
(declare-const y Int)
(assert (= x y))
(check-sat)"

#eval runScript script
-- Output: "✅ VALID (Semantically correct)"
```

### Evaluation

```lean
-- Evaluate ground boolean expressions
#eval runSafe "(assert (> 10 5))"
-- Output: "✅ TRUE"

#eval runSafe "(assert (< 10 5))"
-- Output: "❌ FALSE"
```

### Pretty Printing

```lean
#eval showCondition "(assert (=> (and (> x 0) (< x 10)) (= x 5)))"
-- Output: "(((x > 0) ∧ (x < 10)) → (x = 5))"
```

### Converting to Lean Propositions

```lean
-- Convert SMT-LIB assertions to Lean Props
#reduce specAssert (Command.assert (Term.app ">" [Term.intLit 7, Term.intLit 0]))
-- Output: some (7 > 0)

-- With custom variable environment
def myEnv : Valuation := fun name => if name == "x" then 42 else 0
#reduce specAssert (Command.assert (Term.app ">" [Term.var "x", Term.intLit 0])) myEnv
-- Output: some (42 > 0)
```

## API Reference

### High-Level Functions

| Function | Type | Description |
|----------|------|-------------|
| `parse` | `String → Option Problem` | Parse a full SMT-LIB script |
| `parseCommand` | `String → Option Command` | Parse a single command |
| `parseSExp` | `String → Except String SExp` | Parse an S-expression |
| `parseAndCheck` | `String → Option Problem` | Parse and validate |
| `runScript` | `String → String` | Validate with human-readable output |
| `runSafe` | `String → RunResult` | Parse, check, and evaluate |
| `showCondition` | `String → String` | Pretty-print an assertion |

### Core Types

```lean
inductive Srt where
  | bool | int | ident (name : String)

inductive Term where
  | var (name : String)
  | intLit (val : Int)
  | app (fn : String) (args : List Term)

inductive Command where
  | setLogic (logic : String)
  | declareConst (name : String) (sort : Srt)
  | declareFun (name : String) (args : List Srt) (ret : Srt)
  | defineFun (name : String) (params : List (String × Srt)) (ret : Srt) (body : Term)
  | assert (term : Term)
  | checkSat
```

## Examples

### Type Error Detection

```lean
-- Mixed types in equality (rejected)
def badScript := "
(declare-const x Int)
(declare-const p Bool)
(assert (= x p))
(check-sat)"

#eval runScript badScript
-- Output: "❌ INVALID (Semantic or structural error)"
```

### Using `distinct`

```lean
def distinctScript := "
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (distinct x y z))
(check-sat)"

#eval runScript distinctScript
-- Output: "✅ VALID (Semantically correct)"
```

### If-Then-Else

```lean
def iteScript := "
(declare-const x Int)
(assert (= (ite (> x 0) 1 0) 1))
(check-sat)"

#eval runScript iteScript
-- Output: "✅ VALID (Semantically correct)"
```

## License

MIT License
