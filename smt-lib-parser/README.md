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
| `(get-model)` | Request the current model |
| `(get-value (<terms>))` | Evaluate specific terms in the current model |

### Supported Theories

**Core Theory:**
- Boolean: `true`, `false`, `and`, `or`, `not`, `=>`, `xor`
- Polymorphic: `=`, `distinct`, `ite`

**Ints Theory:**
- Arithmetic: `+`, `-`, `*`, `div`, `mod`
- Comparison: `<`, `>`, `<=`, `>=`

**Strings Theory:**
- Literals: `"hello"`, `"world"`
- Operations: `str.++`, `str.len`, `str.at`, `str.substr`, `str.prefixof`, `str.suffixof`, `str.contains`, `str.replace`

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

### Strings & Solver Control

```lean
def stringScript := "
(declare-const s String)
(assert (= (str.len s) 5))
(assert (str.contains s \"world\"))
(check-sat)
(get-model)
(get-value (s (str.++ s \"!\")))"

#eval runScript stringScript
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
