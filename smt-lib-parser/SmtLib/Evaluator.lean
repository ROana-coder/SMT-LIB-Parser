/-
  SmtLib/Evaluator.lean
  =====================
  Term evaluation (concrete execution) for SMT-LIB
-/

import SmtLib.AST

namespace SmtLib

/- ==========================================
   VALUATION (Variable Environment)
   ========================================== -/

/-- A valuation maps variable names to integer values -/
abbrev Valuation := String → Int

/-- Default valuation: all variables are 0 -/
def defaultEnv : Valuation := fun _ => 0

/- ==========================================
   ARITHMETIC EVALUATION
   ========================================== -/

/-- Evaluate a term to an integer value -/
@[reducible]
def termToInt (env : Valuation) : Term → Option Int
  | Term.intLit n => some n
  | Term.var s    => some (env s)
  | Term.app "+" [a, b] => do
      let va ← termToInt env a
      let vb ← termToInt env b
      some (va + vb)
  | Term.app "-" [a, b] => do
      let va ← termToInt env a
      let vb ← termToInt env b
      some (va - vb)
  | Term.app "*" [a, b] => do
      let va ← termToInt env a
      let vb ← termToInt env b
      some (va * vb)
  | Term.app "-" [a] => do  -- Unary minus
      let va ← termToInt env a
      some (-va)
  | _ => none

/- ==========================================
   PROPOSITIONAL EVALUATION (to Prop)
   ========================================== -/

/-- Helper for combining propositions -/
def foldProp (op : Prop → Prop → Prop) (base : Prop) (args : List Prop) : Prop :=
  args.foldr op base

/-- Evaluate a term to a Lean Prop -/
@[reducible]
def termToProp (env : Valuation) : Term → Option Prop
  -- Boolean constants
  | Term.var "true"      => some True
  | Term.var "false"     => some False
  | Term.app "true" []   => some True
  | Term.app "false" []  => some False

  -- Arithmetic comparisons
  | Term.app ">" [t1, t2] => do
      let v1 ← termToInt env t1
      let v2 ← termToInt env t2
      some (v1 > v2)

  | Term.app "<" [t1, t2] => do
      let v1 ← termToInt env t1
      let v2 ← termToInt env t2
      some (v1 < v2)

  | Term.app "=" [t1, t2] => do
      let v1 ← termToInt env t1
      let v2 ← termToInt env t2
      some (v1 = v2)

  | Term.app ">=" [t1, t2] => do
      let v1 ← termToInt env t1
      let v2 ← termToInt env t2
      some (v1 ≥ v2)

  | Term.app "<=" [t1, t2] => do
      let v1 ← termToInt env t1
      let v2 ← termToInt env t2
      some (v1 ≤ v2)

  -- Logical operators
  | Term.app "not" [t] =>
      match termToProp env t with
      | some p => some (¬p)
      | none => none

  | Term.app "and" args =>
      match args.mapM (termToProp env) with
      | some ps => some (foldProp And True ps)
      | none => none

  | Term.app "or" args =>
      match args.mapM (termToProp env) with
      | some ps => some (foldProp Or False ps)
      | none => none

  | Term.app "=>" [t1, t2] =>
      match termToProp env t1, termToProp env t2 with
      | some p1, some p2 => some (p1 → p2)
      | _, _ => none

  -- If-then-else
  | Term.app "ite" [c, t, e] =>
      match termToProp env c, termToProp env t, termToProp env e with
      | some pc, some pt, some pe => some ((pc → pt) ∧ (¬pc → pe))
      | _, _, _ => none

  | _ => none

/- ==========================================
   BOOLEAN EVALUATION (to Bool)
   ========================================== -/

/-- Helper for combining booleans -/
def foldBool (op : Bool → Bool → Bool) (base : Bool) (args : List Bool) : Bool :=
  args.foldr op base

/-- Evaluate a term to a concrete boolean value -/
partial def evalTerm : Term → Option Bool
  -- Constants
  | Term.var "true"     => some true
  | Term.var "false"    => some false
  | Term.app "true" []  => some true
  | Term.app "false" [] => some false

  -- Arithmetic comparisons (only literals)
  | Term.app ">" [Term.intLit a, Term.intLit b]  => some (a > b)
  | Term.app "<" [Term.intLit a, Term.intLit b]  => some (a < b)
  | Term.app "=" [Term.intLit a, Term.intLit b]  => some (a == b)
  | Term.app ">=" [Term.intLit a, Term.intLit b] => some (a >= b)
  | Term.app "<=" [Term.intLit a, Term.intLit b] => some (a <= b)

  -- If-then-else
  | Term.app "ite" [c, t, e] =>
      match evalTerm c with
      | some condVal => if condVal then evalTerm t else evalTerm e
      | none => none

  -- Logical operators
  | Term.app "not" [t] =>
      match evalTerm t with
      | some b => some (!b)
      | none => none

  | Term.app "and" args =>
      match args.mapM evalTerm with
      | some bs => some (foldBool (· && ·) true bs)
      | none => none

  | Term.app "or" args =>
      match args.mapM evalTerm with
      | some bs => some (foldBool (· || ·) false bs)
      | none => none

  | Term.app "=>" [t1, t2] =>
      match evalTerm t1, evalTerm t2 with
      | some b1, some b2 => some (!b1 || b2)
      | _, _ => none

  | _ => none

/- ==========================================
   COMMAND EVALUATION
   ========================================== -/

/-- Evaluate an assert command -/
def evalAssert (c : Command) : Option Bool :=
  match c with
  | .assert t => evalTerm t
  | _         => none

/-- Convert an assert command to a Prop -/
@[reducible]
def specAssert (c : Command) (env : Valuation := defaultEnv) : Option Prop :=
  match c with
  | .assert t => termToProp env t
  | _         => none

end SmtLib
