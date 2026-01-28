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

structure FunctionDef where
  params : List String
  body : Term
  deriving Repr, BEq

/-- Environment containing variable mapping and function definitions -/
structure Environment where
  vars : String → Int
  funcs : List (String × FunctionDef)

/-- Default environment -/
def defaultEnv : Environment := { vars := fun _ => 0, funcs := [] }

/-- Helper to update variable mapping -/
def Environment.extendVar (env : Environment) (name : String) (val : Int) : Environment :=
  { env with vars := fun s => if s == name then val else env.vars s }

/-- Helper to update function mapping -/
def Environment.addFunc (env : Environment) (name : String) (defn : FunctionDef) : Environment :=
  { env with funcs := (name, defn) :: env.funcs }

/- ==========================================
   ARITHMETIC EVALUATION
   ========================================== -/


def termToInt (env : Environment) (gas : Nat := 1000) (t : Term) : Option Int :=
  match gas with
  | 0 => none
  | gas' + 1 =>
    match t with
    | Term.intLit n => some n
    | Term.stringLit _ => none
    | Term.var s    => some (env.vars s)
    | Term.app "+" [a, b] => do
        let va ← termToInt env gas' a
        let vb ← termToInt env gas' b
        some (va + vb)
    | Term.app "-" [a, b] => do
        let va ← termToInt env gas' a
        let vb ← termToInt env gas' b
        some (va - vb)
    | Term.app "*" [a, b] => do
        let va ← termToInt env gas' a
        let vb ← termToInt env gas' b
        some (va * vb)
    | Term.app "-" [a] => do
        let va ← termToInt env gas' a
        some (-va)
    -- Function application
    | Term.app fn args =>
        match env.funcs.lookup fn with
        | some defn =>
            if args.length == defn.params.length then
               -- Evaluate arguments (assuming call-by-value for ints)
               match args.mapM (termToInt env gas') with
               | some argVals =>
                   -- Bind arguments to parameters
                   let newEnv := List.zip defn.params argVals |>.foldl
                     (fun e (p, v) => e.extendVar p v) env
                   -- Recursive call on body with *decremented gas*
                   termToInt newEnv gas' defn.body
               | none => none
            else none
        | none => none



/- ==========================================
   PROPOSITIONAL EVALUATION (to Prop)
   ========================================== -/

/-- Helper for combining propositions -/
def foldProp (op : Prop → Prop → Prop) (base : Prop) (args : List Prop) : Prop :=
  args.foldr op base

/-- Evaluate a term to a Lean Prop -/
def termToProp (env : Environment) (gas : Nat := 1000) (t : Term) : Option Prop :=
  match gas with
  | 0 => none
  | gas' + 1 =>
    match t with
    | Term.var "true"      => some True
    | Term.var "false"     => some False
    | Term.stringLit _     => none
    | Term.app "true" []   => some True
    | Term.app "false" []  => some False

    -- Arithmetic comparisons
    | Term.app ">" [t1, t2] => do
        let v1 ← termToInt env gas' t1
        let v2 ← termToInt env gas' t2
        some (v1 > v2)

    | Term.app "<" [t1, t2] => do
        let v1 ← termToInt env gas' t1
        let v2 ← termToInt env gas' t2
        some (v1 < v2)

    | Term.app "=" [t1, t2] => do
        let v1 ← termToInt env gas' t1
        let v2 ← termToInt env gas' t2
        some (v1 = v2)

    | Term.app ">=" [t1, t2] => do
        let v1 ← termToInt env gas' t1
        let v2 ← termToInt env gas' t2
        some (v1 ≥ v2)

    | Term.app "<=" [t1, t2] => do
        let v1 ← termToInt env gas' t1
        let v2 ← termToInt env gas' t2
        some (v1 ≤ v2)

    -- Logical operators
    | Term.app "not" [t] =>
        match termToProp env gas' t with
        | some p => some (¬p)
        | none => none

    | Term.app "and" args =>
        match args.mapM (termToProp env gas') with
        | some ps => some (foldProp And True ps)
        | none => none

    | Term.app "or" args =>
        match args.mapM (termToProp env gas') with
        | some ps => some (foldProp Or False ps)
        | none => none

    | Term.app "=>" [t1, t2] =>
        match termToProp env gas' t1, termToProp env gas' t2 with
        | some p1, some p2 => some (p1 → p2)
        | _, _ => none

    -- If-then-else
    | Term.app "ite" [c, t, e] =>
        match termToProp env gas' c, termToProp env gas' t, termToProp env gas' e with
        | some pc, some pt, some pe => some ((pc → pt) ∧ (¬pc → pe))
        | _, _, _ => none

    -- Function application (returning Bool)
    | Term.app fn args =>
        match env.funcs.lookup fn with
        | some defn =>
            if args.length == defn.params.length then
               -- Try to evaluate args as Ints first (common case)
               match args.mapM (termToInt env gas') with
               | some argVals =>
                   let newEnv := List.zip defn.params argVals |>.foldl
                     (fun e (p, v) => e.extendVar p v) env
                   termToProp newEnv gas' defn.body
               | none =>
                   -- If args aren't Ints, we can't bind them in current Environment
                   none
            else none
        | none => none

    | _ => none

/- ==========================================
   BOOLEAN EVALUATION (to Bool)
   ========================================== -/

/-- Helper for combining booleans -/
def foldBool (op : Bool → Bool → Bool) (base : Bool) (args : List Bool) : Bool :=
  args.foldr op base

/-- Evaluate a term to a concrete boolean value -/
def evalTerm (gas : Nat := 1000) (t : Term) : Option Bool :=
  match gas with
  | 0 => none
  | gas' + 1 =>
    match t with
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
        match evalTerm gas' c with
        | some condVal => if condVal then evalTerm gas' t else evalTerm gas' e
        | none => none

    -- Logical operators
    | Term.app "not" [t] =>
        match evalTerm gas' t with
        | some b => some (!b)
        | none => none

    | Term.app "and" args =>
        match args.mapM (evalTerm gas') with
        | some bs => some (foldBool (· && ·) true bs)
        | none => none

    | Term.app "or" args =>
        match args.mapM (evalTerm gas') with
        | some bs => some (foldBool (· || ·) false bs)
        | none => none

    | Term.app "=>" [t1, t2] =>
        match evalTerm gas' t1, evalTerm gas' t2 with
        | some b1, some b2 => some (!b1 || b2)
        | _, _ => none

    | _ => none

/- ==========================================
   COMMAND EVALUATION
   ========================================== -/

/-- Evaluate an assert command -/
def evalAssert (c : Command) : Option Bool :=
  match c with
  | .assert t => evalTerm 1000 t
  | _         => none


/-- Convert an assert command to a Prop using current environment -/
@[reducible]
def specAssert (c : Command) (env : Environment := defaultEnv) : Option Prop :=
  match c with
  | .assert t => termToProp env 1000 t
  | _         => none


/-- to do: de validat, sa intoarca o propozitie lean
assert x = 10
sa il transforme in exista... (env)
--/

def specProblem (cmds : List SmtLib.Command) (inputEnv : SmtLib.Environment := SmtLib.defaultEnv) : Prop :=
  let (props, _) := cmds.foldl (fun (acc, env) cmd =>
    match cmd with
    | SmtLib.Command.defineFun name args _ body =>
        let params := args.map Prod.fst
        let defn : SmtLib.FunctionDef := { params := params, body := body }
        (acc, env.addFunc name defn)
    | SmtLib.Command.assert t =>
        match SmtLib.termToProp env 1000 t with
        | some p => (p :: acc, env)
        | none => (acc, env) -- Skip invalid props
    | _ => (acc, env)
  ) ([], inputEnv)

  props.foldl (· ∧ ·) True

end SmtLib
