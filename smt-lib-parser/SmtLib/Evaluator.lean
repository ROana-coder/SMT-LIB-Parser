/-
  SmtLib/Evaluator.lean
  =====================
  Term evaluation (concrete execution) for SMT-LIB
-/

import SmtLib.AST
import SmtLib.PrettyPrint

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

/-- Replaces variables in `params` with values `args` inside `body`. -/
def substitute (params : List String) (args : List Term) (body : Term) : Term :=
  match body with
  | Term.intLit i => Term.intLit i
  | Term.stringLit s => Term.stringLit s
  | Term.var s =>
    -- Find the argument corresponding to the variable 's'
    match params.zip args |>.find? (fun (p, _) => p == s) with
    | some (_, val) => val
    | none => Term.var s
  | Term.app op subterms =>
    Term.app op (subterms.map (substitute params args))

/--
  Replaces custom function calls with their definitions.
  Because we ensure 'env' only contains fully expanded bodies,
  we do NOT need to recurse into the result of the substitution.
-/
def expand (env : Environment) (t : Term) : Term :=
  match t with
  | Term.app (Op.custom fn) args =>
      let args' := args.map (expand env)
      match env.funcs.lookup fn with
      | some defn =>
          if args'.length == defn.params.length then
             -- Substitute args into the ALREADY EXPANDED body
             substitute defn.params args' defn.body
          else
             Term.app (Op.custom fn) args'
      | none => Term.app (Op.custom fn) args'
  | Term.app op args =>
      Term.app op (args.map (expand env))
  | _ => t

/-- Helper to update function mapping -/
def Environment.addFunc (env : Environment) (name : String) (defn : FunctionDef) : Environment :=
  -- Expand the body BEFORE adding it to the map
  let expandedBody := expand env defn.body
  let newDefn := { defn with body := expandedBody }
  { env with funcs := (name, newDefn) :: env.funcs }

/- ==========================================
   ARITHMETIC EVALUATION
   ========================================== -/


def termToInt (t : Term) : Option Int :=
  match t with
  | Term.intLit n => some n
  | Term.stringLit _ => none
  | Term.var _    => none -- Variables should be substituted by now if they are parameters
  | Term.app Op.plus [a, b] => do
      let va ← termToInt a
      let vb ← termToInt b
      some (va + vb)
  | Term.app Op.minus [a, b] => do
      let va ← termToInt a
      let vb ← termToInt b
      some (va - vb)
  | Term.app Op.mul [a, b] => do
      let va ← termToInt a
      let vb ← termToInt b
      some (va * vb)
  | Term.app Op.minus [a] => do
      let va ← termToInt a
      some (-va)
  | Term.app Op.div [a, b] => do
      let va ← termToInt a
      let vb ← termToInt b
      if vb == 0 then none else some (va / vb)
  | Term.app Op.mod [a, b] => do
      let va ← termToInt a
      let vb ← termToInt b
      if vb == 0 then none else some (va % vb)
  | _ => none



/- ==========================================
   PROPOSITIONAL EVALUATION (to Prop)
   ========================================== -/

/-- Helper for combining propositions -/
def foldProp (op : Prop → Prop → Prop) (base : Prop) (args : List Prop) : Prop :=
  args.foldr op base

/-- Evaluate a term to a Lean Prop -/

def termToProp (t : Term) : Option Prop :=
  match t with
  | Term.var "true"      => some True
  | Term.var "false"     => some False
  | Term.stringLit _     => none
  | Term.app (Op.custom "true") []   => some True
  | Term.app (Op.custom "false") []  => some False

  -- Arithmetic comparisons
  | Term.app Op.gt [t1, t2] => do
      let v1 ← termToInt t1
      let v2 ← termToInt t2
      some (v1 > v2)

  | Term.app Op.lt [t1, t2] => do
      let v1 ← termToInt t1
      let v2 ← termToInt t2
      some (v1 < v2)

  | Term.app Op.eq [t1, t2] => do
      let v1 ← termToInt t1
      let v2 ← termToInt t2
      some (v1 = v2)

  | Term.app Op.ge [t1, t2] => do
      let v1 ← termToInt t1
      let v2 ← termToInt t2
      some (v1 ≥ v2)

  | Term.app Op.le [t1, t2] => do
      let v1 ← termToInt t1
      let v2 ← termToInt t2
      some (v1 ≤ v2)

  -- Logical operators
  | Term.app Op.not [t] =>
      match termToProp t with
      | some p => some (¬p)
      | none => none

  | Term.app Op.and args =>
      match args.mapM termToProp with
      | some ps => some (foldProp And True ps)
      | none => none

  | Term.app Op.or args =>
      match args.mapM termToProp with
      | some ps => some (foldProp Or False ps)
      | none => none

  | Term.app Op.imp [t1, t2] =>
      match termToProp t1, termToProp t2 with
      | some p1, some p2 => some (p1 → p2)
      | _, _ => none

  -- If-then-else
  | Term.app Op.ite [c, t, e] =>
      match termToProp c, termToProp t, termToProp e with
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
def evalTerm (t : Term) : Option Bool :=
  match t with
  | Term.var "true"     => some true
  | Term.var "false"    => some false
  | Term.app (Op.custom "true") []  => some true
  | Term.app (Op.custom "false") [] => some false

  -- Arithmetic comparisons
  | Term.app Op.gt [t1, t2] => do
      let v1 ← termToInt t1
      let v2 ← termToInt t2
      some (v1 > v2)

  | Term.app Op.lt [t1, t2] => do
      let v1 ← termToInt t1
      let v2 ← termToInt t2
      some (v1 < v2)

  | Term.app Op.eq [t1, t2] => do
      let v1 ← termToInt t1
      let v2 ← termToInt t2
      some (v1 == v2)

  | Term.app Op.ge [t1, t2] => do
      let v1 ← termToInt t1
      let v2 ← termToInt t2
      some (v1 >= v2)

  | Term.app Op.le [t1, t2] => do
      let v1 ← termToInt t1
      let v2 ← termToInt t2
      some (v1 <= v2)

  -- If-then-else
  | Term.app Op.ite [c, t, e] =>
      match evalTerm c with
      | some condVal => if condVal then evalTerm t else evalTerm e
      | none => none

  -- Logical operators
  | Term.app Op.not [t] =>
      match evalTerm t with
      | some b => some (!b)
      | none => none

  | Term.app Op.and args =>
      match args.mapM evalTerm with
      | some bs => some (foldBool (· && ·) true bs)
      | none => none

  | Term.app Op.or args =>
      match args.mapM evalTerm with
      | some bs => some (foldBool (· || ·) false bs)
      | none => none

  | Term.app Op.imp [t1, t2] =>
      match evalTerm t1, evalTerm t2 with
      | some b1, some b2 => some (!b1 || b2)
      | _, _ => none

  | _ => none

/- ==========================================
   COMMAND EVALUATION
   ========================================== -/

/-- Evaluate an assert command -/
def evaluate (env : Environment) (t : Term) : Option Int :=
  -- 1. Expand macros/functions
  let t' := expand env t
  -- 2. Evaluate pure term
  termToInt t'

def evalAssert (c : Command) : Option Bool :=
  match c with
  | .assert t => evalTerm (expand defaultEnv t)
  | _         => none


/-- Convert an assert command to a Prop using current environment -/
@[reducible]
def specAssert (c : Command) (env : Environment := defaultEnv) : Option Prop :=
  match c with
  | .assert t => termToProp (expand env t)
  | _         => none


/-
  specProblemSat: Returns a Prop that is satisfiable iff there exists
  a valuation (assignment of Int values to variables) that makes all
  assertions true.

  For example:
    (declare-const x Int)
    (assert (> x 5))
    (assert (< x 10))

  Becomes: ∃ (vals : String → Int), x > 5 ∧ x < 10
           where x is looked up via vals "x"
-/

/-- Evaluate a term to Int using a valuation function for variables -/
def termToIntVal (vals : String → Int) (t : Term) : Option Int :=
  match t with
  | Term.intLit n => some n
  | Term.stringLit _ => none
  | Term.var s => some (vals s)
  | Term.app Op.plus [a, b] => do
      let va ← termToIntVal vals a
      let vb ← termToIntVal vals b
      some (va + vb)
  | Term.app Op.minus [a, b] => do
      let va ← termToIntVal vals a
      let vb ← termToIntVal vals b
      some (va - vb)
  | Term.app Op.mul [a, b] => do
      let va ← termToIntVal vals a
      let vb ← termToIntVal vals b
      some (va * vb)
  | Term.app Op.minus [a] => do
      let va ← termToIntVal vals a
      some (-va)
  | Term.app Op.div [a, b] => do
      let va ← termToIntVal vals a
      let vb ← termToIntVal vals b
      if vb == 0 then none else some (va / vb)
  | Term.app Op.mod [a, b] => do
      let va ← termToIntVal vals a
      let vb ← termToIntVal vals b
      if vb == 0 then none else some (va % vb)
  | _ => none

/-- Evaluate a term to Prop using a valuation function for variables -/
def termToPropVal (vals : String → Int) (t : Term) : Option Prop :=
  match t with
  | Term.var "true"  => some True
  | Term.var "false" => some False
  | Term.app (Op.custom "true") []  => some True
  | Term.app (Op.custom "false") [] => some False

  | Term.app Op.gt [t1, t2] => do
      let v1 ← termToIntVal vals t1
      let v2 ← termToIntVal vals t2
      some (v1 > v2)

  | Term.app Op.lt [t1, t2] => do
      let v1 ← termToIntVal vals t1
      let v2 ← termToIntVal vals t2
      some (v1 < v2)

  | Term.app Op.eq [t1, t2] => do
      let v1 ← termToIntVal vals t1
      let v2 ← termToIntVal vals t2
      some (v1 = v2)

  | Term.app Op.ge [t1, t2] => do
      let v1 ← termToIntVal vals t1
      let v2 ← termToIntVal vals t2
      some (v1 ≥ v2)

  | Term.app Op.le [t1, t2] => do
      let v1 ← termToIntVal vals t1
      let v2 ← termToIntVal vals t2
      some (v1 ≤ v2)

  | Term.app Op.not [t] =>
      match termToPropVal vals t with
      | some p => some (¬p)
      | none => none

  | Term.app Op.and args =>
      match args.mapM (termToPropVal vals) with
      | some ps => some (foldProp And True ps)
      | none => none

  | Term.app Op.or args =>
      match args.mapM (termToPropVal vals) with
      | some ps => some (foldProp Or False ps)
      | none => none

  | Term.app Op.imp [t1, t2] =>
      match termToPropVal vals t1, termToPropVal vals t2 with
      | some p1, some p2 => some (p1 → p2)
      | _, _ => none

  | _ => none

/--
  Build the body of the SAT proposition: conjunction of all assertions
  evaluated with the given valuation.
-/
def buildSatBody (vals : String → Int) (cmds : List Command) (env : Environment) : Prop :=
  let (props, _) := cmds.foldl (fun (acc, e) cmd =>
    match cmd with
    | Command.defineFun name args _ body =>
        let params := args.map Prod.fst
        let defn : FunctionDef := { params := params, body := body }
        (acc, e.addFunc name defn)
    | Command.assert t =>
        match termToPropVal vals (expand e t) with
        | some p => (p :: acc, e)
        | none => (acc, e)
    | _ => (acc, e)
  ) ([], env)
  props.foldl (· ∧ ·) True

/--
  specProblemSat: The satisfiability proposition.
  Returns: ∃ (vals : String → Int), <all assertions hold under vals>

  This Prop is provable iff there exists a variable assignment
  that satisfies all assertions.
-/
def specProblemSat (cmds : List Command) : Prop :=
  ∃ (vals : String → Int), buildSatBody vals cmds defaultEnv

/--
  String representation of the SAT proposition.
  Shows the existential structure in a human-readable format.
-/
def specProblemSatStr (cmds : List Command) : String :=
  -- Collect declared variables
  let vars := cmds.filterMap fun cmd =>
    match cmd with
    | Command.declareConst name _ => some name
    | _ => none
  -- Collect assertions
  let asserts := cmds.filterMap fun cmd =>
    match cmd with
    | Command.assert t => some (toString t)
    | _ => none
  -- Build the string
  let varStr := String.intercalate ", " vars
  let assertStr := String.intercalate " ∧ " asserts
  s!"∃ ({varStr} : Int), {assertStr}"

def specProblem (cmds : List SmtLib.Command) (inputEnv : SmtLib.Environment := SmtLib.defaultEnv) : Prop :=
  let (props, _) := cmds.foldl (fun (acc, env) cmd =>
    match cmd with
    | SmtLib.Command.defineFun name args _ body =>
        let params := args.map Prod.fst
        let defn : SmtLib.FunctionDef := { params := params, body := body }
        (acc, env.addFunc name defn)
    | SmtLib.Command.assert t =>
        match SmtLib.termToProp (expand env t) with
        | some p => (p :: acc, env)
        | none => (acc, env) -- Skip invalid props
    | _ => (acc, env)
  ) ([], inputEnv)

  props.foldl (· ∧ ·) True

/-- Evaluate a list of commands to a boolean (conjunctive) -/
def checkProblem (cmds : List Command) (inputEnv : Environment := defaultEnv) : Bool :=
  let (bools, _) := cmds.foldl (fun (acc, env) cmd =>
    match cmd with
    | Command.defineFun name args _ body =>
        let params := args.map Prod.fst
        let defn : FunctionDef := { params := params, body := body }
        (acc, env.addFunc name defn)
    | Command.assert t =>
        match evalTerm (expand env t) with
        | some b => (b :: acc, env)
        | none => (acc, env)
    | _ => (acc, env)
  ) ([], inputEnv)

  bools.foldl (· && ·) true

end SmtLib
