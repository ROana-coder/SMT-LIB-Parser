/-
  SmtLib/TypeChecker.lean
  =======================
  Type inference and semantic validation for SMT-LIB 2.6
-/

import SmtLib.AST

namespace SmtLib

/- ==========================================
   INITIAL CONTEXT (Built-in signatures)
   ========================================== -/

def initialContext : Context := [
  -- Core Theory
  ("true",  Signature.mk [] Srt.bool),
  ("false", Signature.mk [] Srt.bool),
  ("not",   Signature.mk [Srt.bool] Srt.bool),
  ("and",   Signature.mk [Srt.bool, Srt.bool] Srt.bool),
  ("or",    Signature.mk [Srt.bool, Srt.bool] Srt.bool),
  ("xor",   Signature.mk [Srt.bool, Srt.bool] Srt.bool),
  ("=>",    Signature.mk [Srt.bool, Srt.bool] Srt.bool),

  -- Ints Theory
  ("+",     Signature.mk [Srt.int, Srt.int] Srt.int),
  ("-",     Signature.mk [Srt.int, Srt.int] Srt.int),
  ("*",     Signature.mk [Srt.int, Srt.int] Srt.int),
  ("div",   Signature.mk [Srt.int, Srt.int] Srt.int),
  ("mod",   Signature.mk [Srt.int, Srt.int] Srt.int),
  ("abs",   Signature.mk [Srt.int] Srt.int),
  ("<",     Signature.mk [Srt.int, Srt.int] Srt.bool),
  (">",     Signature.mk [Srt.int, Srt.int] Srt.bool),
  ("<=",    Signature.mk [Srt.int, Srt.int] Srt.bool),
  (">=",    Signature.mk [Srt.int, Srt.int] Srt.bool)
  -- NOTE: "=" and "distinct" are handled specially (polymorphic)
  -- NOTE: "ite" is handled specially (polymorphic result type)
]

/- ==========================================
   TYPE INFERENCE
   ========================================== -/

/-- Infer the sort of a term in a given context -/
def inferSort (ctx : Context) (t : Term) : Option Srt :=
  match t with
  | Term.intLit _ => some Srt.int
  | Term.stringLit _ => some Srt.string

  | Term.var name =>
      match ctx.lookup name with
      | some sig => if sig.args.isEmpty then some sig.res else none
      | none     => none

  -- Polymorphic equality: (= a b) where a and b have the same type
  | Term.app "=" [t1, t2] => do
      let s1 ← inferSort ctx t1
      let s2 ← inferSort ctx t2
      if s1 == s2 then some Srt.bool else none

  -- Polymorphic distinct: (distinct a b c ...) all same type
  | Term.app "distinct" args => do
      if args.isEmpty then none
      else
        let sorts ← args.mapM (inferSort ctx)
        match sorts with
        | [] => none
        | firstSort :: rest =>
            if rest.all (· == firstSort) then some Srt.bool else none

  -- If-then-else: (ite cond then else)
  | Term.app "ite" [cond, t1, t2] => do
      let sCond ← inferSort ctx cond
      let s1    ← inferSort ctx t1
      let s2    ← inferSort ctx t2
      if sCond == Srt.bool && s1 == s2 then some s1 else none

  -- General function application
  | Term.app fn args => do
      let sig ← ctx.lookup fn
      if sig.args.length != args.length then none
      else
        let argSorts ← args.mapM (inferSort ctx)
        if argSorts == sig.args then some sig.res else none

/- ==========================================
   COMMAND VALIDATION
   ========================================== -/

/-- Check a single command and return updated context -/
def checkCommand (ctx : Context) (cmd : Command) : Option Context :=
  match cmd with
  | Command.declareConst name res =>
      some (ctx.extend name (Signature.mk [] res))

  | Command.declareFun name args res =>
      some (ctx.extend name (Signature.mk args res))

  | Command.defineFun name args resSort body =>
      -- Create local context with function arguments
      let localCtx := args.foldl (fun c (argName, argSort) =>
          c.extend argName (Signature.mk [] argSort)
      ) ctx

      -- Check body type in local context
      match inferSort localCtx body with
      | some bodySort =>
          if bodySort == resSort then
             let argTypes := args.map (·.2)
             some (ctx.extend name (Signature.mk argTypes resSort))
          else none
      | none => none

  | Command.assert t =>
      match inferSort ctx t with
      | some Srt.bool => some ctx
      | _ => none

  | Command.setLogic _ => some ctx
  | Command.checkSat   => some ctx
  | Command.exit       => some ctx

/-- Check all commands in a script -/
def checkScript (cmds : List Command) : Bool :=
  let result := cmds.foldl (fun ctxOpt cmd =>
    match ctxOpt with
    | some ctx => checkCommand ctx cmd
    | none     => none
  ) (some initialContext)
  result.isSome

/- ==========================================
   SPECIFICATION VALIDATION
   ========================================== -/

def Command.isSetLogic : Command → Bool
  | .setLogic _ => true
  | _ => false

def Command.isDeclaration : Command → Bool
  | .declareFun .. => true
  | .declareConst .. => true
  | .defineFun .. => true
  | _ => false

def Command.isAssertOrCheck : Command → Bool
  | .assert _ => true
  | .checkSat => true
  | _ => false

def countSetLogic (p : Problem) : Nat :=
  p.commands.foldl (fun acc c => if c.isSetLogic then acc + 1 else acc) 0

def hasCheckSat (p : Problem) : Bool :=
  p.commands.any (fun c => match c with | .checkSat => true | _ => false)

/-- Check that no declarations appear after assertions -/
def noLateDecls (p : Problem) : Bool :=
  let rec go (phase : Bool) (cs : List Command) : Bool :=
    match cs with
    | []        => true
    | c :: rest =>
        if phase then
          if c.isDeclaration then false else go true rest
        else
          if c.isAssertOrCheck then go true rest else go false rest
  go false p.commands

/-- Full specification check for a problem -/
def specification (p : Problem) : Bool :=
  countSetLogic p ≤ 1 &&
  hasCheckSat p &&
  noLateDecls p &&
  checkScript p.commands

end SmtLib
