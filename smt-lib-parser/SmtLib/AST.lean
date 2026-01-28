/-
  SmtLib/AST.lean
  ===============
  Abstract Syntax Tree definitions for SMT-LIB 2.6
-/

namespace SmtLib

/- ==========================================
   SORTS (Types)
   ========================================== -/

inductive Srt where
  | bool
  | int
  | string
  | ident (name : String)
  deriving Repr, BEq, Inhabited

/- ==========================================
   TERMS (Expressions)
   ========================================== -/

inductive Term where
  | var    (name : String)
  | intLit (val  : Int)
  | stringLit (val : String)
  | app    (fn   : String) (args : List Term)
  deriving Repr, BEq, Inhabited

/- ==========================================
   COMMANDS
   ========================================== -/

inductive Command where
  | setLogic     (name : String)
  | declareConst (name : String) (srt : Srt)
  | declareFun   (name : String) (argSorts : List Srt) (resSort : Srt)
  | defineFun    (name : String) (args : List (String × Srt)) (resSort : Srt) (body : Term)
  | assert       (t : Term)
  | checkSat
  | getModel
  | getValue     (terms : List Term)
  | exit
  deriving Repr, BEq

/- ==========================================
   PROBLEM (Script)
   ========================================== -/

structure Problem where
  commands : List Command
  deriving BEq, Repr, Inhabited

/- ==========================================
   S-EXPRESSIONS (Low-level parsing)
   ========================================== -/

inductive SExp where
  | sym  (s : String)
  | num  (n : Int)
  | str  (s : String)
  | list (xs : List SExp)
  deriving Repr, BEq

namespace SExp

def asSym : SExp → Option String
  | .sym s => some s
  | _      => none

def asList : SExp → Option (List SExp)
  | .list xs => some xs
  | _        => none

def asNum : SExp → Option Int
  | .num n => some n
  | _      => none

end SExp

/- ==========================================
   SIGNATURES (for type checking)
   ========================================== -/

structure Signature where
  args : List Srt
  res  : Srt
  deriving Repr, BEq

abbrev Context := List (String × Signature)

def Context.lookup (ctx : Context) (name : String) : Option Signature :=
  List.lookup name ctx

def Context.extend (ctx : Context) (name : String) (sig : Signature) : Context :=
  (name, sig) :: ctx

end SmtLib
