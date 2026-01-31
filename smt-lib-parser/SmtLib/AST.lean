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

inductive Op where
  | plus | minus | mul | div | mod
  | not | and | or | xor | imp
  | eq | lt | gt | le | ge
  | ite
  | distinct
  | num (n : Int) -- For numeric literals in operator position if needed, though usually not an Op
  | str (s : String) -- For string literals in operator position
  | custom (name : String)
  deriving Repr, BEq, Inhabited

def Op.toString : Op → String
  | .plus => "+"
  | .minus => "-"
  | .mul => "*"
  | .div => "div"
  | .mod => "mod"
  | .not => "not"
  | .and => "and"
  | .or => "or"
  | .xor => "xor"
  | .imp => "=>"
  | .eq => "="
  | .lt => "<"
  | .gt => ">"
  | .le => "<="
  | .ge => ">="
  | .ite => "ite"
  | .distinct => "distinct"
  | .num n => s!"{n}"
  | .str s => s
  | .custom s => s

instance : ToString Op := ⟨Op.toString⟩

inductive Term where
  | var    (name : String)
  | intLit (val  : Int)
  | stringLit (val : String)
  | app    (op   : Op) (args : List Term)
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
