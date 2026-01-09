/-
  SmtLib/PrettyPrint.lean
  =======================
  String conversion and pretty printing for SMT-LIB AST
-/

import SmtLib.AST

namespace SmtLib

/- ==========================================
   SORT TO STRING
   ========================================== -/

def Srt.toString : Srt → String
  | .bool     => "Bool"
  | .int      => "Int"
  | .ident s  => s

instance : ToString Srt := ⟨Srt.toString⟩

/- ==========================================
   TERM TO STRING (Mathematical notation)
   ========================================== -/

/-- Convert a term to a human-readable mathematical string -/
partial def Term.toString (t : Term) : String :=
  match t with
  | Term.intLit n => s!"{n}"
  | Term.var s    => s

  -- Logical operators (mathematical symbols)
  | Term.app "not" [x] => s!"(¬ {x.toString})"
  | Term.app "and" args => s!"({String.intercalate " ∧ " (args.map Term.toString)})"
  | Term.app "or"  args => s!"({String.intercalate " ∨ " (args.map Term.toString)})"
  | Term.app "=>"  [a, b] => s!"({a.toString} → {b.toString})"

  -- If-then-else
  | Term.app "ite" [c, t, e] =>
      s!"(if {c.toString} then {t.toString} else {e.toString})"

  -- Distinct
  | Term.app "distinct" args =>
      s!"(distinct {String.intercalate " " (args.map Term.toString)})"

  -- Binary operators (infix notation)
  | Term.app op [a, b] =>
      if ["=", ">", "<", ">=", "<=", "+", "-", "*", "div", "mod"].contains op then
        s!"({a.toString} {op} {b.toString})"
      else
        s!"({op} {a.toString} {b.toString})"

  -- General application (prefix)
  | Term.app fn args =>
      s!"({fn} {String.intercalate " " (args.map Term.toString)})"

instance : ToString Term := ⟨Term.toString⟩

/- ==========================================
   TERM TO SMT-LIB STRING (S-expression)
   ========================================== -/

/-- Convert a term back to SMT-LIB s-expression format -/
partial def Term.toSExp (t : Term) : String :=
  match t with
  | Term.intLit n => if n < 0 then s!"(- {-n})" else s!"{n}"
  | Term.var s    => s
  | Term.app fn [] => fn
  | Term.app fn args =>
      s!"({fn} {String.intercalate " " (args.map Term.toSExp)})"

/- ==========================================
   COMMAND TO STRING
   ========================================== -/

def Command.toString : Command → String
  | .setLogic name => s!"(set-logic {name})"
  | .declareConst name srt => s!"(declare-const {name} {srt})"
  | .declareFun name args res =>
      let argsStr := String.intercalate " " (args.map Srt.toString)
      s!"(declare-fun {name} ({argsStr}) {res})"
  | .defineFun name args res body =>
      let argsStr := String.intercalate " " (args.map fun (n, s) => s!"({n} {s})")
      s!"(define-fun {name} ({argsStr}) {res} {body.toSExp})"
  | .assert t => s!"(assert {t.toSExp})"
  | .checkSat => "(check-sat)"
  | .exit => "(exit)"

instance : ToString Command := ⟨Command.toString⟩

/- ==========================================
   PROBLEM TO STRING
   ========================================== -/

def Problem.toString (p : Problem) : String :=
  String.intercalate "\n" (p.commands.map Command.toString)

instance : ToString Problem := ⟨Problem.toString⟩

end SmtLib
