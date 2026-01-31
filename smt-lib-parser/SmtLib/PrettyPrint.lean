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
  | .string   => "String"
  | .ident s  => s

instance : ToString Srt := ⟨Srt.toString⟩

/- ==========================================
   TERM TO STRING (Mathematical notation)
   ========================================== -/

/-- Convert a term to a human-readable mathematical string -/
def Term.toString (t : Term) : String :=
  match t with
  | Term.intLit n => s!"{n}"
  | Term.stringLit s => s!"\"{s}\""
  | Term.var s    => s

  -- Logical operators (mathematical symbols)
  | Term.app Op.not [x] => s!"(¬ {x.toString})"
  | Term.app Op.and args => s!"({String.intercalate " ∧ " (args.map Term.toString)})"
  | Term.app Op.or  args => s!"({String.intercalate " ∨ " (args.map Term.toString)})"
  | Term.app Op.imp  [a, b] => s!"({a.toString} → {b.toString})"

  -- If-then-else
  | Term.app Op.ite [c, t, e] =>
      s!"(if {c.toString} then {t.toString} else {e.toString})"

  -- Distinct
  | Term.app Op.distinct args =>
      s!"(distinct {String.intercalate " " (args.map Term.toString)})"

  -- Binary operators (infix notation)
  | Term.app op [a, b] =>
      match op with
      | Op.plus | Op.minus | Op.mul | Op.div | Op.mod
      | Op.eq | Op.lt | Op.gt | Op.le | Op.ge =>
          s!"({a.toString} {op.toString} {b.toString})"
      | _ =>
          s!"({op.toString} {a.toString} {b.toString})"

  -- General application (prefix)
  | Term.app op args =>
      s!"({op.toString} {String.intercalate " " (args.map Term.toString)})"

instance : ToString Term := ⟨Term.toString⟩

/- ==========================================
   TERM TO SMT-LIB STRING (S-expression)
   ========================================== -/

/-- Convert a term back to SMT-LIB s-expression format -/
def Term.toSExp (t : Term) : String :=
  match t with
  | Term.intLit n => if n < 0 then s!"(- {-n})" else s!"{n}"
  | Term.stringLit s => s!"\"{s}\""
  | Term.var s    => s
  | Term.app (Op.custom fn) [] => fn
  | Term.app op args =>
      s!"({op.toString} {String.intercalate " " (args.map Term.toSExp)})"

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
  | .getModel => "(get-model)"
  | .getValue terms =>
      let ts := String.intercalate " " (terms.map Term.toSExp)
      s!"(get-value ({ts}))"
  | .exit => "(exit)"

instance : ToString Command := ⟨Command.toString⟩

/- ==========================================
   PROBLEM TO STRING
   ========================================== -/

def Problem.toString (p : Problem) : String :=
  String.intercalate "\n" (p.commands.map Command.toString)

instance : ToString Problem := ⟨Problem.toString⟩

end SmtLib
