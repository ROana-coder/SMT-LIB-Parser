import SmtLib
import SmtLib.Evaluator

set_option maxHeartbeats 1000000


open SmtLib

def testScript := "
(define-fun f ((x Int)) Int (+ x 1))
(assert (= (f 10) 11))
"

-- Use #reduce to view the generated Prop
def prob : Option SmtLib.Problem := parse testScript

def prop : Option Prop := 
  match prob with
  | some p => specProblem p.commands
  | none => none

#eval match prop with | some _ => "✅ Success" | none => "❌ Fail"
