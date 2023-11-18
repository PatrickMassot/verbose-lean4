import Lean

open Lean Meta Elab Command

open Lean.Parser.Term (bracketedBinder)

elab "Exercise" str
    "Given:" objs:bracketedBinder*
    "Assume:" hyps:bracketedBinder*
    "Conclusion:" concl:term
    "Proof:" prf:tacticSeq "QED": command => do
  elabCommand (← `(command|example $(objs ++ hyps):bracketedBinder* : $concl := by $prf))


Exercise "Test"
  Given: (n : Nat)
  Assume: (hn : n = 0)
  Conclusion: True

  Proof:
  sorry
  QED
