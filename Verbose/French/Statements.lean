import Lean

open Lean Meta Elab Command

open Lean.Parser.Term (bracketedBinder)

/- **TODO**  Allow empty Given of Assume. -/

elab ("Exercice"<|>"Exemple") str
    "Données :" objs:bracketedBinder*
    "Hypothèses :" hyps:bracketedBinder*
    "Conclusion :" concl:term
    "Démonstration :" prf:tacticSeq "QED": command => do
  elabCommand (← `(command|example $(objs ++ hyps):bracketedBinder* : $concl := by $prf))


Exercice "Test"
  Données : (n : Nat)
  Hypothèses : (hn : n = 0)
  Conclusion : True

Démonstration :
  sorry
QED
