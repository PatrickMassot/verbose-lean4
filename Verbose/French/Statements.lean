import Verbose.Tactics.Initialize
import Verbose.Tactics.Widget

open Lean Meta Elab Command

open Lean.Parser.Term (bracketedBinder)

/- **TODO**  Allow empty Given of Assume. -/

elab ("Exercice"<|>"Exemple") str
    "Données :" objs:bracketedBinder*
    "Hypothèses :" hyps:bracketedBinder*
    "Conclusion :" concl:term
    "Démonstration :" prf:tacticSeq "QED": command => do
  let opts ← getOptions
  if opts.getBool `verbose_widget then
    dbg_trace "Yes"
    elabCommand (← `(command|example $(objs ++ hyps):bracketedBinder* : $concl := by
      with_suggestions
      $prf))
  else
    dbg_trace "No"
    elabCommand (← `(command|example $(objs ++ hyps):bracketedBinder* : $concl := by $prf))

set_option verbose_widget true

Exercice "Test"
  Données : (n : Nat)
  Hypothèses : (hn : n = 0)
  Conclusion : True

Démonstration :

  sorry
QED
