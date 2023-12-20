import Verbose.Tactics.Initialize
import Verbose.Tactics.Widget

import ProofWidgets.Demos.Macro

open Lean Meta Elab Command

open Lean.Parser.Term (bracketedBinder)

/- **TODO**  Allow empty Given of Assume.
**FIXME**: Need better behavior for empty proofs. Currently you need to put sorry there.
-/

elab ("Exercice"<|>"Exemple") str
    "Données :" objs:bracketedBinder*
    "Hypothèses :" hyps:bracketedBinder*
    "Conclusion :" concl:term
    "Démonstration :" prf:tacticSeq "QED": command => do
  if (← getOptions).getBool `verbose.suggestion_widget then
    let tac : TSyntax `tactic ←
    Lean.TSyntax.mkInfoCanonical <$>
      `(tactic| with_suggestions
                  $prf)
    elabCommand (← `(command|example $(objs ++ hyps):bracketedBinder* : $concl := by {$tac}))
  else
    dbg_trace "No"
    elabCommand (← `(command|example $(objs ++ hyps):bracketedBinder* : $concl := by $prf))

set_option verbose.suggestion_widget true

Exercice "Test"
  Données : (n : Nat)
  Hypothèses : (hn : n = 0)
  Conclusion : True

Démonstration :

  sorry
QED
