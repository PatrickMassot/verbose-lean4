import Verbose.Tactics.Initialize
import Verbose.English.Widget

import ProofWidgets.Demos.Macro

open Lean Meta Elab Command

open Lean.Parser.Term (bracketedBinder)

/- **TODO**  Allow empty Given of Assume. -/

elab ("Exercise"<|>"Example") str
    "Given:" objs:bracketedBinder*
    "Assume:" hyps:bracketedBinder*
    "Conclusion:" concl:term
    "Proof:" prf:tacticSeq "QED": command => do
  if (← getOptions).getBool `verbose.suggestion_widget then
    let tac : TSyntax `tactic ←
    Lean.TSyntax.mkInfoCanonical <$>
      `(tactic| with_suggestions
                  $prf)
    elabCommand (← `(command|example $(objs ++ hyps):bracketedBinder* : $concl := by {$tac}))
  else
    elabCommand (← `(command|example $(objs ++ hyps):bracketedBinder* : $concl := by $prf))
