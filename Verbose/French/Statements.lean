import Verbose.Tactics.Initialize
import Verbose.French.Widget

import ProofWidgets.Demos.Macro

open Lean Meta Elab Command Parser Tactic

open Lean.Parser.Term (bracketedBinder)

/- **TODO**  Allow empty Given of Assume. -/

elab ("Exercice"<|>"Exemple") str
    "Données :" objs:bracketedBinder*
    "Hypothèses :" hyps:bracketedBinder*
    "Conclusion :" concl:term
    tkp:"Démonstration :" prf?:(tacticSeq)? tk:"QED" : command => do
  let ref := mkNullNode #[tkp, tk]
  let prf ← prf?.getDM <| withRef ref `(tacticSeq| skip)
  let term ← withRef tk `(by%$ref
    skip%$ref
    ($prf)
    skip%$ref)
  if (← getOptions).getBool `verbose.suggestion_widget then
    let tac : TSyntax `tactic ←
    Lean.TSyntax.mkInfoCanonical <$>
      `(tactic| with_suggestions
                  $prf)
    elabCommand (← `(command|example $(objs ++ hyps):bracketedBinder* : $concl := by {$tac}))
  else
    elabCommand (← `(command|example $(objs ++ hyps):bracketedBinder* : $concl := $term))
