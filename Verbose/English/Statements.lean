import Verbose.Infrastructure.Initialize
import Verbose.English.Widget

import ProofWidgets.Demos.Macro

open Lean Meta Elab Command Parser Tactic

open Lean.Parser.Term (bracketedBinder)

/- **TODO**  Allow empty Given of Assume. -/

elab ("Exercise"<|>"Example") str
    "Given:" objs:bracketedBinder*
    "Assume:" hyps:bracketedBinder*
    "Conclusion:" concl:term
    tkp:"Proof:" prf?:(tacticSeq)? tk:"QED" : command => do
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
