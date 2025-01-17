import Verbose.Tactics.Statements
import Verbose.French.Widget

import ProofWidgets.Demos.Macro

open Lean Meta Elab Command Parser Tactic

open Lean.Parser.Term (bracketedBinder)

implement_endpoint (lang := fr) mkWidgetProof (prf : TSyntax ``tacticSeq) : CoreM (TSyntax `tactic) :=
Lean.TSyntax.mkInfoCanonical <$> `(tactic| with_suggestions $prf)

implement_endpoint (lang := fr) victoryMessage : CoreM String := return "Gagné 🎉"
implement_endpoint (lang := fr) noVictoryMessage : CoreM String := return "L’exercice n’est pas terminé."

/- **TODO**  Allow omitting Données or Hypothèses. -/

elab ("Exercice"<|>"Exemple") str
    "Données :" objs:bracketedBinder*
    "Hypothèses :" hyps:bracketedBinder*
    "Conclusion :" concl:term
    tkp:"Démonstration :" prf?:(tacticSeq)? tkq:"QED" : command => do
  mkExercise none objs hyps concl prf? tkp tkq

elab ("Exercice-lemme"<|>"Lemme") name:ident str
    "Données :" objs:bracketedBinder*
    "Hypothèses :" hyps:bracketedBinder*
    "Conclusion :" concl:term
    tkp:"Démonstration :" prf?:(tacticSeq)? tkq:"QED" : command => do
  mkExercise (some name) objs hyps concl prf? tkp tkq
