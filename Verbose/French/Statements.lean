import Verbose.Infrastructure.Initialize
import Verbose.Tactics.Statements
import Verbose.French.Widget

import ProofWidgets.Demos.Macro

open Lean Meta Elab Command Parser Tactic

open Lean.Parser.Term (bracketedBinder)

implement_endpoint (lang := fr) mkProof (prf : TSyntax ``tacticSeq) : CoreM (TSyntax `tactic) :=
Lean.TSyntax.mkInfoCanonical <$> `(tactic| with_suggestions $prf)

/- **TODO**  Allow omitting Données or Hypothèses. -/

elab name?:(ident)? ("Exercice"<|>"Exemple") str
    "Données :" objs:bracketedBinder*
    "Hypothèses :" hyps:bracketedBinder*
    "Conclusion :" concl:term
    tkp:"Démonstration :" prf?:(tacticSeq)? tkq:"QED" : command => do
  mkExercise name? objs hyps concl prf? tkp tkq
