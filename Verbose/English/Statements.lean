import Verbose.Tactics.Statements
import Verbose.English.Widget

import ProofWidgets.Demos.Macro

open Lean Meta Elab Command Parser Tactic

open Lean.Parser.Term (bracketedBinder)

implement_endpoint (lang := en) mkWidgetProof (prf : TSyntax ``tacticSeq) : CoreM (TSyntax `tactic) :=
Lean.TSyntax.mkInfoCanonical <$> `(tactic| with_suggestions $prf)

/- **TODO**  Allow omitting Given or Assume. -/

elab ("Exercise"<|>"Example") str
    "Given:" objs:bracketedBinder*
    "Assume:" hyps:bracketedBinder*
    "Conclusion:" concl:term
    tkp:"Proof:" prf?:(tacticSeq)? tkq:"QED" : command => do
  mkExercise none objs hyps concl prf? tkp tkq

elab ("Exercise-lemma"<|>"Lemma") name:ident str
    "Given:" objs:bracketedBinder*
    "Assume:" hyps:bracketedBinder*
    "Conclusion:" concl:term
    tkp:"Proof:" prf?:(tacticSeq)? tkq:"QED" : command => do
  mkExercise (some name) objs hyps concl prf? tkp tkq
