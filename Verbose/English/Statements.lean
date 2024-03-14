import Verbose.Infrastructure.Initialize
import Verbose.Tactics.Statements
import Verbose.English.Widget

import ProofWidgets.Demos.Macro

open Lean Meta Elab Command Parser Tactic

open Lean.Parser.Term (bracketedBinder)

endpoint (lang := en) mkProof (prf : TSyntax ``tacticSeq) : CoreM (TSyntax `tactic) :=
Lean.TSyntax.mkInfoCanonical <$> `(tactic| with_suggestions $prf)

/- **TODO**  Allow omitting Given or Assume. -/

elab name?:(ident)? ("Exercise"<|>"Example") str
    "Given:" objs:bracketedBinder*
    "Assume:" hyps:bracketedBinder*
    "Conclusion:" concl:term
    tkp:"Proof:" prf?:(tacticSeq)? tkq:"QED" : command => do
  mkExercise name? objs hyps concl prf? tkp tkq
