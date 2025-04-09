import Verbose.Tactics.Statements
import Verbose.Tactics.Common
import Verbose.English.Widget

open Lean Meta Elab Command Parser Tactic

open Lean.Parser.Term (bracketedBinder)

implement_endpoint (lang := en) mkWidgetProof (prf : TSyntax ``tacticSeq) (tkp : Syntax) : CoreM (TSyntax `tactic) :=
  -- the token itself should have the info of `Proof:` so that incrementality is not disabled but
  -- the overall syntax node should have the full ref (the proof block) as canonical info so that
  -- the widget is shown on the entire block
  Lean.TSyntax.mkInfoCanonical <$> `(tactic| with_suggestions%$tkp $prf)

implement_endpoint (lang := en) victoryMessage : CoreM String := return "Victory 🎉"
implement_endpoint (lang := en) noVictoryMessage : CoreM String := return "The exercise is not done."

/- **TODO**  Allow omitting Given or Assume. -/

syntax ("Exercise"<|>"Example") str
    "Given:" bracketedBinder*
    "Assume:" bracketedBinder*
    "Conclusion:" term
    "Proof:" (tacticSeq)? "QED" : command

@[incremental]
elab_rules : command
| `(command|Exercise $_str
    Given: $objs:bracketedBinder*
    Assume: $hyps:bracketedBinder*
    Conclusion: $concl:term
    Proof:%$tkp $(prf?)? QED%$tkq) => do
  mkExercise none objs hyps concl prf? tkp tkq

@[incremental]
elab_rules : command
| `(command|Example $_str
    Given: $objs:bracketedBinder*
    Assume: $hyps:bracketedBinder*
    Conclusion: $concl:term
    Proof:%$tkp $(prf?)? QED%$tkq) => do
  mkExercise none objs hyps concl prf? tkp tkq

syntax ("Exercise-lemma"<|>"Lemma") ident str
    "Given:" bracketedBinder*
    "Assume:" bracketedBinder*
    "Conclusion:" term
    "Proof:" (tacticSeq)? "QED" : command

@[incremental]
elab_rules : command
| `(command|Exercise-lemma $name $_str
    Given: $objs:bracketedBinder*
    Assume: $hyps:bracketedBinder*
    Conclusion: $concl:term
    Proof:%$tkp $(prf?)? QED%$tkq) => do
  mkExercise (some name) objs hyps concl prf? tkp tkq

@[incremental]
elab_rules : command
| `(command|Lemma $name $_str
    Given: $objs:bracketedBinder*
    Assume: $hyps:bracketedBinder*
    Conclusion: $concl:term
    Proof:%$tkp $(prf?)? QED%$tkq) => do
  mkExercise (some name) objs hyps concl prf? tkp tkq
