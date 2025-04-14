import Verbose.Tactics.Statements
import Verbose.French.Widget

open Lean Meta Elab Command Parser Tactic

open Lean.Parser.Term (bracketedBinder)

implement_endpoint (lang := fr) mkWidgetProof (prf : TSyntax ``tacticSeq) (tkp : Syntax) : CoreM (TSyntax `tactic) :=
  -- the token itself should have the info of `Proof:` so that incrementality is not disabled but
  -- the overall syntax node should have the full ref (the proof block) as canonical info so that
  -- the widget is shown on the entire block
  Lean.TSyntax.mkInfoCanonical <$> `(tactic| with_suggestions%$tkp $prf)

implement_endpoint (lang := fr) victoryMessage : CoreM String := return "Gagné 🎉"
implement_endpoint (lang := fr) noVictoryMessage : CoreM String := return "L’exercice n’est pas terminé."

/- **TODO**  Allow omitting Données or Hypothèses. -/

syntax ("Exercice"<|>"Exemple") str
    "Données :" bracketedBinder*
    "Hypothèses :" bracketedBinder*
    "Conclusion :" term
    "Démonstration :" (tacticSeq)? ("QED" <|> "CQFD") : command

@[incremental]
elab_rules : command
| `(command|Exercice $_str
    Données : $objs:bracketedBinder*
    Hypothèses : $hyps:bracketedBinder*
    Conclusion : $concl:term
    Démonstration :%$tkp $(prf?)? QED%$tkq) => do
  mkExercise none objs hyps concl prf? tkp tkq

@[incremental]
elab_rules : command
| `(command|Exemple $_str
    Données : $objs:bracketedBinder*
    Hypothèses : $hyps:bracketedBinder*
    Conclusion : $concl:term
    Démonstration :%$tkp $(prf?)? QED%$tkq) => do
  mkExercise none objs hyps concl prf? tkp tkq

syntax ("Exercice-lemme"<|>"Lemme") ident str
    "Données :" bracketedBinder*
    "Hypothèses :" bracketedBinder*
    "Conclusion :" term
    "Démonstration :" (tacticSeq)? ("QED" <|> "CQFD") : command

@[incremental]
elab_rules : command
| `(command|Exercice-lemme $name $_str
    Données : $objs:bracketedBinder*
    Hypothèses : $hyps:bracketedBinder*
    Conclusion : $concl:term
    Démonstration :%$tkp $(prf?)? QED%$tkq) => do
  mkExercise (some name) objs hyps concl prf? tkp tkq

@[incremental]
elab_rules : command
| `(command|Lemme $name $_str
    Données : $objs:bracketedBinder*
    Hypothèses : $hyps:bracketedBinder*
    Conclusion : $concl:term
    Démonstration :%$tkp $(prf?)? QED%$tkq) => do
  mkExercise (some name) objs hyps concl prf? tkp tkq
