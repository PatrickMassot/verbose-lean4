import Verbose.Tactics.Statements
import Verbose.Tactics.Common
import Verbose.Spanish.Widget

open Lean Meta Elab Command Parser Tactic

open Lean.Parser.Term (bracketedBinder)

implement_endpoint (lang := es) mkWidgetProof (prf : TSyntax ``tacticSeq) (tkp : Syntax) : CoreM (TSyntax `tactic) :=
  -- the token itself should have the info of `Proof:` so that incrementality is not disabled but
  -- the overall syntax node should have the full ref (the proof block) as canonical info so that
  -- the widget is shown on the entire block
  Lean.TSyntax.mkInfoCanonical <$> `(tactic| with_suggestions%$tkp $prf)

implement_endpoint (lang := es) victoryMessage : CoreM String := return "¡Victoria! 🎉"
implement_endpoint (lang := es) noVictoryMessage : CoreM String := return "El ejercicio no está terminado."

/- **TODO**  Allow omitting Dado or Asume. -/

syntax ("Ejercicio"<|>"Ejemplo") str
    "Dado:" bracketedBinder*
    "Asumimos:" bracketedBinder*
    "Conclusión:" term
    "Demostración:" (tacticSeq)? "QED" : command

@[incremental]
elab_rules : command
| `(command|Ejercicio $_str
    Dado: $objs:bracketedBinder*
    Asumimos: $hyps:bracketedBinder*
    Conclusión: $concl:term
    Demostración:%$tkp $(prf?)? QED%$tkq) => do
  mkExercise none objs hyps concl prf? tkp tkq

@[incremental]
elab_rules : command
| `(command|Ejemplo $_str
    Dado: $objs:bracketedBinder*
    Asumimos: $hyps:bracketedBinder*
    Conclusión: $concl:term
    Demostración:%$tkp $(prf?)? QED%$tkq) => do
  mkExercise none objs hyps concl prf? tkp tkq

syntax ("Ejercicio-lema"<|>"Lema") ident str
    "Dado:" bracketedBinder*
    "Asumimos:" bracketedBinder*
    "Conclusión:" term
    "Demostración:" (tacticSeq)? "QED" : command

@[incremental]
elab_rules : command
| `(command|Ejercicio-lema $name $_str
    Dado: $objs:bracketedBinder*
    Asumimos: $hyps:bracketedBinder*
    Conclusión: $concl:term
    Demostración:%$tkp $(prf?)? QED%$tkq) => do
  mkExercise (some name) objs hyps concl prf? tkp tkq

@[incremental]
elab_rules : command
| `(command|Lema $name $_str
    Dado: $objs:bracketedBinder*
    Asumimos: $hyps:bracketedBinder*
    Conclusión: $concl:term
    Demostración:%$tkp $(prf?)? QED%$tkq) => do
  mkExercise (some name) objs hyps concl prf? tkp tkq
