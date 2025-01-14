import Mathlib.Tactic.Lemma
import Verbose.Infrastructure.Multilingual

open Lean Meta Elab Command Parser Tactic

open Lean.Parser.Term (bracketedBinder)

register_endpoint mkWidgetProof (prf : TSyntax ``tacticSeq) : CoreM (TSyntax `tactic)

def mkExercise (name? : Option Ident) (objs hyps : TSyntaxArray ``bracketedBinder) (concl: Term)
    (prf?: Option (TSyntax ``tacticSeq)) (tkp tkq : Syntax) : CommandElabM Unit := do
  let ref := mkNullNode #[tkp, tkq]
  let prf ← prf?.getDM <| withRef ref `(tacticSeq| skip)
  let term ← withRef tkq `(by%$ref
    skip%$ref
    ($prf)
    skip%$ref)
  let config ← verboseConfigurationExt.get
  if config.useSuggestionWidget then
    let tac : TSyntax `tactic ← liftCoreM <| mkWidgetProof prf
    if let some name := name? then
      elabCommand (← `(command|lemma $name $(objs ++ hyps):bracketedBinder* : $concl := by {$tac}))
    else
      elabCommand (← `(command|example $(objs ++ hyps):bracketedBinder* : $concl := by {$tac}))
  else
    if let some name := name? then
      elabCommand (← `(command|lemma $name $(objs ++ hyps):bracketedBinder* : $concl := $term))
    else
      elabCommand (← `(command|example $(objs ++ hyps):bracketedBinder* : $concl := $term))
  if let some name := name? then
    if config.autoRegisterAnonymousLemma then
      elabCommand (← `(command|addAnonymousFactSplittingLemma $name))
