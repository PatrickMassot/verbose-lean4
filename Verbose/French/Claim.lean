import Verbose.Tactics.Lets
import Verbose.French.Common

open Lean Verbose.French

macro ("Fait" <|> "Affirmation") name:ident ":" stmt:term "car" colGt prf:tacticSeq : tactic => `(tactic|(checkName $name; have $name : $stmt := by $prf))

macro "On" (" observe " <|> " obtient ") name:ident ":" stmt:term : tactic => `(tactic|(checkName $name; have $name : $stmt := by strongAssumption))

open Lean Elab Tactic

elab ("Fait" <|> "Affirmation") name:ident ":" stmt:term "par" prf:maybeAppliedFR : tactic => do
  let prfTerm ← maybeAppliedFRToTerm prf
  evalTactic (← `(tactic|have $name : $stmt := by exact $prfTerm))

example : 1 = 1 := by
  Fait H : 1 = 1 car
    rfl
  exact H

set_option linter.unusedVariables false

example (n : ℕ) : n + n + n = 3*n := by
  Affirmation key : n + n = 2*n car
    ring
  ring

example (n : ℤ) (h : 0 < n) : True := by
  Fait key : 0 < 2*n car
    linarith only [h]
  Fait keybis : 0 < 2*n par mul_pos appliqué à [zero_lt_two, h]
  On observe keyter : 0 < 2* n
  On obtient keyquadro : 0 < 2* n
  trivial
