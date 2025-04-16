import Verbose.Tactics.Lets
import Verbose.French.Common
import Verbose.French.We
import Verbose.French.Since

open Lean Verbose.French

macro ("Fait" <|> "Affirmation") name:ident ":" stmt:term "car" colGt prf:tacticSeq : tactic =>
withRef name `(tactic|(checkName $name; have $name : $stmt := by $prf))

macro "On" (" observe " <|> " obtient ") name:ident ":" stmt:term : tactic =>
withRef name `(tactic|(checkName $name; have $name : $stmt := by strongAssumption))

open Lean Elab Tactic

macro ("Fait" <|> "Affirmation") name:ident ":" stmt:term "par" prf:maybeAppliedFR : tactic =>
 withRef name  `(tactic|(checkName $name; have $name : $stmt := by On conclut par $prf))

macro ("Fait" <|> "Affirmation") name:ident ":" stmt:term "par calcul" : tactic =>
 withRef name  `(tactic|(checkName $name; have $name : $stmt := by On calcule))

macro ("Fait" <|> "Affirmation") name:ident ":" stmt:term "puisque" facts:factsFR : tactic =>
 withRef name  `(tactic|(checkName $name; have $name : $stmt := by Comme $facts on conclut que $stmt))

example : 1 = 1 := by
  Fait H : 1 = 1 car
    rfl
  exact H

example : 1 + 1 = 2 := by
  Fait H : 1 + 1 = 2 par calcul
  exact H

example (ε : ℝ) (ε_pos : 0 < ε) : 1 = 1 := by
  Fait H : ε ≥ 0 par ε_pos
  rfl

example (ε : ℝ) (ε_pos : 0 < ε) : 1 = 1 := by
  Fait H : ε ≥ 0 puisque ε > 0
  rfl

set_option linter.unusedVariables false

example (n : ℕ) : n + n + n = 3*n := by
  Affirmation key : n + n = 2*n car
    ring
  ring

example (n : ℤ) (h : 0 < n) : True := by
  Fait key : 0 < 2*n car
    linarith only [h]
  Fait keybis : 0 < 2*n par mul_pos appliqué à zero_lt_two et h
  On observe keyter : 0 < 2* n
  On obtient keyquadro : 0 < 2* n
  trivial
