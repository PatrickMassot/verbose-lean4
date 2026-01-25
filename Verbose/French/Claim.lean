import Verbose.Tactics.Claim
import Verbose.French.Common
import Verbose.French.We
import Verbose.French.Since

open Lean Verbose.French

namespace Verbose.Named
scoped macro ("Fait" <|> "Affirmation") name:ident ":" stmt:term "car" colGt prf:tacticSeq : tactic =>
withRef name `(tactic|(checkName $name; have $name : $stmt := by $prf))

scoped macro "On" (" observe " <|> " obtient ") name:ident ":" stmt:term : tactic =>
withRef name `(tactic|(checkName $name; have $name : $stmt := by strongAssumption))

scoped macro ("Fait" <|> "Affirmation") name:ident ":" stmt:term "par" prf:maybeAppliedFR : tactic =>
 withRef name  `(tactic|(checkName $name; have $name : $stmt := by On conclut par $prf))

scoped macro ("Fait" <|> "Affirmation") name:ident ":" stmt:term "par calcul" : tactic =>
 withRef name  `(tactic|(checkName $name; have $name : $stmt := by On calcule))

scoped macro ("Fait" <|> "Affirmation") name:ident ":" stmt:term "puisque" facts:factsFR : tactic =>
 withRef name  `(tactic|(checkName $name; have $name : $stmt := by Comme $facts on conclut que $stmt))
end Verbose.Named

namespace Verbose.NameLess
scoped elab ("Fait" <|> "Affirmation") ":" stmt:term "car" colGt prf:tacticSeq : tactic =>
  mkClaim stmt fun name ↦ `(tactic|have $name : $stmt := by $prf)

scoped elab "On " ("observe" <|> "obtient") " que " stmt:term : tactic =>
  mkClaim stmt fun name ↦ `(tactic|have $name : $stmt := by strongAssumption)

scoped elab "On obtient" news:newObjectNameLessFR : tactic => do
  let newsT ← newObjectNameLessFRToTerm news
  let news_patt := newObjectNameLessFRToRCasesPatt news
  sinceObtainTac newsT news_patt #[]

scoped elab ("Fait" <|> "Affirmation") " : " stmt:term "par" prf:maybeAppliedFR : tactic =>
  mkClaim stmt fun name ↦ `(tactic|have $name : $stmt := by On conclut par $prf)

scoped elab ("Fait" <|> "Affirmation") " : " stmt:term "par calcul" : tactic =>
  mkClaim stmt fun name ↦ `(tactic|have $name : $stmt := by On calcule)

scoped elab ("Fait" <|> "Affirmation") " : " stmt:term "puisque" facts:factsFR : tactic =>
  mkClaim stmt fun name ↦ `(tactic|have $name : $stmt := by Comme $facts on conclut que $stmt)

end Verbose.NameLess

section
open Verbose.Named

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

end

section
open Verbose.NameLess

example : 1 = 1 := by
  Fait : 1 = 1 car
    rfl
  exact h

example : 1 + 1 = 2 := by
  Fait : 1 + 1 = 2 par calcul
  exact h

example (ε : ℝ) (ε_pos : 0 < ε) : 1 = 1 := by
  Fait : ε ≥ 0 par ε_pos
  rfl

example (ε : ℝ) (ε_pos : 0 < ε) : 1 = 1 := by
  Fait : ε ≥ 0 puisque ε > 0
  rfl

set_option linter.unusedVariables false

example (n : ℕ) : n + n + n = 3*n := by
  Affirmation : n + n = 2*n car
    ring
  ring

example (n : ℤ) (h : 0 < n) : True := by
  Fait : 0 < 2*n car
    linarith only [h]
  Fait  : 0 < 2*n par mul_pos appliqué à zero_lt_two et h
  On observe que 0 < 2* n
  On obtient que 0 < 2* n
  trivial

lemma foo_ex : ∃ N : Nat, True := by simp

addAnonymousFactSplittingLemma foo_ex

example (A : ℝ) : True := by
  On obtient N : ℕ tel que True
  trivial

end

