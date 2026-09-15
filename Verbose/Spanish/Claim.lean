import Verbose.Tactics.Claim
import Verbose.Spanish.Common
import Verbose.Spanish.We
import Verbose.Spanish.Since

open Lean Verbose.Spanish

namespace Verbose.Named
scoped macro "Afirmación" name:ident ":" stmt:term "por" colGt prf:tacticSeq: tactic =>
 withRef name  `(tactic|(checkName $name; have $name : $stmt := by $prf))

scoped macro "Afirmación" name:ident ":" stmt:term "pues" prf:maybeAppliedES : tactic => do
 withRef name  `(tactic|(checkName $name; have $name : $stmt := by Concluimos por $prf))

scoped macro "Afirmación" name:ident ":" stmt:term "por " ("cuentas" <|> "desarrollo") : tactic => do
 withRef name  `(tactic|(checkName $name; have $name : $stmt := by Desarrollamos))

scoped macro "Afirmación" name:ident ":" stmt:term "ya que" facts:factsES : tactic =>
 withRef name  `(tactic|(checkName $name; have $name : $stmt := by Como $facts concluimos que $stmt))
end Verbose.Named

namespace Verbose.NameLess
scoped elab "Afirmación" ":" stmt:term "por" colGt prf:tacticSeq : tactic =>
  mkClaim stmt fun name ↦ `(tactic|have $name : $stmt := by $prf)

scoped elab "Afirmación" ":" stmt:term "pues" prf:maybeAppliedES : tactic =>
  mkClaim stmt fun name ↦ `(tactic|have $name : $stmt := by Concluimos por $prf)

scoped elab "Afirmación" ":" stmt:term "por " ("cuentas" <|> "desarrollo") : tactic => mkClaim stmt fun name ↦  `(tactic|have $name : $stmt := by Desarrollamos)

scoped elab "Afirmación" ":" stmt:term "ya que" facts:factsES : tactic => mkClaim stmt fun name ↦
   `(tactic|have $name : $stmt := by Como $facts concluimos que $stmt)

scoped elab ("Observamos" <|> "Obtenemos" <|> "Tenemos ") " que " stmt:term : tactic =>
  mkClaim stmt fun name ↦ `(tactic|have $name : $stmt := by strongAssumption)

scoped elab ("Obtenemos " <|> "Tenemos ") news:newObjectNameLessES : tactic => do
  let newsT ← newObjectNameLessESToTerm news
  let news_patt := newObjectNameLessESToRCasesPatt news
  sinceObtainTac newsT news_patt #[]

scoped elab "Afirmación" " : " stmt:term "de" prf:maybeAppliedES : tactic =>
  mkClaim stmt fun name ↦ `(tactic|have $name : $stmt := by Concluimos por $prf)

scoped elab "Afirmación" " : " stmt:term "por " ("cuentas" <|> "desarrollo") : tactic =>
  mkClaim stmt fun name ↦ `(tactic|have $name : $stmt := by Desarrollamos)

scoped elab "Afirmación" " : " stmt:term "ya que" facts:factsES : tactic =>
  mkClaim stmt fun name ↦ `(tactic|have $name : $stmt := by Como $facts concluimos que $stmt)

end Verbose.NameLess

section
open Verbose.Named

setLang es

example : 1 = 1 := by
  Afirmación H : 1 = 1 por
    rfl
  exact H

example : 1 + 1 = 2 := by
  Afirmación H : 1 + 1 = 2 por cuentas
  exact H

example : 1 + 1 = 2 := by
  Afirmación H : 1 + 1 = 2 por desarrollo
  exact H

example (ε : ℝ) (ε_pos : 0 < ε) : 1 = 1 := by
  Afirmación H : ε ≥ 0 pues ε_pos
  rfl

example (ε : ℝ) (ε_pos : 0 < ε) : 1 = 1 := by
  Afirmación H : ε ≥ 0 ya que ε > 0
  rfl

set_option linter.unusedVariables false

example (n : ℕ) : n + n + n = 3*n := by
  Afirmación key : n + n = 2*n por
    ring
  ring

example (n : ℤ) (h : 0 < n) : True := by
  Afirmación key : 0 < 2*n por
    linarith only [h]
  Afirmación keybis : 0 < 2*n pues mul_pos aplicado a zero_lt_two ,y h
  trivial
end

section
open Verbose.NameLess
example : 1 = 1 := by
  Afirmación: 1 = 1 por
    rfl
  exact h

example : 1 + 1 = 2 := by
  Afirmación: 1 + 1 = 2 por cuentas
  exact h

example : 1 + 1 = 2 := by
  Afirmación: 1 + 1 = 2 por desarrollo
  exact h

example (ε : ℝ) (ε_pos : 0 < ε) : 1 = 1 := by
  Afirmación : ε ≥ 0 pues ε_pos
  rfl

example (ε : ℝ) (ε_pos : 0 < ε) : 1 = 1 := by
  Afirmación: ε ≥ 0 ya que ε > 0
  rfl

set_option linter.unusedVariables false

example (n : ℕ) : n + n + n = 3*n := by
  Afirmación: n + n = 2*n por
    ring
  ring

example (n : ℤ) (h : 0 < n) : True := by
  Afirmación: 0 < 2*n por
    linarith only [h]
  Afirmación: 0 < 2*n pues mul_pos aplicado a zero_lt_two ,e h
  trivial

lemma foo_ex : ∃ N : Nat, True := by simp

addAnonymousFactSplittingLemma foo_ex

example (A : ℝ) : True := by
  Obtenemos N : ℕ tal que True
  trivial
end
