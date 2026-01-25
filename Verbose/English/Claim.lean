import Verbose.Tactics.Claim
import Verbose.English.Common
import Verbose.English.We
import Verbose.English.Since

open Lean Verbose.English

namespace Verbose.Named
scoped macro ("Fact" <|> "Claim") name:ident ":" stmt:term "by" colGt prf:tacticSeq: tactic =>
 withRef name  `(tactic|(checkName $name; have $name : $stmt := by $prf))

open Lean Elab Tactic

scoped macro ("Fact" <|> "Claim") name:ident ":" stmt:term "from" prf:maybeApplied : tactic => do
 withRef name  `(tactic|(checkName $name; have $name : $stmt := by We conclude by $prf))

scoped macro ("Fact" <|> "Claim") name:ident ":" stmt:term "by computation" : tactic => do
 withRef name  `(tactic|(checkName $name; have $name : $stmt := by We compute))

scoped macro ("Fact" <|> "Claim") name:ident ":" stmt:term "since" facts:facts : tactic =>
 withRef name  `(tactic|(checkName $name; have $name : $stmt := by Since $facts we conclude that $stmt))
end Verbose.Named

namespace Verbose.NameLess
open Lean Elab Tactic

scoped elab ("Fact" <|> "Claim") ":" stmt:term "by" colGt prf:tacticSeq : tactic =>
  mkClaim stmt fun name ↦ `(tactic|have $name : $stmt := by $prf)

scoped elab "We " ("observe" <|> "obtain") " that " stmt:term : tactic =>
  mkClaim stmt fun name ↦ `(tactic|have $name : $stmt := by strongAssumption)


scoped elab ("Fact" <|> "Claim") " : " stmt:term "from" prf:maybeApplied : tactic =>
  mkClaim stmt fun name ↦ `(tactic|have $name : $stmt := by We conclude by $prf)

scoped elab ("Fact" <|> "Claim") " : " stmt:term "by computation" : tactic =>
  mkClaim stmt fun name ↦ `(tactic|have $name : $stmt := by We compute)

scoped elab ("Fact" <|> "Claim") " : " stmt:term "since" facts:facts : tactic =>
  mkClaim stmt fun name ↦ `(tactic|have $name : $stmt := by Since $facts we conclude that $stmt)

end Verbose.NameLess

section
open Verbose.Named
example : 1 = 1 := by
  Claim H : 1 = 1 by
    rfl
  exact H

example : 1 + 1 = 2 := by
  Fact H : 1 + 1 = 2 by computation
  exact H

example (ε : ℝ) (ε_pos : 0 < ε) : 1 = 1 := by
  Claim H : ε ≥ 0 from ε_pos
  rfl

example (ε : ℝ) (ε_pos : 0 < ε) : 1 = 1 := by
  Fact H : ε ≥ 0 since ε > 0
  rfl

set_option linter.unusedVariables false

example (n : ℕ) : n + n + n = 3*n := by
  Fact key : n + n = 2*n by
    ring
  ring

example (n : ℤ) (h : 0 < n) : True := by
  Fact key : 0 < 2*n by
    linarith only [h]
  Fact keybis : 0 < 2*n from mul_pos applied to zero_lt_two and h
  trivial
end

section
open Verbose.NameLess
example : 1 = 1 := by
  Claim: 1 = 1 by
    rfl
  exact h

example : 1 + 1 = 2 := by
  Fact: 1 + 1 = 2 by computation
  exact h

example (ε : ℝ) (ε_pos : 0 < ε) : 1 = 1 := by
  Claim: ε ≥ 0 from ε_pos
  rfl

example (ε : ℝ) (ε_pos : 0 < ε) : 1 = 1 := by
  Fact: ε ≥ 0 since ε > 0
  rfl

set_option linter.unusedVariables false

example (n : ℕ) : n + n + n = 3*n := by
  Fact: n + n = 2*n by
    ring
  ring

example (n : ℤ) (h : 0 < n) : True := by
  Fact: 0 < 2*n by
    linarith only [h]
  Fact: 0 < 2*n from mul_pos applied to zero_lt_two and h
  trivial

end
