import Verbose.Tactics.Lets
import Verbose.English.Common
import Verbose.English.We

open Lean Verbose.English

macro ("Fact" <|> "Claim") name:ident ":" stmt:term "by" colGt prf:tacticSeq: tactic => `(tactic|have $name : $stmt := by $prf)

open Lean Elab Tactic

elab ("Fact" <|> "Claim") name:ident ":" stmt:term "from" prf:maybeApplied : tactic => do
  evalTactic (← `(tactic|have $name : $stmt := by We conclude by $prf))

elab ("Fact" <|> "Claim") name:ident ":" stmt:term "by computation" : tactic => do
  evalTactic (← `(tactic|have $name : $stmt := by We compute))

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
