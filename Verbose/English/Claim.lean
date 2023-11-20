import Verbose.Tactics.Lets
import Verbose.English.Common

open Lean

macro ("Fact" <|> "Claim") name:ident ":" stmt:term "by" colGt prf:tacticSeq: tactic => `(tactic|have $name : $stmt := by $prf)

open Lean Elab Tactic

elab ("Fact" <|> "Claim") name:ident ":" stmt:term "from" prf:maybeApplied : tactic => do
  let prfTerm ← maybeAppliedToTerm prf
  evalTactic (← `(tactic|have $name : $stmt := by exact $prfTerm))

example : 1 = 1 := by
  Claim H : 1 = 1 by
    rfl
  exact H

set_option linter.unusedVariables false

example (n : ℕ) : n + n + n = 3*n := by
  Fact key : n + n = 2*n by
    ring
  ring

example (n : ℤ) (h : 0 < n) : True := by
  Fact key : 0 < 2*n by
    linarith only [h]
  Fact keybis : 0 < 2*n from mul_pos applied to [zero_lt_two, h]
  trivial
