import Verbose.Tactics.Lets

elab "Claim" name:ident ":" stmt:term : tactic => do
let _ ← claim name.getId stmt
pure ()

example : 1 = 1 := by
  Claim H : 1 = 1
  . rfl
  exact H

elab "Let's" "prove by induction" name:ident ":" stmt:term : tactic =>
letsInduct name.getId stmt

example (P : Nat → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : P 4 := by
  Let's prove by induction H : ∀ k, P k
  . exact h₀
  . exact h k hyp_rec
  . exact H 4
