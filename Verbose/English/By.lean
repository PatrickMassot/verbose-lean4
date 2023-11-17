import Verbose.Tactics.By
import Verbose.English.Common

elab "By " e:maybeApplied " we get " colGt news:newStuff : tactic => do
obtainTac (← maybeAppliedToTerm e) (newStuffToArray news)

elab "By " e:maybeApplied " we choose " colGt news:newStuff : tactic => do
chooseTac (← maybeAppliedToTerm e) (newStuffToArray news)

elab "By " e:maybeApplied " it suffices to prove " "that "? colGt arg:term : tactic => do
bySufficesTac (← maybeAppliedToTerm e) #[arg]

elab "By " e:maybeApplied " it suffices to prove " "that "? colGt "["args:term,*"]" : tactic => do
bySufficesTac (← maybeAppliedToTerm e) args.getElems


example (P : Nat → Prop) (h : ∀ n, P n) : P 0 := by
  By h applied to 0 we get h₀
  exact h₀

example (P : Nat → Nat → Prop) (h : ∀ n k, P n (k+1)) : P 0 1 := by
  --rcases h 0 0 with (h₀ : P 0 0)
  By h applied to [0, 0] we get (h₀ : P 0 1)
  exact h₀

example (n : Nat) (h : ∃ k, n = 2*k) : True := by
  By h we get k such that (H : n = 2*k)
  trivial

example (n : Nat) (h : ∃ k, n = 2*k) : True := by
  By h we get k such that H
  trivial

example (P Q : Prop) (h : P ∧ Q)  : Q := by
  By h we get (hP : P) (hQ : Q)
  exact hQ

noncomputable example (f : ℕ → ℕ) (h : ∀ y, ∃ x, f x = y) : ℕ → ℕ := by
  By h we choose g such that (H : ∀ (y : ℕ), f (g y) = y)
  exact g


example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  By h it suffices to prove that P
  exact h'

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  By h it suffices to prove P
  exact h'

example (P Q R : Prop) (h : P → R → Q) (hP : P) (hR : R) : Q := by
  By h it suffices to prove [P, R]
  exact hP
  exact hR

/-
example (P Q : Prop) (h : ∀ n : ℕ, P → Q) (h' : P) : Q := by
  success_if_fail_with_msg "Apply this leads to 0 goals, not 1."
    By h applied to [0, 1] it suffices to prove P
  By h applied to 0 it suffices to prove P
  exact h'
 -/

example (Q : Prop) (h : ∀ n : ℤ, n > 0 → Q)  : Q := by
  By h applied to 1 it suffices to prove 1 > 0
  norm_num
