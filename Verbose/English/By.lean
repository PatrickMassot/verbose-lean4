import Verbose.Tactics.By
import Verbose.English.Common

open Lean Verbose.English


elab "By " e:maybeApplied " we get " colGt news:newStuff : tactic => do
obtainTac (← maybeAppliedToTerm e) (newStuffToArray news)

elab "By " e:maybeApplied " we choose " colGt news:newStuff : tactic => do
chooseTac (← maybeAppliedToTerm e) (newStuffToArray news)

elab "By " e:maybeApplied " it suffices to prove " "that "? colGt arg:term : tactic => do
bySufficesTac (← maybeAppliedToTerm e) #[arg]

elab "By " e:maybeApplied " it suffices to prove " "that "? colGt args:sepBy(term, " and ") : tactic => do
bySufficesTac (← maybeAppliedToTerm e) args.getElems

elab "assumption'" : tactic => assumption'

macro "assumption" : term => `(by assumption')

lemma le_le_of_abs_le {α : Type*} [LinearOrderedAddCommGroup α] {a b : α} : |a| ≤ b → -b ≤ a ∧ a ≤ b := abs_le.1

lemma le_le_of_max_le {α : Type*} [LinearOrder α] {a b c : α} : max a b ≤ c → a ≤ c ∧ b ≤ c :=
max_le_iff.1

implement_endpoint (lang := en) cannotGet : CoreM String := pure "Cannot get this."

implement_endpoint (lang := en) theName : CoreM String := pure "The name"

implement_endpoint (lang := en) needName : CoreM String :=
pure "You need to provide a name for the chosen object."

implement_endpoint (lang := en) wrongNbGoals : CoreM String :=
pure s!"There are not so many claims to check."

implement_endpoint (lang := en) doesNotApply (fact : Format) : CoreM String :=
pure s!"Cannot apply {fact}."

implement_endpoint (lang := en) couldNotInferImplVal (val : Name) : CoreM String :=
pure s!"Could not infer implicit value for {val}."

implement_endpoint (lang := en) alsoNeedCheck (fact : Format) : CoreM String :=
pure s!"You also need to check {fact}"

configureAnonymousFactSplittingLemmas le_le_of_abs_le le_le_of_max_le

example (P : Nat → Prop) (h : ∀ n, P n) : P 0 := by
  By h applied to 0 we get h₀
  exact h₀

example (P : Nat → Nat → Prop) (h : ∀ n k, P n (k+1)) : P 0 1 := by
  By h applied to 0 and 0 we get (h₀ : P 0 1)
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

example (x : ℝ) (h : |x| ≤ 3) : True := by
  By h we get (h₁ : -3 ≤ x) (h₂ : x ≤ 3)
  trivial

example (n p q : ℕ) (h : n ≥ max p q) : True := by
  By h we get (h₁ : n ≥ p) (h₂ : n ≥ q)
  trivial

noncomputable example (f : ℕ → ℕ) (h : ∀ y, ∃ x, f x = y) : ℕ → ℕ := by
  By h we choose g such that (H : ∀ (y : ℕ), f (g y) = y)
  exact g

noncomputable example (f : ℕ → ℕ) (A : Set ℕ) (h : ∀ y, ∃ x ∈ A, f x = y) : ℕ → ℕ := by
  By h we choose g such that (H : ∀ (y : ℕ), g y ∈ A) and (H' : ∀ (y : ℕ), f (g y) = y)
  exact g

noncomputable example (f : ℕ → ℕ) (A : Set ℕ) (h : ∀ y, ∃ x ∈ A, f x = y) : ℕ → ℕ := by
  By h we choose g such that (H : ∀ (y : ℕ), g y + 0 ∈ A) and (H' : ∀ (y : ℕ), f (g y) = y)
  exact g

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  By h it suffices to prove that P
  exact h'

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  By h it suffices to prove P
  exact h'

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  By h it suffices to prove P
  exact assumption

example (P Q R : Prop) (h : P → R → Q) (hP : P) (hR : R) : Q := by
  By h it suffices to prove P and R
  exact hP
  exact hR

set_option linter.unusedVariables false in
example (P Q : Prop) (h : ∀ n : ℕ, P → Q) (h' : P) : Q := by
  success_if_fail_with_msg "Cannot apply h 0 1."
    By h applied to 0 and 1 it suffices to prove P
  By h applied to 0 it suffices to prove P
  exact h'

example (Q : Prop) (h : ∀ n : ℤ, n > 0 → Q)  : Q := by
  By h applied to 1 it suffices to prove 1 > 0
  norm_num

example (Q : Prop) (h : ∀ n : ℤ, n > 0 → Q)  : Q := by
  By h it suffices to prove 1 > 0
  norm_num

example {P Q R : ℕ → Prop} {n k l : ℕ} (h : ∀ k l, P k → Q l → R n) (hk : P k) (hl : Q l) :
    R n := by
  success_if_fail_with_msg "You also need to check Q ?l"
    By h it suffices to prove P k
  By h it suffices to prove P k and Q l
  exact hk
  exact hl

set_option linter.unusedVariables false in
example (n : Nat) (h : ∃ n : Nat, n = n) : True := by
  success_if_fail_with_msg "The name n is already used"
    By h we get n such that H
  trivial
