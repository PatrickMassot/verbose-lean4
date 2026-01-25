import Verbose.Tactics.Since
import Verbose.English.Common
import Lean

namespace Verbose.English

open Lean Elab Tactic

elab "Since " facts:facts " we get " news:newObjectNameLess : tactic => do
  let newsT ← newObjectNameLessToTerm news
  let news_patt := newObjectNameLessToRCasesPatt news
  let factsT := factsToArray facts
  sinceObtainTac newsT news_patt factsT

open RCases in
elab "Since " facts:facts " we get that " news:facts : tactic =>
  withMainContext do
  let ctx ← getLCtx
  let newsT ← factsToTypeTerm news
  let mut patts : Array RCasesPatt := #[]
  let mut added_names : Array Name := #[]
  for t in factsToArray news do
    let e ← elabTerm t none
    let mut n := ctx.getUnusedName (← mk_hyp_name t e)
    while n ∈ added_names do
      n := .mkSimple (toString n ++ "'")
    added_names := added_names.push n
    patts := patts.push <| RCasesPatt.typed t (RCasesPatt.one Syntax.missing  n) t
  let patt := if patts.size > 1 then
      .tuple default patts.toList
    else patts[0]!
  let factsT := factsToArray facts
  sinceObtainTac newsT patt factsT

elab "Since " facts:facts " we conclude that " concl:term : tactic => do
  let factsT := factsToArray facts
  -- dbg_trace "factsT {factsT}"
  sinceConcludeTac concl factsT

elab "Since " fact:term " we choose "  colGt news:newObjectNameLess : tactic => do
  let news := newObjectNameLessToArray news
  sinceChooseTac fact news

elab "Since " facts:facts " it suffices to prove that " newGoals:facts : tactic => do
  let factsT := factsToArray facts
  let newGoalsT := factsToArray newGoals
  sinceSufficesTac factsT newGoalsT

elab "It suffices to prove that " newGoals:facts : tactic => do
  let newGoalsT := factsToArray newGoals
  sinceSufficesTac #[] newGoalsT

elab "We discuss depending on whether " factL:term " or " factR:term : tactic => do
  -- dbg_trace s!"factL {factL}"
  -- dbg_trace s!"factR {factR}"
  sinceDiscussTac factL factR

implement_endpoint (lang := en) unusedFact (fact : String) : TacticM String :=
  pure s!"We do not need that {fact} here."

set_option linter.unusedVariables false

example (f : ℝ → ℝ) (hf : ∀ x y, f x = f y → x = y) (x y : ℝ) (hxy : f x = f y) : x = y := by
  Since ∀ x y, f x = f y → x = y and f x = f y we conclude that x = y

example (n : Nat) (h : ∃ k, n = 2*k) : True := by
  Since ∃ k, n = 2*k we get k such that n = 2*k
  trivial

example (n : Nat) (h : ∃ k ≥ 1, n = 2*k) : True := by
  Since ∃ k ≥ 1, n = 2*k we get k such that k ≥ 1 and n = 2*k
  trivial

example (n : Nat) (h : ∃ k ≥ 1, n = 2*k ∧ k ≠ 0) : True := by
  Since ∃ k ≥ 1, n = 2*k ∧ k ≠ 0 we get k such that k ≥ 1, n = 2*k and k ≠ 0
  trivial

example (n : Nat) (h : ∃ (k l : Nat), n = k + l) : True := by
  Since ∃ (k l : Nat), n = k + l we get k and l such that n = k + l
  trivial

example (n : Nat) (h : ∃ (k l : Nat), n = k + l ∧ k = 1) : True := by
  Since ∃ (k l : Nat), n = k + l ∧ k = 1 we get k and l such that n = k + l and k = 1
  trivial

example (n : Nat) (h : ∃ (k l : Nat), n = k + l ∧ k = 1 ∧ l = 2) : True := by
  Since ∃ (k l : Nat), n = k + l ∧ k = 1 ∧ l = 2 we get k and l such that n = k + l, k = 1
    and l = 2
  trivial

example (n N : Nat) (hn : n ≥ N) (h : ∀ n ≥ N, ∃ k, n = 2*k) : True := by
  success_if_fail_with_msg "We do not need that n ≥ n here."
    Since ∀ n ≥ N, ∃ k, n = 2*k, n ≥ N and n ≥ n we get k such that n = 2*k
  Since ∀ n ≥ N, ∃ k, n = 2*k and n ≥ N we get k such that n = 2*k
  trivial

example (P Q : Prop) (h : P ∧ Q)  : Q := by
  Since P ∧ Q we get that P and Q
  exact hQ

example (P Q R S : Prop) (h : P ↔ R) (h' : (Q → R) → S) : (Q → P) → S := by
  Since P ↔ R and (Q → R) → S we conclude that (Q → P) → S

example (P Q R S : Prop) (h : P ↔ R) (h' : (Q → R) → S) : (Q → P) → S := by
  Since R ↔ P and (Q → R) → S we conclude that (Q → P) → S

example (n : Nat) (P : Nat → Prop) (Q : ℕ → ℕ → Prop) (h : P n ∧ ∀ m, Q n m) : Q n n := by
  Since P n ∧ ∀ m, Q n m we get that ∀ m, Q n m
  apply hQn

example (n : ℕ) (hn : n > 2) (P : ℕ → Prop) (h : ∀ n ≥ 3, P n) : True := by
  Since ∀ n ≥ 3, P n and n ≥ 3 we get that P n
  trivial

example (n : ℕ) (hn : n > 2) (P Q : ℕ → Prop) (h : ∀ n ≥ 3, P n ∧ Q n) : True := by
  Since ∀ n ≥ 3, P n ∧ Q n and n ≥ 3 we get that P n and Q n
  trivial

example (n : ℕ) (hn : n > 2) (P : ℕ → Prop) (h : ∀ n ≥ 3, P n) : P n := by
  Since ∀ n ≥ 3, P n and n ≥ 3 we conclude that P n

example (n : ℕ) (hn : n > 2) (P Q : ℕ → Prop) (h : ∀ n ≥ 3, P n ∧ Q n) : P n := by
  Since ∀ n ≥ 3, P n ∧ Q n and n ≥ 3 we conclude that P n

example (n : ℕ) (hn : n > 2) (P Q : ℕ → Prop) (h : ∀ n ≥ 3, P n ∧ Q n) : True := by
  Since ∀ n ≥ 3, P n ∧ Q n and n ≥ 3 we get that P n
  trivial

example (n : ℕ) (hn : n > 2) (P Q : ℕ → Prop) (h : ∀ n ≥ 3, P n) (h' : ∀ n ≥ 3, Q n) : True := by
  Since ∀ n ≥ 3, P n, ∀ n ≥ 3, Q n and n ≥ 3 we get that P n and Q n
  trivial

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  Since P → Q it suffices to prove that P
  exact h'

example (P Q R : Prop) (h : P → R → Q) (hP : P) (hR : R) : Q := by
  Since P → R → Q it suffices to prove that P and R
  exact hP
  exact hR

set_option linter.unusedTactic false in
example (P : ℝ → Prop) (h : ∀ x > 0, P x)  : P 1 := by
  Since 1 > 0 and ∀ x > 0, P x we get that P 1
  guard_hyp_nums 3
  exact hP

set_option linter.unusedTactic false in
example (P Q : ℝ → Prop) (h : ∀ x > 0, P x → Q x) (h' : P 1) : Q 1 := by
  Since 1 > 0 and ∀ x > 0, P x → Q x it suffices to prove that P 1
  guard_hyp_nums 5
  exact h'

example (P Q R S : Prop) (h : P → R → Q → S) (hP : P) (hR : R) (hQ : Q) : S := by
  Since P → R → Q → S it suffices to prove that P, R and Q
  exact hP
  exact hR
  exact hQ

example (P Q : Prop) (h : P ↔ Q) (hP : P) : Q := by
  Since P ↔ Q it suffices to prove that P
  exact hP

example (P Q : Prop) (h : P ↔ Q) (hP : P) : Q ∧ True:= by
  constructor
  Since P ↔ Q it suffices to prove that P
  exact hP
  trivial

example (P : ℕ → Prop) (x y : ℕ) (h : x = y) (h' : P x) : P y := by
  success_if_fail_with_msg "
Could not prove:
P : ℕ → Prop
x y : ℕ
GivenFact_0 : x = y
⊢ P y"
    Since x = y we get that P y
  Since x = y and P x we get that P y
  exact hPy

example (P : ℕ → Prop) (x y : ℕ) (h : x = y) (h' : P x) : P y := by
  Since x = y and P x we conclude that P y

example (P : ℕ → Prop) (x y : ℕ) (h : x = y) (h' : P x) : P y := by
  Since x = y it suffices to prove that P x
  exact h'

-- example (n : ℤ) : Even (n^2) → Even n := by
--   contrapose
--   have := @Int.not_even_iff_odd
--   Since (¬ Even n ↔ Odd n) and (¬ Even (n^2) ↔ Odd (n^2)) it suffices to prove that Odd n → Odd (n^2)
--   rintro ⟨k, rfl⟩
--   use 2*k*(k+1)
--   ring

example (ε : ℝ) (ε_pos : ε > 0) : ε ≥ 0 := by
  Since ε > 0 we conclude that ε ≥ 0

example (f : ℕ → ℕ) (x y : ℕ) (h : x = y) : f x ≤ f y := by
  Since x = y we conclude that f x ≤ f y

configureAnonymousCaseSplittingLemmas le_or_gt lt_or_gt_of_ne lt_or_eq_of_le eq_or_lt_of_le Classical.em

example (P Q : Prop) (h : P ∨ Q) : True := by
  We discuss depending on whether P or Q
  all_goals tauto

example (P Q : Prop) (h : P ∨ Q) : True := by
  We discuss depending on whether Q or P
  all_goals tauto

example (P : Prop) : True := by
  We discuss depending on whether P or ¬ P
  all_goals tauto

example (x y : ℕ) : True := by
  We discuss depending on whether x ≤ y or x > y
  all_goals tauto

example (x y : ℕ) : True := by
  We discuss depending on whether x = y or x ≠ y
  all_goals tauto

example (x y : ℕ) (h : x ≠ y) : True := by
  We discuss depending on whether x < y or x > y
  all_goals tauto

example (ε : ℝ) (h : ε > 0) : ε ≥ 0 := by
  success_if_fail_with_msg "Could not prove:
ε : ℝ
SufficientFact_0 : ε < 0
⊢ ε ≥ 0"
    It suffices to prove that ε < 0
  It suffices to prove that ε > 0
  exact h

lemma le_le_of_max_le' {α : Type*} [LinearOrder α] {a b c : α} : max a b ≤ c → a ≤ c ∧ b ≤ c :=
max_le_iff.1

configureAnonymousFactSplittingLemmas le_max_left le_max_right le_le_of_max_le' le_of_max_le_left le_of_max_le_right

example (n a b : ℕ) (h : n ≥ max a b) : True := by
  Since n ≥ max a b we get that n ≥ a and n ≥ b
  trivial

example (n a b : ℕ) (h : n ≥ max a b) : True := by
  Since n ≥ max a b we get that n ≥ a
  trivial

example (n a b : ℕ) (h : n ≥ max a b) (P : ℕ → Prop) (hP : ∀ n ≥ a, P n) : P n := by
  Since ∀ n ≥ a, P n and n ≥ a we conclude that P n

set_option linter.unusedVariables false in
example (a b : ℕ) (P : ℕ → Prop) (h : ∀ n ≥ a, P n) : True := by
  Since ∀ n ≥ a, P n and max a b ≥ a we get that P (max a b)
  trivial

example (a b : ℝ) (h : a + b ≤ 3) (h' : b ≥ 0) : b*(a + b) ≤ b*3 := by
  success_if_fail_with_msg "
Could not prove:
a b : ℝ
GivenFact_0 : a + b ≤ 3
⊢ b * (a + b) ≤ b * 3"
    Since a + b ≤ 3 we conclude that b*(a + b) ≤ b*3
  Since a + b ≤ 3 and b ≥ 0 we conclude that b*(a + b) ≤ b*3

example (a b : ℝ) (hb : b = 2) : a + a*b = a + a*2 := by
  Since b = 2 we conclude that a + a*b = a + a*2

example (P Q R S T : Prop) (hPR : P ↔ R) : ((Q → R) → S) ↔ ((Q → P) → S) := by
  -- simp only [hPR]
  Since P ↔ R we conclude that ((Q → R) → S) ↔ ((Q → P) → S)

example (a k : ℤ) (h : a = 0*k) : a = 0 := by
  Since a = 0*k we conclude that a = 0

local macro_rules | `($x ∣ $y)   => `(@Dvd.dvd ℤ Int.instDvd ($x : ℤ) ($y : ℤ))

example (a : ℤ) (h : a = 0) : a ∣ 0 := by
  success_if_fail_with_msg "
Could not prove:
a : ℤ
GivenFact_0 : a = 0
⊢ a ∣ 0"
    Since a = 0 we conclude that a ∣ 0
  Since a = 0 it suffices to prove that 0 ∣ 0
  use 0
  rfl

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  Since P and Q we conclude that P ∧ Q

example (P Q : Prop) (hPQ : P → Q) (hQP : Q → P) : P ↔ Q := by
  Since P → Q and Q → P we conclude that P ↔ Q

example (P Q : Prop) (hPQ : P ↔ Q) : True := by
  Since P ↔ Q we get that P → Q and Q → P
  trivial

private lemma test_abs_le_of_le_le {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] {a b : α}
    (h : -b ≤ a) (h' : a ≤ b) : |a| ≤ b := abs_le.2 ⟨h, h'⟩

private lemma test_abs_le_of_le_le' {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] {a b : α}
    (h' : a ≤ b) (h : -b ≤ a) : |a| ≤ b := abs_le.2 ⟨h, h'⟩

private lemma test_abs_le_of_le_and_le {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] {a b : α}
    (h : -b ≤ a ∧ a ≤ b) : |a| ≤ b := abs_le.2 h

configureAnonymousGoalSplittingLemmas test_abs_le_of_le_le test_abs_le_of_le_le' test_abs_le_of_le_and_le

example (a b : ℝ) (h : a - b ≥ -1) (h' : a - b ≤ 1) : |a - b| ≤ 1 := by
  Since (-1 ≤ a - b ∧ a - b ≤ 1) → |a - b| ≤ 1 it suffices to prove that -1 ≤ a - b ∧ a - b ≤ 1
  exact ⟨h, h'⟩

example (a b : ℝ) (h : a - b ≥ -1) (h' : a - b ≤ 1) : |a - b| ≤ 1 := by
  Since (-1 ≤ a - b ∧ a - b ≤ 1) → |a - b| ≤ 1 it suffices to prove that -1 ≤ a - b and a - b ≤ 1
  all_goals assumption

example (a b : ℝ) (h : a - b ≥ -1) (h' : a - b ≤ 1) : |a - b| ≤ 1 := by
  Since -1 ≤ a - b → a - b ≤ 1 → |a - b| ≤ 1 it suffices to prove that -1 ≤ a - b and a - b ≤ 1
  all_goals assumption

example (u v : ℕ → ℝ) (h : ∀ n, u n ≤ v n) : u 0 - 2 ≤ v 0 - 2 := by
  Since ∀ n, u n ≤ v n we conclude that u 0 - 2 ≤ v 0 - 2

example (P : Nat → Prop) (h : ∃ x, ¬ P x) : ¬ (∀ x, P x) := by
  It suffices to prove that ∃ x, ¬ P x
  exact h

example (P Q : Prop) (h : ¬ P ∨ Q) : P → Q := by
  Since ¬ P ∨ Q we conclude that P → Q

example (P : Prop) (x : ℝ) (h : ¬ (P ∧ x < 0)) : P → x ≥ 0 := by
  Since ¬ (P ∧ x < 0) we conclude that P → x ≥ 0

private def foo_bar (P : Nat → Prop) := ∀ x, P x
configureUnfoldableDefs foo_bar

example (P : Nat → Prop) (h : ∃ x, ¬ P x) : ¬ foo_bar P := by
  It suffices to prove that ∃ x, ¬ P x
  exact h

example (P : Nat → Prop) (h : ¬ foo_bar P) : ∃ x, ¬ P x := by
  Since ¬ foo_bar P we get that ∃ x, ¬ P x
  exact hP

example (P : Nat → Prop) (h : ∃ x, ¬ P x) : ¬ (∀ x, P x) := by
  Since ∃ x, ¬ P x we conclude that ¬ (∀ x, P x)

example (P : Nat → Prop) (h : ∃ x, ¬ P x) : True := by
  Since ∃ x, ¬ P x we get that ¬ (∀ x, P x)
  trivial

example (h : (2 : ℝ) * -42 = 2 * 42) : False := by
  -- Note: the following example doesn’t need backtracking because linarith
  -- finds a proof using h anyway
  Since 2 * -42 = 2 * 42 we conclude that False

-- The next three examples test reelaborating numbers as reals after failure

example (P : ℝ → Prop) (h : ∀ ε > 0, P ε) : P 1 := by
  Since ∀ ε > 0, P ε and 1 > 0 we get that P 1
  exact hP

example (P : ℝ → Prop) (h : ∀ ε > 0, P ε) : P 1 := by
  Since ∀ ε > 0, P ε and 1 > 0 we conclude that P 1

example (P : ℝ → Prop) (h : ∀ ε > 0, P ε) : P 1 := by
  Since ∀ ε > 0, P ε it suffices to prove that 1 > 0
  norm_num

example (l : ℝ) (N : ℕ) (h : |(-1)^(2*N) - l| ≤ 1/2) : True := by
  Since |(-1)^(2*N) - l| ≤ 1/2 and (-1)^(2*N) = (1 : ℝ) we get that |1 - l| ≤ 1/2
  trivial

noncomputable section
example (f : ℕ → ℕ) (h : ∀ y, ∃ x, f x = y) : ℕ → ℕ := by
  Since ∀ y, ∃ x, f x = y we choose g such that ∀ (y : ℕ), f (g y) = y
  exact g

example (f : ℕ → ℕ) (A : Set ℕ) (h : ∀ y, ∃ x ∈ A, f x = y) : ℕ → ℕ := by
  Since ∀ y, ∃ x ∈ A, f x = y we choose g such that ∀ (y : ℕ), g y ∈ A and ∀ (y : ℕ), f (g y) = y
  exact g

example (f : ℕ → ℕ) (A : Set ℕ) (h : ∀ y, ∃ x ∈ A, f x = y) : ℕ → ℕ := by
  Since ∀ y, ∃ x ∈ A, f x = y we choose g such that ∀ (y : ℕ), g y + 0 ∈ A and ∀ (y : ℕ), f (g y) = y
  exact g

end

addAnonymousFactSplittingLemma lt_of_lt_of_le

example (ε : ℝ) (ε_pos : 1/ε > 0) (N : ℕ) (hN : N ≥ 1 / ε) : N > 0 := by
  Since N ≥ 1/ε and 1/ε > 0 we get that N > 0
  Since N ≥ 1/ε and 1/ε > 0 we conclude that N > 0
