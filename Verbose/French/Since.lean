import Verbose.Tactics.Since
import Verbose.French.Common
import Lean

namespace Verbose.French

open Lean Elab Tactic

elab ("Comme " <|> "Puisque ") facts:factsFR " on obtient " news:newObjectFR : tactic => do
  let newsT ← newObjectFRToTerm news
  let news_patt := newObjectFRToRCasesPatt news
  let factsT := factsFRToArray facts
  sinceObtainTac newsT news_patt factsT

elab ("Comme " <|> "Puisque ") facts:factsFR " on obtient " news:newFactsFR : tactic => do
  let newsT ← newFactsFRToTypeTerm news
  -- dbg_trace "newsT {newsT}"
  let news_patt := newFactsFRToRCasesPatt news
  let factsT := factsFRToArray facts
  -- dbg_trace "factsT {factsT}"
  sinceObtainTac newsT news_patt factsT

elab ("Comme " <|> "Puisque ") facts:factsFR " on conclut que " concl:term : tactic => do
  let factsT := factsFRToArray facts
  -- dbg_trace "factsT {factsT}"
  sinceConcludeTac concl factsT

elab ("Comme " <|> "Puisque ") fact:term " on choisit "  colGt news:newStuffFR : tactic => do
  let news := newStuffFRToArray news
  sinceChooseTac fact news

elab ("Comme " <|> "Puisque ") facts:factsFR " il suffit de montrer que " newGoals:factsFR : tactic => do
  let factsT := factsFRToArray facts
  let newGoalsT := factsFRToArray newGoals
  sinceSufficesTac factsT newGoalsT

elab "Il suffit de montrer que " newGoals:factsFR : tactic => do
  let newGoalsT := factsFRToArray newGoals
  sinceSufficesTac #[] newGoalsT

elab "On discute selon que " factL:term " ou " factR:term : tactic => do
  -- dbg_trace s!"factL {factL}"
  -- dbg_trace s!"factR {factR}"
  sinceDiscussTac factL factR

setLang fr

implement_endpoint (lang := fr) unusedFact (fact : String) : TacticM String :=
  pure s!"Il est inutile de savoir que {fact} ici."

set_option linter.unusedVariables false

example (f : ℝ → ℝ) (hf : ∀ x y, f x = f y → x = y) (x y : ℝ) (hxy : f x = f y) : x = y := by
  Comme ∀ x y, f x = f y → x = y et f x = f y on conclut que x = y

example (n : Nat) (h : ∃ k, n = 2*k) : True := by
  success_if_fail_with_msg "Le nom h est déjà utilisé."
    Comme ∃ k, n = 2*k on obtient k tel que h : n = 2*k
  Comme ∃ k, n = 2*k on obtient k tel que H : n = 2*k
  trivial

example (n N : Nat) (hn : n ≥ N) (h : ∀ n ≥ N, ∃ k, n = 2*k) : True := by
  success_if_fail_with_msg "Il est inutile de savoir que n ≥ n ici."
    Comme ∀ n ≥ N, ∃ k, n = 2*k, n ≥ N et n ≥ n on obtient k tel que H : n = 2*k
  Comme ∀ n ≥ N, ∃ k, n = 2*k et n ≥ N on obtient k tel que H : n = 2*k
  trivial

example (P Q : Prop) (h : P ∧ Q)  : Q := by
  Comme P ∧ Q on obtient (hP : P) et (hQ : Q)
  exact hQ

example (P Q R S : Prop) (h : P ↔ R) (h' : (Q → R) → S) : (Q → P) → S := by
  Comme P ↔ R et (Q → R) → S on conclut que (Q → P) → S

example (P Q R S : Prop) (h : P ↔ R) (h' : (Q → R) → S) : (Q → P) → S := by
  Comme R ↔ P et (Q → R) → S on conclut que (Q → P) → S

example (n : Nat) (P : Nat → Prop) (Q : ℕ → ℕ → Prop) (h : P n ∧ ∀ m, Q n m) : Q n n := by
  Comme P n ∧ ∀ m, Q n m on obtient (hQ : ∀ m, Q n m)
  apply hQ

example (n : ℕ) (hn : n > 2) (P : ℕ → Prop) (h : ∀ n ≥ 3, P n) : True := by
  Comme ∀ n ≥ 3, P n et n ≥ 3 on obtient H : P n
  trivial

example (n : ℕ) (hn : n > 2) (P Q : ℕ → Prop) (h : ∀ n ≥ 3, P n ∧ Q n) : True := by
  Comme ∀ n ≥ 3, P n ∧ Q n et n ≥ 3 on obtient H : P n et H' : Q n
  trivial

example (n : ℕ) (hn : n > 2) (P : ℕ → Prop) (h : ∀ n ≥ 3, P n) : P n := by
  Comme ∀ n ≥ 3, P n et n ≥ 3 on conclut que P n

example (n : ℕ) (hn : n > 2) (P Q : ℕ → Prop) (h : ∀ n ≥ 3, P n ∧ Q n) : P n := by
  Comme ∀ n ≥ 3, P n ∧ Q n et n ≥ 3 on conclut que P n

example (n : ℕ) (hn : n > 2) (P Q : ℕ → Prop) (h : ∀ n ≥ 3, P n ∧ Q n) : True := by
  Comme ∀ n ≥ 3, P n ∧ Q n et n ≥ 3 on obtient H : P n
  trivial

example (n : ℕ) (hn : n > 2) (P Q : ℕ → Prop) (h : ∀ n ≥ 3, P n) (h' : ∀ n ≥ 3, Q n) : True := by
  Comme ∀ n ≥ 3, P n, ∀ n ≥ 3, Q n et n ≥ 3 on obtient H : P n et H' : Q n
  trivial

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  Comme P → Q il suffit de montrer que P
  exact h'

example (P Q R : Prop) (h : P → R → Q) (hP : P) (hR : R) : Q := by
  Comme P → R → Q il suffit de montrer que P et R
  exact hP
  exact hR

-- Test bug Titouan
set_option linter.unusedTactic false in
example (P : ℝ → Prop) (h : ∀ x > 0, P x)  : P 1 := by
  Comme 1 > 0 et ∀ x > 0, P x on obtient h' : P 1
  guard_hyp_nums 3
  exact h'

-- Test bug Titouan
set_option linter.unusedTactic false in
example (P Q : ℝ → Prop) (h : ∀ x > 0, P x → Q x) (h' : P 1) : Q 1 := by
  Comme 1 > 0 et ∀ x > 0, P x → Q x il suffit de montrer que P 1
  guard_hyp_nums 5
  exact h'

example (P Q R S : Prop) (h : P → R → Q → S) (hP : P) (hR : R) (hQ : Q) : S := by
  Comme P → R → Q → S il suffit de montrer que P, R et Q
  exact hP
  exact hR
  exact hQ

example (P Q : Prop) (h : P ↔ Q) (hP : P) : Q := by
  Comme P ↔ Q  il suffit de montrer que P
  exact hP

example (P Q : Prop) (h : P ↔ Q) (hP : P) : Q ∧ True:= by
  constructor
  Comme P ↔ Q  il suffit de montrer que P
  exact hP
  trivial

example (P : ℕ → Prop) (x y : ℕ) (h : x = y) (h' : P x) : P y := by
  success_if_fail_with_msg "
La justification a échoué :
P : ℕ → Prop
x y : ℕ
GivenFact_0 : x = y
⊢ P y"
    Comme x = y on obtient H : P y
  Comme x = y et P x on obtient H : P y
  exact H

example (P : ℕ → Prop) (x y : ℕ) (h : x = y) (h' : P x) : P y := by
  Comme x = y et P x on conclut que P y

example (P : ℕ → Prop) (x y : ℕ) (h : x = y) (h' : P x) : P y := by
  Comme x = y  il suffit de montrer que P x
  exact h'

-- example (n : ℤ) : Even (n^2) → Even n := by
--   contrapose
--   have := @Int.not_even_iff_odd
--   Comme (¬ Even n ↔ Odd n) et (¬ Even (n^2) ↔ Odd (n^2)) il suffit de montrer que Odd n → Odd (n^2)
--   rintro ⟨k, rfl⟩
--   use 2*k*(k+1)
--   ring

example (ε : ℝ) (ε_pos : ε > 0) : ε ≥ 0 := by
  Comme ε > 0 on conclut que ε ≥ 0

configureAnonymousCaseSplittingLemmas le_or_gt lt_or_gt_of_ne lt_or_eq_of_le eq_or_lt_of_le Classical.em

example (P Q : Prop) (h : P ∨ Q) : True := by
  On discute selon que P ou Q
  all_goals tauto

example (P Q : Prop) (h : P ∨ Q) : True := by
  On discute selon que Q ou P
  all_goals tauto

example (P : Prop) : True := by
  On discute selon que P ou ¬ P
  all_goals tauto

example (x y : ℕ) : True := by
  On discute selon que x ≤ y ou x > y
  all_goals tauto

example (x y : ℕ) : True := by
  On discute selon que x = y ou x ≠ y
  all_goals tauto

example (x y : ℕ) (h : x ≠ y) : True := by
  On discute selon que x < y ou x > y
  all_goals tauto

example (ε : ℝ) (h : ε > 0) : ε ≥ 0 := by
  success_if_fail_with_msg "La justification a échoué :
ε : ℝ
SufficientFact_0 : ε < 0
⊢ ε ≥ 0"
    Il suffit de montrer que ε < 0
  Il suffit de montrer que ε > 0
  exact h

lemma le_le_of_max_le' {α : Type*} [LinearOrder α] {a b c : α} : max a b ≤ c → a ≤ c ∧ b ≤ c :=
max_le_iff.1

configureAnonymousFactSplittingLemmas le_max_left le_max_right le_le_of_max_le' le_of_max_le_left le_of_max_le_right

example (n a b : ℕ) (h : n ≥ max a b) : True := by
  Comme n ≥ max a b on obtient H : n ≥ a et H' : n ≥ b
  trivial

example (n a b : ℕ) (h : n ≥ max a b) : True := by
  Comme n ≥ max a b on obtient H : n ≥ a
  trivial

example (n a b : ℕ) (h : n ≥ max a b) (P : ℕ → Prop) (hP : ∀ n ≥ a, P n) : P n := by
  Comme ∀ n ≥ a, P n et n ≥ a on conclut que P n

set_option linter.unusedVariables false in
example (a b : ℕ) (P : ℕ → Prop) (h : ∀ n ≥ a, P n) : True := by
  Comme ∀ n ≥ a, P n et max a b ≥ a on obtient H : P (max a b)
  trivial

example (a b : ℝ) (h : a + b ≤ 3) (h' : b ≥ 0) : b*(a + b) ≤ b*3 := by
  success_if_fail_with_msg "
La justification a échoué :
a b : ℝ
GivenFact_0 : a + b ≤ 3
⊢ b * (a + b) ≤ b * 3"
    Comme a + b ≤ 3 on conclut que b*(a + b) ≤ b*3
  Comme a + b ≤ 3 et b ≥ 0 on conclut que b*(a + b) ≤ b*3

example (a b : ℝ) (hb : b = 2) : a + a*b = a + a*2 := by
  Comme b = 2 on conclut que a + a*b = a + a*2

example (P Q R S T : Prop) (hPR : P ↔ R) : ((Q → R) → S) ↔ ((Q → P) → S) := by
  -- simp only [hPR]
  Comme P ↔ R on conclut que ((Q → R) → S) ↔ ((Q → P) → S)

example (a k : ℤ) (h : a = 0*k) : a = 0 := by
  Comme a = 0*k on conclut que a = 0

local macro_rules | `($x ∣ $y)   => `(@Dvd.dvd ℤ Int.instDvd ($x : ℤ) ($y : ℤ))

example (a : ℤ) (h : a = 0) : a ∣ 0 := by
  success_if_fail_with_msg "
La justification a échoué :
a : ℤ
GivenFact_0 : a = 0
⊢ a ∣ 0"
    Comme a = 0 on conclut que a ∣ 0
  Comme a = 0 il suffit de montrer que 0 ∣ 0
  use 0
  rfl

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  Comme P et Q on conclut que P ∧ Q

example (P Q : Prop) (hPQ : P → Q) (hQP : Q → P) : P ↔ Q := by
  Comme P → Q et Q → P on conclut que P ↔ Q

example (P Q : Prop) (hPQ : P ↔ Q) : True := by
  Comme P ↔ Q on obtient h : P → Q et h' : Q → P
  trivial

private lemma test_abs_le_of_le_le {α : Type*} [LinearOrderedAddCommGroup α] {a b : α}
    (h : -b ≤ a) (h' : a ≤ b) : |a| ≤ b := abs_le.2 ⟨h, h'⟩

private lemma test_abs_le_of_le_le' {α : Type*} [LinearOrderedAddCommGroup α] {a b : α}
    (h' : a ≤ b) (h : -b ≤ a) : |a| ≤ b := abs_le.2 ⟨h, h'⟩

private lemma test_abs_le_of_le_and_le {α : Type*} [LinearOrderedAddCommGroup α] {a b : α}
    (h : -b ≤ a ∧ a ≤ b) : |a| ≤ b := abs_le.2 h

configureAnonymousGoalSplittingLemmas test_abs_le_of_le_le test_abs_le_of_le_le' test_abs_le_of_le_and_le

example (a b : ℝ) (h : a - b ≥ -1) (h' : a - b ≤ 1) : |a - b| ≤ 1 := by
  Comme (-1 ≤ a - b ∧ a - b ≤ 1) → |a - b| ≤ 1 il suffit de montrer que -1 ≤ a - b ∧ a - b ≤ 1
  exact ⟨h, h'⟩

example (a b : ℝ) (h : a - b ≥ -1) (h' : a - b ≤ 1) : |a - b| ≤ 1 := by
  Comme (-1 ≤ a - b ∧ a - b ≤ 1) → |a - b| ≤ 1 il suffit de montrer que -1 ≤ a - b et a - b ≤ 1
  all_goals assumption

example (a b : ℝ) (h : a - b ≥ -1) (h' : a - b ≤ 1) : |a - b| ≤ 1 := by
  Comme -1 ≤ a - b → a - b ≤ 1 → |a - b| ≤ 1 il suffit de montrer que -1 ≤ a - b et a - b ≤ 1
  all_goals assumption

example (u v : ℕ → ℝ) (h : ∀ n, u n ≤ v n) : u 0 - 2 ≤ v 0 - 2 := by
  Comme ∀ n, u n ≤ v n on conclut que u 0 - 2 ≤ v 0 - 2

example (P : Nat → Prop) (h : ∃ x, ¬ P x) : ¬ (∀ x, P x) := by
  Il suffit de montrer que ∃ x, ¬ P x
  exact h

example (P Q : Prop) (h : ¬ P ∨ Q) : P → Q := by
  Comme ¬ P ∨ Q on conclut que P → Q

example (P : Prop) (x : ℝ) (h : ¬ (P ∧ x < 0)) : P → x ≥ 0 := by
  Comme ¬ (P ∧ x < 0) on conclut que P → x ≥ 0

private def foo_bar (P : Nat → Prop) := ∀ x, P x
configureUnfoldableDefs foo_bar

example (P : Nat → Prop) (h : ∃ x, ¬ P x) : ¬ foo_bar P := by
  Il suffit de montrer que ∃ x, ¬ P x
  exact h

example (P : Nat → Prop) (h : ¬ foo_bar P) : ∃ x, ¬ P x := by
  Comme ¬ foo_bar P on obtient h' : ∃ x, ¬ P x
  exact h'

example (P : Nat → Prop) (h : ∃ x, ¬ P x) : ¬ (∀ x, P x) := by
  Comme ∃ x, ¬ P x on conclut que ¬ (∀ x, P x)

example (P : Nat → Prop) (h : ∃ x, ¬ P x) : True := by
  Comme ∃ x, ¬ P x on obtient H : ¬ (∀ x, P x)
  trivial

example (h : (2 : ℝ) * -42 = 2 * 42) : False := by
  -- Note: the following example doesn’t need backtracking because linarith
  -- finds a proof using h anyway
  Comme 2 * -42 = 2 * 42 on conclut que False

-- The next three examples test reelaborating numbers as reals after failure

example (P : ℝ → Prop) (h : ∀ ε > 0, P ε) : P 1 := by
  Comme ∀ ε > 0, P ε et 1 > 0 on obtient h' : P 1
  exact h'

example (P : ℝ → Prop) (h : ∀ ε > 0, P ε) : P 1 := by
  Comme ∀ ε > 0, P ε et 1 > 0 on conclut que P 1

example (P : ℝ → Prop) (h : ∀ ε > 0, P ε) : P 1 := by
  Comme ∀ ε > 0, P ε il suffit de montrer que 1 > 0
  norm_num

noncomputable example (f : ℕ → ℕ) (h : ∀ y, ∃ x, f x = y) : ℕ → ℕ := by
  Comme ∀ y, ∃ x, f x = y on choisit g tel que (H : ∀ (y : ℕ), f (g y) = y)
  exact g

noncomputable example (f : ℕ → ℕ) (A : Set ℕ) (h : ∀ y, ∃ x ∈ A, f x = y) : ℕ → ℕ := by
  Comme ∀ y, ∃ x ∈ A, f x = y on choisit g tel que (H : ∀ (y : ℕ), g y ∈ A) et (H' : ∀ (y : ℕ), f (g y) = y)
  exact g

noncomputable example (f : ℕ → ℕ) (A : Set ℕ) (h : ∀ y, ∃ x ∈ A, f x = y) : ℕ → ℕ := by
  Comme ∀ y, ∃ x ∈ A, f x = y on choisit g tel que (H : ∀ (y : ℕ), g y + 0 ∈ A) et (H' : ∀ (y : ℕ), f (g y) = y)
  exact g
