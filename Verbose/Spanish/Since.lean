import Verbose.Tactics.Since
import Verbose.Spanish.Common
import Lean

namespace Verbose.Spanish

open Lean Elab Tactic

elab "Como " facts:factsES " se tiene " news:newObjectNameLessES : tactic => do
  let newsT ← newObjectNameLessESToTerm news
  let news_patt := newObjectNameLessESToRCasesPatt news
  let factsT := factsESToArray facts
  sinceObtainTac newsT news_patt factsT

declare_syntax_cat thenConcludeES
syntax " finalmente concluimos que " term : thenConcludeES

def thenConcludeEStoTerm : TSyntax `thenConcludeES → Term
| `(thenConcludeES|finalmente concluimos que $t:term) => t
| _ => default

elab "Como " facts:factsES (" se tiene " <|> "tenemos que") news:sepBy1(factsES, " luego ") concl?:(thenConcludeES)? : tactic =>
  withMainContext do
  let newsArr := news.getElems
  let factsTArr := (#[facts] ++ newsArr).map factsESToArray
  let newsTArr ← liftM <| (#[facts] ++ newsArr).mapM factsESToTypeTerm
  let conclT? := if let some x := concl? then some (thenConcludeEStoTerm x) else none
  multipleSinceObtainTac factsTArr newsTArr conclT?

elab "Como " facts:factsES " concluimos que " concl:term : tactic => do
  let factsT := factsESToArray facts
  -- dbg_trace "factsT {factsT}"
  sinceConcludeTac concl factsT

elab "Como " fact:term " elegimos "  colGt news:newObjectNameLessES : tactic => do
  let news := newObjectNameLessESToArray news
  sinceChooseTac fact news

elab "Como " facts:factsES " basta probar que " newGoals:factsES : tactic => do
  let factsT := factsESToArray facts
  let newGoalsT := factsESToArray newGoals
  sinceSufficesTac factsT newGoalsT

elab "basta probar que " newGoals:factsES : tactic => do
  let newGoalsT := factsESToArray newGoals
  sinceSufficesTac #[] newGoalsT

elab "Decidimos en función de si " factL:term " o " factR:term : tactic => do
  -- dbg_trace s!"factL {factL}"
  -- dbg_trace s!"factR {factR}"
  sinceDiscussTac factL factR

implement_endpoint (lang:=es) unusedFact (fact : String) : TacticM String :=
  pure s!"Aquí {fact} no es necesario."

set_option linter.unusedVariables false

setLang es

example (f : ℝ → ℝ) (hf : ∀ x y, f x = f y → x = y) (x y : ℝ) (hxy : f x = f y) : x = y := by
  Como ∀ x y, f x = f y → x = y yy f x = f y concluimos que x = y

example (n : Nat) (h : ∃ k, n = 2*k) : True := by
  Como ∃ k, n = 2*k se tiene k tal que n = 2*k
  trivial

example (n : Nat) (h : ∃ k ≥ 1, n = 2*k) : True := by
  Como ∃ k ≥ 1, n = 2*k se tiene k tal que k ≥ 1 yy n = 2*k
  trivial

example (n : Nat) (h : ∃ k ≥ 1, n = 2*k ∧ k ≠ 0) : True := by
  Como ∃ k ≥ 1, n = 2*k ∧ k ≠ 0 se tiene k tal que k ≥ 1, n = 2*k yy k ≠ 0
  trivial

example (n : Nat) (h : ∃ (k l : Nat), n = k + l) : True := by
  Como ∃ (k l : Nat), n = k + l se tiene k yy l tal que n = k + l
  trivial

example (n : Nat) (h : ∃ (k l : Nat), n = k + l ∧ k = 1) : True := by
  Como ∃ (k l : Nat), n = k + l ∧ k = 1 se tiene k yy l tal que n = k + l yy k = 1
  trivial

example (n : Nat) (h : ∃ (k l : Nat), n = k + l ∧ k = 1 ∧ l = 2) : True := by
  Como ∃ (k l : Nat), n = k + l ∧ k = 1 ∧ l = 2 se tiene k yy l tal que n = k + l, k = 1
    yy l = 2
  trivial

example (n N : Nat) (hn : n ≥ N) (h : ∀ n ≥ N, ∃ k, n = 2*k) : True := by
  success_if_fail_with_msg "Aquí n ≥ n no es necesario."
    Como ∀ n ≥ N, ∃ k, n = 2*k, n ≥ N yy n ≥ n se tiene k tal que n = 2*k
  Como ∀ n ≥ N, ∃ k, n = 2*k yy n ≥ N se tiene k tal que n = 2*k
  trivial

example (P Q : Prop) (h : P ∧ Q)  : Q := by
  Como P ∧ Q se tiene P yy Q
  exact hQ

example (P Q R S : Prop) (h : P ↔ R) (h' : (Q → R) → S) : (Q → P) → S := by
  Como P ↔ R yy (Q → R) → S concluimos que (Q → P) → S

example (P Q R S : Prop) (h : P ↔ R) (h' : (Q → R) → S) : (Q → P) → S := by
  Como R ↔ P yy (Q → R) → S concluimos que (Q → P) → S

example (n : Nat) (P : Nat → Prop) (Q : ℕ → ℕ → Prop) (h : P n ∧ ∀ m, Q n m) : Q n n := by
  Como P n ∧ ∀ m, Q n m se tiene ∀ m, Q n m
  apply hQn

example (n : ℕ) (hn : n > 2) (P : ℕ → Prop) (h : ∀ n ≥ 3, P n) : True := by
  Como ∀ n ≥ 3, P n yy n ≥ 3 se tiene P n
  trivial

example (n : ℕ) (hn : n > 2) (P Q : ℕ → Prop) (h : ∀ n ≥ 3, P n ∧ Q n) : True := by
  Como ∀ n ≥ 3, P n ∧ Q n yy n ≥ 3 se tiene P n yy Q n
  trivial

example (n : ℕ) (hn : n > 2) (P : ℕ → Prop) (h : ∀ n ≥ 3, P n) : P n := by
  Como ∀ n ≥ 3, P n yy n ≥ 3 concluimos que P n

example (n : ℕ) (hn : n > 2) (P Q : ℕ → Prop) (h : ∀ n ≥ 3, P n ∧ Q n) : P n := by
  Como ∀ n ≥ 3, P n ∧ Q n yy n ≥ 3 concluimos que P n

example (n : ℕ) (hn : n > 2) (P Q : ℕ → Prop) (h : ∀ n ≥ 3, P n ∧ Q n) : True := by
  Como ∀ n ≥ 3, P n ∧ Q n yy n ≥ 3 se tiene P n
  trivial

example (n : ℕ) (hn : n > 2) (P Q : ℕ → Prop) (h : ∀ n ≥ 3, P n) (h' : ∀ n ≥ 3, Q n) : True := by
  Como ∀ n ≥ 3, P n, ∀ n ≥ 3, Q n yy n ≥ 3 se tiene P n yy Q n
  trivial

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  Como P → Q basta probar que P
  exact h'

example (P Q R : Prop) (h : P → R → Q) (hP : P) (hR : R) : Q := by
  Como P → R → Q basta probar que P yy R
  exact hP
  exact hR

set_option linter.unusedTactic false in
example (P : ℝ → Prop) (h : ∀ x > 0, P x)  : P 1 := by
  Como 1 > 0 yy ∀ x > 0, P x se tiene P 1
  guard_hyp_nums 3
  exact hP

set_option linter.unusedTactic false in
example (P Q : ℝ → Prop) (h : ∀ x > 0, P x → Q x) (h' : P 1) : Q 1 := by
  Como 1 > 0 yy ∀ x > 0, P x → Q x basta probar que P 1
  guard_hyp_nums 5
  exact h'

example (P Q R S : Prop) (h : P → R → Q → S) (hP : P) (hR : R) (hQ : Q) : S := by
  Como P → R → Q → S basta probar que P, R yy Q
  exact hP
  exact hR
  exact hQ

example (P Q : Prop) (h : P ↔ Q) (hP : P) : Q := by
  Como P ↔ Q basta probar que P
  exact hP

example (P Q : Prop) (h : P ↔ Q) (hP : P) : Q ∧ True:= by
  constructor
  Como P ↔ Q basta probar que P
  exact hP
  trivial

example (P : ℕ → Prop) (x y : ℕ) (h : x = y) (h' : P x) : P y := by
  success_if_fail_with_msg "No se pudo probar:
P : ℕ → Prop
x y : ℕ
GivenFact_0 : x = y
⊢ P y"
    Como x = y se tiene P y
  Como x = y yy P x se tiene P y
  exact hPy

example (P : ℕ → Prop) (x y : ℕ) (h : x = y) (h' : P x) : P y := by
  Como x = y yy P x concluimos que P y

example (P : ℕ → Prop) (x y : ℕ) (h : x = y) (h' : P x) : P y := by
  Como x = y basta probar que P x
  exact h'

-- example (n : ℤ) : Even (n^2) → Even n := by
--   contrapose
--   have := @Int.not_even_iff_odd
--   Como (¬ Even n ↔ Odd n) yy (¬ Even (n^2) ↔ Odd (n^2)) basta probar que Odd n → Odd (n^2)
--   rintro ⟨k, rfl⟩
--   use 2*k*(k+1)
--   ring

example (ε : ℝ) (ε_pos : ε > 0) : ε ≥ 0 := by
  Como ε > 0 concluimos que ε ≥ 0

example (f : ℕ → ℕ) (x y : ℕ) (h : x = y) : f x ≤ f y := by
  Como x = y concluimos que f x ≤ f y

configureAnonymousCaseSplittingLemmas le_or_gt lt_or_gt_of_ne lt_or_eq_of_le eq_or_lt_of_le Classical.em

example (P Q : Prop) (h : P ∨ Q) : True := by
  Decidimos en función de si  P o Q
  all_goals tauto

example (P Q : Prop) (h : P ∨ Q) : True := by
  Decidimos en función de si  Q o P
  all_goals tauto

example (P : Prop) : True := by
  Decidimos en función de si  P o ¬ P
  all_goals tauto

example (x y : ℕ) : True := by
  Decidimos en función de si  x ≤ y o x > y
  all_goals tauto

example (x y : ℕ) : True := by
  Decidimos en función de si  x = y o x ≠ y
  all_goals tauto

example (x y : ℕ) (h : x ≠ y) : True := by
  Decidimos en función de si  x < y o x > y
  all_goals tauto

example (ε : ℝ) (h : ε > 0) : ε ≥ 0 := by
  success_if_fail_with_msg "No se pudo probar:
ε : ℝ
SufficientFact_0 : ε < 0
⊢ ε ≥ 0"
    basta probar que ε < 0
  basta probar que ε > 0
  exact h

lemma le_le_of_max_le' {α : Type*} [LinearOrder α] {a b c : α} : max a b ≤ c → a ≤ c ∧ b ≤ c :=
max_le_iff.1

configureAnonymousFactSplittingLemmas le_max_left le_max_right le_le_of_max_le' le_of_max_le_left le_of_max_le_right

example (n a b : ℕ) (h : n ≥ max a b) : True := by
  Como n ≥ max a b se tiene n ≥ a yy n ≥ b
  trivial

example (n a b : ℕ) (h : n ≥ max a b) : True := by
  Como n ≥ max a b se tiene n ≥ a
  trivial

example (n a b : ℕ) (h : n ≥ max a b) (P : ℕ → Prop) (hP : ∀ n ≥ a, P n) : P n := by
  Como ∀ n ≥ a, P n yy n ≥ a concluimos que P n

set_option linter.unusedVariables false in
example (a b : ℕ) (P : ℕ → Prop) (h : ∀ n ≥ a, P n) : True := by
  Como ∀ n ≥ a, P n yy max a b ≥ a se tiene P (max a b)
  trivial

example (a b : ℝ) (h : a + b ≤ 3) (h' : b ≥ 0) : b*(a + b) ≤ b*3 := by
  success_if_fail_with_msg "No se pudo probar:
a b : ℝ
GivenFact_0 : a + b ≤ 3
⊢ b * (a + b) ≤ b * 3"
    Como a + b ≤ 3 concluimos que b*(a + b) ≤ b*3
  Como a + b ≤ 3 yy b ≥ 0 concluimos que b*(a + b) ≤ b*3

example (a b : ℝ) (hb : b = 2) : a + a*b = a + a*2 := by
  Como b = 2 concluimos que a + a*b = a + a*2

example (P Q R S T : Prop) (hPR : P ↔ R) : ((Q → R) → S) ↔ ((Q → P) → S) := by
  -- simp only [hPR]
  Como P ↔ R concluimos que ((Q → R) → S) ↔ ((Q → P) → S)

example (a k : ℤ) (h : a = 0*k) : a = 0 := by
  Como a = 0*k concluimos que a = 0

local macro_rules | `($x ∣ $y)   => `(@Dvd.dvd ℤ Int.instDvd ($x : ℤ) ($y : ℤ))

example (a : ℤ) (h : a = 0) : a ∣ 0 := by
  success_if_fail_with_msg "No se pudo probar:
a : ℤ
GivenFact_0 : a = 0
⊢ a ∣ 0"
    Como a = 0 concluimos que a ∣ 0
  Como a = 0 basta probar que 0 ∣ 0
  use 0
  rfl

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  Como P yy Q concluimos que P ∧ Q

example (P Q : Prop) (hPQ : P → Q) (hQP : Q → P) : P ↔ Q := by
  Como P → Q yy Q → P concluimos que P ↔ Q

example (P Q : Prop) (hPQ : P ↔ Q) : True := by
  Como P ↔ Q se tiene P → Q yy Q → P
  trivial

private lemma test_abs_le_of_le_le {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] {a b : α}
    (h : -b ≤ a) (h' : a ≤ b) : |a| ≤ b := abs_le.2 ⟨h, h'⟩

private lemma test_abs_le_of_le_le' {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] {a b : α}
    (h' : a ≤ b) (h : -b ≤ a) : |a| ≤ b := abs_le.2 ⟨h, h'⟩

private lemma test_abs_le_of_le_and_le {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] {a b : α}
    (h : -b ≤ a ∧ a ≤ b) : |a| ≤ b := abs_le.2 h

configureAnonymousGoalSplittingLemmas test_abs_le_of_le_le test_abs_le_of_le_le' test_abs_le_of_le_and_le

example (a b : ℝ) (h : a - b ≥ -1) (h' : a - b ≤ 1) : |a - b| ≤ 1 := by
  Como (-1 ≤ a - b ∧ a - b ≤ 1) → |a - b| ≤ 1 basta probar que -1 ≤ a - b ∧ a - b ≤ 1
  exact ⟨h, h'⟩

example (a b : ℝ) (h : a - b ≥ -1) (h' : a - b ≤ 1) : |a - b| ≤ 1 := by
  Como (-1 ≤ a - b ∧ a - b ≤ 1) → |a - b| ≤ 1 basta probar que -1 ≤ a - b yy a - b ≤ 1
  all_goals assumption

example (a b : ℝ) (h : a - b ≥ -1) (h' : a - b ≤ 1) : |a - b| ≤ 1 := by
  Como -1 ≤ a - b → a - b ≤ 1 → |a - b| ≤ 1 basta probar que -1 ≤ a - b yy a - b ≤ 1
  all_goals assumption

example (u v : ℕ → ℝ) (h : ∀ n, u n ≤ v n) : u 0 - 2 ≤ v 0 - 2 := by
  Como ∀ n, u n ≤ v n concluimos que u 0 - 2 ≤ v 0 - 2

example (P : Nat → Prop) (h : ∃ x, ¬ P x) : ¬ (∀ x, P x) := by
  basta probar que ∃ x, ¬ P x
  exact h

example (P Q : Prop) (h : ¬ P ∨ Q) : P → Q := by
  Como ¬ P ∨ Q concluimos que P → Q

example (P : Prop) (x : ℝ) (h : ¬ (P ∧ x < 0)) : P → x ≥ 0 := by
  Como ¬ (P ∧ x < 0) concluimos que P → x ≥ 0

private def foo_bar (P : Nat → Prop) := ∀ x, P x
configureUnfoldableDefs foo_bar

example (P : Nat → Prop) (h : ∃ x, ¬ P x) : ¬ foo_bar P := by
  basta probar que ∃ x, ¬ P x
  exact h

example (P : Nat → Prop) (h : ¬ foo_bar P) : ∃ x, ¬ P x := by
  Como ¬ foo_bar P se tiene ∃ x, ¬ P x
  exact hP

example (P : Nat → Prop) (h : ∃ x, ¬ P x) : ¬ (∀ x, P x) := by
  Como ∃ x, ¬ P x concluimos que ¬ (∀ x, P x)

example (P : Nat → Prop) (h : ∃ x, ¬ P x) : True := by
  Como ∃ x, ¬ P x se tiene ¬ (∀ x, P x)
  trivial

example (h : (2 : ℝ) * -42 = 2 * 42) : False := by
  -- Note: the following example doesn’t need backtracking because linarith
  -- finds a proof using h anyway
  Como 2 * -42 = 2 * 42 concluimos que False

-- The next three examples test reelaborating numbers as reals after failure

example (P : ℝ → Prop) (h : ∀ ε > 0, P ε) : P 1 := by
  Como ∀ ε > 0, P ε yy 1 > 0 se tiene P 1
  exact hP

example (P : ℝ → Prop) (h : ∀ ε > 0, P ε) : P 1 := by
  Como ∀ ε > 0, P ε yy 1 > 0 concluimos que P 1

example (P : ℝ → Prop) (h : ∀ ε > 0, P ε) : P 1 := by
  Como ∀ ε > 0, P ε basta probar que 1 > 0
  norm_num

example (l : ℝ) (N : ℕ) (h : |(-1)^(2*N) - l| ≤ 1/2) : True := by
  Como |(-1)^(2*N) - l| ≤ 1/2 yy (-1)^(2*N) = (1 : ℝ) se tiene |1 - l| ≤ 1/2
  trivial

noncomputable section
example (f : ℕ → ℕ) (h : ∀ y, ∃ x, f x = y) : ℕ → ℕ := by
  Como ∀ y, ∃ x, f x = y elegimos g tal que ∀ (y : ℕ), f (g y) = y
  exact g

example (f : ℕ → ℕ) (A : Set ℕ) (h : ∀ y, ∃ x ∈ A, f x = y) : ℕ → ℕ := by
  Como ∀ y, ∃ x ∈ A, f x = y elegimos g tal que ∀ (y : ℕ), g y ∈ A yy ∀ (y : ℕ), f (g y) = y
  exact g

example (f : ℕ → ℕ) (A : Set ℕ) (h : ∀ y, ∃ x ∈ A, f x = y) : ℕ → ℕ := by
  Como ∀ y, ∃ x ∈ A, f x = y elegimos g tal que ∀ (y : ℕ), g y + 0 ∈ A yy ∀ (y : ℕ), f (g y) = y
  exact g

end

addAnonymousFactSplittingLemma lt_of_lt_of_le

example (ε : ℝ) (ε_pos : 1/ε > 0) (N : ℕ) (hN : N ≥ 1 / ε) : True := by
  Como N ≥ 1/ε yy 1/ε > 0 se tiene N > 0
  trivial

example (ε : ℝ) (ε_pos : 1/ε > 0) (N : ℕ) (hN : N ≥ 1 / ε) : N > 0 := by
  Como N ≥ 1/ε yy 1/ε > 0 concluimos que N > 0

addAnonymousFactSplittingLemma abs_of_pos
example (a b : ℝ) (h : a ≥ b) (h' : b > 0) : True := by
  Como a ≥ b yy b > 0 se tiene a > 0 luego |a| = a
  trivial

example (a b : ℝ) (h : a ≥ b) (h' : b > 0) : |a| = a := by
  Como a ≥ b yy b > 0 se tiene a > 0 finalmente concluimos que |a| = a
