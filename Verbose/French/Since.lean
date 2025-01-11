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

set_option linter.unusedVariables false

example (n : Nat) (h : ∃ k, n = 2*k) : True := by
  Comme ∃ k, n = 2*k on obtient k tel que H : n = 2*k
  trivial

example (n N : Nat) (hn : n ≥ N) (h : ∀ n ≥ N, ∃ k, n = 2*k) : True := by
  Comme ∀ n ≥ N, ∃ k, n = 2*k et n ≥ N on obtient k tel que H : n = 2*k
  trivial

example (P Q : Prop) (h : P ∧ Q)  : Q := by
  Comme P ∧ Q on obtient (hP : P) et (hQ : Q)
  exact hQ

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
  constructor
  exact hP
  exact hR

example (P : ℕ → Prop) (x y : ℕ) (h : x = y) (h' : P x) : P y := by
  success_if_fail_with_msg "
La justification a échoué :
P : ℕ → Prop
x y : ℕ
h : x = y
h' : P x
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

example (n : ℤ) : Even (n^2) → Even n := by
  contrapose
  have := @Int.not_even_iff_odd
  Comme (¬ Even n ↔ Odd n) et (¬ Even (n^2) ↔ Odd (n^2)) il suffit de montrer que Odd n → Odd (n^2)
  rintro ⟨k, rfl⟩
  use 2*k*(k+1)
  ring

example (ε : ℝ) (ε_pos : ε > 0) : ε ≥ 0 := by
  Comme ε > 0 on conclut que ε ≥ 0

configureAnonymousCaseSplittingLemmas le_or_gt lt_or_gt_of_ne lt_or_eq_of_le eq_or_lt_of_le Classical.em

example (P Q : Prop) (h : P ∨ Q) : True := by
  On discute selon que P ou Q
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
h : ε > 0
SufficientFact : ε < 0
⊢ ε ≥ 0"
    Il suffit de montrer que ε < 0
  Il suffit de montrer que ε > 0
  exact h

configureAnonymousFactSplittingLemmas le_max_left le_max_right

set_option linter.unusedVariables false in
example (a b : ℕ) (P : ℕ → Prop) (h : ∀ n ≥ a, P n) : True := by
  Comme ∀ n ≥ a, P n et max a b ≥ a on obtient H : P (max a b)
  trivial
