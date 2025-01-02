import Verbose.Tactics.Since
import Verbose.English.Common
import Lean

namespace Verbose.English

open Lean Elab Tactic

elab "Since " facts:facts " we get " news:newObject : tactic => do
  let newsT ← newObjectToTerm news
  let news_patt := newObjectToRCasesPatt news
  let factsT := factsToArray facts
  sinceObtainTac newsT news_patt factsT

elab "Since " facts:facts " we get " news:newFacts : tactic => do
  let newsT ← newFactsToTypeTerm news
  let news_patt := newFactsToRCasesPatt news
  let factsT := factsToArray facts
  sinceObtainTac newsT news_patt factsT

elab "Since " facts:facts " we conclude that " concl:term : tactic => do
  let factsT := factsToArray facts
  -- dbg_trace "factsT {factsT}"
  sinceConcludeTac concl factsT

elab "Since " facts:facts " it suffices to prove " " that " newGoals:facts : tactic => do
  let factsT := factsToArray facts
  let newGoalsT := factsToArray newGoals
  sinceSufficesTac factsT newGoalsT

implement_endpoint (lang := en) couldNotProve (goal : Format) : CoreM String :=
pure s!"Could not prove:\n {goal}"

implement_endpoint (lang := en) failedProofUsing (goal : Format) : CoreM String :=
pure s!"Failed to prove this using the provided facts.\n{goal}"

set_option linter.unusedVariables false

example (n : Nat) (h : ∃ k, n = 2*k) : True := by
  Since ∃ k, n = 2*k we get k such that H : n = 2*k
  trivial

example (n N : Nat) (hn : n ≥ N) (h : ∀ n ≥ N, ∃ k, n = 2*k) : True := by
  Since ∀ n ≥ N, ∃ k, n = 2*k and n ≥ N we get k such that H : n = 2*k
  trivial

example (P Q : Prop) (h : P ∧ Q)  : Q := by
  Since P ∧ Q we get (hP : P) and (hQ : Q)
  exact hQ

example (n : ℕ) (hn : n > 2) (P : ℕ → Prop) (h : ∀ n ≥ 3, P n) : True := by
  Since ∀ n ≥ 3, P n and n ≥ 3 we get H : P n
  trivial

example (n : ℕ) (hn : n > 2) (P Q : ℕ → Prop) (h : ∀ n ≥ 3, P n ∧ Q n) : True := by
  Since ∀ n ≥ 3, P n ∧ Q n and n ≥ 3 we get H : P n and H' : Q n
  trivial

example (n : ℕ) (hn : n > 2) (P : ℕ → Prop) (h : ∀ n ≥ 3, P n) : P n := by
  Since ∀ n ≥ 3, P n and n ≥ 3 we conclude that P n

example (n : ℕ) (hn : n > 2) (P Q : ℕ → Prop) (h : ∀ n ≥ 3, P n ∧ Q n) : P n := by
  Since ∀ n ≥ 3, P n ∧ Q n and n ≥ 3 we conclude that P n

example (n : ℕ) (hn : n > 2) (P Q : ℕ → Prop) (h : ∀ n ≥ 3, P n ∧ Q n) : True := by
  Since ∀ n ≥ 3, P n ∧ Q n and n ≥ 3 we get H : P n
  trivial

example (n : ℕ) (hn : n > 2) (P Q : ℕ → Prop) (h : ∀ n ≥ 3, P n) (h' : ∀ n ≥ 3, Q n) : True := by
  Since ∀ n ≥ 3, P n, ∀ n ≥ 3, Q n and n ≥ 3 we get H : P n and H' : Q n
  trivial

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  Since P → Q it suffices to prove that P
  exact h'

example (P Q R : Prop) (h : P → R → Q) (hP : P) (hR : R) : Q := by
  Since P → R → Q it suffices to prove that P and R
  constructor
  exact hP
  exact hR

example (P : ℕ → Prop) (x y : ℕ) (h : x = y) (h' : P x) : P y := by
  success_if_fail_with_msg "
Could not prove:
 P : ℕ → Prop
x y : ℕ
h : x = y
h' : P x
GivenFact_0 : x = y
⊢ P y"
    Since x = y we get H : P y
  Since x = y and P x we get H : P y
  exact H

example (P : ℕ → Prop) (x y : ℕ) (h : x = y) (h' : P x) : P y := by
  Since x = y and P x we conclude that P y

example (P : ℕ → Prop) (x y : ℕ) (h : x = y) (h' : P x) : P y := by
  Since x = y it suffices to prove that P x
  exact h'

example (n : ℤ) : Even (n^2) → Even n := by
  contrapose
  have := @Int.not_even_iff_odd
  Since (¬ Even n ↔ Odd n) and (¬ Even (n^2) ↔ Odd (n^2)) it suffices to prove that Odd n → Odd (n^2)
  rintro ⟨k, rfl⟩
  use 2*k*(k+1)
  ring
