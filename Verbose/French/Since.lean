import Verbose.Tactics.Since
import Verbose.French.Common
import Lean

namespace Verbose.French

open Lean Elab Tactic

elab "Comme " facts:factsFR " on obtient " news:newObjectFR : tactic => do
  let newsT ← newObjectFRToTerm news
  let news_patt := newObjectFRToRCasesPatt news
  let factsT := factsFRToArray facts
  sinceObtainTac newsT news_patt factsT

elab "Comme " facts:factsFR " on obtient " news:newFactsFR : tactic => do
  let newsT ← newFactsFRToTypeTerm news
  -- dbg_trace "newsT {newsT}"
  let news_patt := newFactsFRToRCasesPatt news
  let factsT := factsFRToArray facts
  -- dbg_trace "factsT {factsT}"
  sinceObtainTac newsT news_patt factsT

elab "Comme " facts:factsFR " on conclut que " concl:term : tactic => do
  let factsT := factsFRToArray facts
  -- dbg_trace "factsT {factsT}"
  sinceConcludeTac concl factsT

elab "Comme " facts:factsFR " il suffit de montrer " " que " newGoals:factsFR : tactic => do
  let factsT := factsFRToArray facts
  let newGoalsT := factsFRToArray newGoals
  sinceSufficesTac factsT newGoalsT

implement_endpoint (lang := fr) couldNotProve (goal : Format) : CoreM String :=
pure s!"La justification a échoué :\n {goal}"

implement_endpoint (lang := fr) failedProofUsing (goal : Format) : CoreM String :=
pure s!"La justification en utilisant les faits fournis a échoué :\n{goal}"

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
