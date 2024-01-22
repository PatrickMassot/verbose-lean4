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
