import Verbose.Tactics.We
import Verbose.English.Common

open Lean Elab Parser Tactic Verbose.English

declare_syntax_cat becomes
syntax colGt " which becomes " term : becomes

def extractBecomes (e : Lean.TSyntax `becomes) : Lean.Term := ⟨e.raw[1]!⟩

elab rw:"We" " rewrite using " s:myRwRuleSeq l:(location)? new:(becomes)? : tactic => do
  rewriteTac rw s (l.map expandLocation) (new.map extractBecomes)

elab rw:"We" " rewrite using " s:myRwRuleSeq " everywhere" : tactic => do
  rewriteTac rw s (some Location.wildcard) none

elab "We" " discuss using" exp:term : tactic =>
  discussOr exp

elab "We" " discuss depending on" exp:term : tactic =>
  discussEm exp

elab "We" " conclude by " e:maybeApplied : tactic => do
  concludeTac (← maybeAppliedToTerm e)

elab "We" " combine [" prfs:term,* "]" : tactic => do
  combineTac prfs.getElems

elab "We" " compute" loc:(location)? : tactic => do
  computeTac loc

elab "We" " apply " exp:term : tactic => do
  evalApply (← `(tactic|apply $exp))

elab "We" " apply " exp:term " at " h:ident: tactic => do
  let loc ← ident_to_location h
  evalTactic (← `(tactic|apply_fun $exp $loc:location))

elab "We" " apply " exp:term " to " e:term : tactic => do
  evalTactic (← `(tactic|specialize $exp $e))

macro "We" " forget" args:(ppSpace colGt term:max)+ : tactic => `(tactic|clear $args*)

macro "We" " reformulate " h:ident " as " new:term : tactic => `(tactic|change $new at $h:ident)

example (P Q : Prop) (h : P ∨ Q) : True := by
  We discuss using h
  . intro _hP
    trivial
  . intro _hQ
    trivial


example (P : Prop) : True := by
  We discuss depending on P
  . intro _hP
    trivial
  . intro _hnP
    trivial

set_option linter.unusedVariables false in
example (P Q R : Prop) (hRP : R → P) (hR : R) (hQ : Q) : P := by
  success_if_fail_with_msg "application type mismatch
  hRP hQ
argument
  hQ
has type
  Q : Prop
but is expected to have type
  R : Prop"
    We conclude by hRP applied to hQ
  We conclude by hRP applied to hR

example (P : ℕ → Prop) (h : ∀ n, P n) : P 0 := by
  We conclude by h applied to _

example (P : ℕ → Prop) (h : ∀ n, P n) : P 0 := by
  We conclude by h

example {a b : ℕ}: a + b = b + a := by
  We compute

example {a b : ℕ} (h : a + b - a = 0) : b = 0 := by
  We compute at h
  We conclude by h

variable (k : Nat)

example (h : True) : True := by
  We conclude by h

example (h : ∀ _n : ℕ, True) : True := by
  We conclude by h applied to 0

example (h : True → True) : True := by
  We apply h
  trivial

example (h : ∀ _n _k : ℕ, True) : True := by
  We conclude by h applied to [0, 1]

example (a b : ℕ) (h : a < b) : a ≤ b := by
  We conclude by h

example (a b c : ℕ) (h : a < b ∧ a < c) : a ≤ b := by
  We conclude by h

example (a b c : ℕ) (h : a ≤ b) (h' : b ≤ c) : a ≤ c := by
  We combine [h, h']

example (a b c : ℤ) (h : a = b + c) (h' : b - a = c) : c = 0 := by
  We combine [h, h']

example (a b c : ℕ) (h : a ≤ b) (h' : b ≤ c ∧ a+b ≤ a+c) : a ≤ c := by
  We combine [h, h']

example (a b c : ℕ) (h : a = b) (h' : a = c) : b = c := by
  We rewrite using ← h
  We conclude by h'

example (a b c : ℕ) (h : a = b) (h' : a = c) : b = c := by
  We rewrite using h at h'
  We conclude by h'

example (a b : Nat) (h : a = b) (h' : b = 0): a = 0 := by
  We rewrite using ← h at h' which becomes a = 0
  exact h'

example (a b : Nat) (h : a = b) (h' : b = 0): a = 0 := by
  We rewrite using ← h at h'
  clear h
  exact h'

example (f : ℕ → ℕ) (n : ℕ) (h : n > 0 → f n = 0) (hn : n > 0): f n = 0 := by
  We rewrite using h
  exact hn

example (f : ℕ → ℕ) (h : ∀ n > 0, f n = 0) : f 1 = 0 := by
  We rewrite using h
  norm_num

example (a b c : ℕ) (h : a = b) (h' : a = c) : b = c := by
  success_if_fail_with_msg "Given term
  a = c
is not definitionally equal to the expected
  b = c
"
    We rewrite using [h] at h' which becomes a = c
  We rewrite using [h] at h' which becomes b = c
  We conclude by h'

example (a b c : ℕ) (h : a = b) (h' : a = c) : a = c := by
  We rewrite using h everywhere
  We conclude by h'

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  We apply h to h'
  We conclude by h

example (P Q R : Prop) (h : P → Q → R) (hP : P) (hQ : Q) : R := by
  We conclude by h applied to [hP, hQ]

example (f : ℕ → ℕ) (a b : ℕ) (h : a = b) : f a = f b := by
  We apply f at h
  We conclude by h

example (P : ℕ → Prop) (h : ∀ n, P n) : P 0 := by
  We apply h to 0
  We conclude by h

/-
example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 := by
  We contrapose
  intro h
  use x/2
  split
   We conclude by h, -- linarith
  We conclude by h, -- linarith
 -/
example (ε : ℝ) (h : ε > 0) : ε ≥ 0 := by We conclude by h
example (ε : ℝ) (h : ε > 0) : ε/2 > 0 := by We conclude by h
example (ε : ℝ) (h : ε > 0) : ε ≥ -1 := by We conclude by h
example (ε : ℝ) (h : ε > 0) : ε/2 ≥ -3 := by We conclude by h

example (x : ℝ) (h : x = 3) : 2*x = 6 := by We conclude by h

/- example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 := by
  We contrapose simply
  intro h
  We push the negation
  We push the negation at h
  use x/2
  split
   We conclude by h, -- linarith
  We conclude by h, -- linarith

example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 := by
  We contrapose simply
  intro h
  success_if_fail_with_msg ""
    We push the negation which becomes 0 < x
  We push the negation
  success_if_fail_with_msg ""
    We push the negation at h which becomes ∃ (ε : ℝ), ε > 0 ∧ ε < x
  We push the negation at h which becomes 0 < x
  use x/2
  split
   We conclude by h, -- linarith
  We conclude by h, -- linarith

example : (∀ n : ℕ, false) → 0 = 1 := by
  We contrapose
  We compute
 -/
example (P Q : Prop) (h : P ∨ Q) : True := by
  We discuss using h
  all_goals
    intro
    trivial

example (P : Prop) (hP₁ : P → True) (hP₂ : ¬ P → True): True := by
  We discuss depending on P
  intro h
  exact hP₁ h
  intro h
  exact hP₂ h

/-
namespace Verbose.English

def f (n : ℕ) := 2*n

example : f 2 = 4 := by
  We unfold f
  refl

example (h : f 2 = 4) : True → True := by
  We unfold f at h
  guard_hyp_strict h : 2*2 = 4
  exact id

example (h : f 2 = 4) : True → True := by
  success_if_fail_with_msg ""
    We unfold f at h which becomes 2*2 = 5
  We unfold f at h which becomes 2*2 = 4
  exact id

example (P : ℕ → ℕ → Prop) (h : ∀ n : ℕ, ∃ k, P n k) : True := by
  We rename n to p at h
  We rename k to l at h
  guard_hyp_strict h : ∀ p, ∃ l, P p l
  trivial

example (P : ℕ → ℕ → Prop) (h : ∀ n : ℕ, ∃ k, P n k) : True := by
  We rename n to p at h which becomes ∀ p, ∃ k, P p k
  success_if_fail_with_msg ""
    We rename k to l at h which becomes ∀ p, ∃ j, P p j
  We rename k to l at h which becomes ∀ p, ∃ l, P p l
  trivial

example (P : ℕ → ℕ → Prop) : (∀ n : ℕ, ∃ k, P n k) ∨ True := by
  We rename n to p
  We rename k to l
  guard_target_strict (∀ p, ∃ l, P p l) ∨ True
  right
  trivial
 -/
example (a b c : ℕ) : True := by
  We forget a
  We forget b c
  trivial

example (h : 1 + 1 = 2) : True := by
  success_if_fail_with_msg "type mismatch
  this
has type
  2 = 3 : Prop
but is expected to have type
  1 + 1 = 2 : Prop"
    We reformulate h as 2 = 3
  We reformulate h as 2 = 2
  trivial
