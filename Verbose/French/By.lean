import Verbose.Tactics.By
import Verbose.French.Common

namespace Verbose.French

open Lean Elab Tactic

elab "Par " e:maybeAppliedFR " on obtient " colGt news:newStuffFR : tactic => do
obtainTac (← maybeAppliedFRToTerm e) (newStuffFRToArray news)

elab "Par " e:maybeAppliedFR " on choisit " colGt news:newStuffFR : tactic => do
chooseTac (← maybeAppliedFRToTerm e) (newStuffFRToArray news)

elab "Par " e:maybeAppliedFR " il suffit de montrer " "que "? colGt arg:term : tactic => do
bySufficesTac (← maybeAppliedFRToTerm e) #[arg]

elab "Par " e:maybeAppliedFR " il suffit de montrer " "que "? colGt args:sepBy(term, " et ") : tactic => do
bySufficesTac (← maybeAppliedFRToTerm e) args.getElems

macro "hypothèse" : term => `(by assumption)

lemma le_le_of_abs_le {α : Type*} [LinearOrderedAddCommGroup α] {a b : α} : |a| ≤ b → -b ≤ a ∧ a ≤ b := abs_le.1

lemma le_le_of_max_le {α : Type*} [LinearOrder α] {a b c : α} : max a b ≤ c → a ≤ c ∧ b ≤ c :=
max_le_iff.1

implement_endpoint (lang := fr) cannotGet : CoreM String := pure "Impossible de déduire cela."

implement_endpoint (lang := fr) theName : CoreM String := pure "Le nom"

implement_endpoint (lang := fr) needName : CoreM String :=
pure "Vous devez fournir un nom pour l’objet choisi."

implement_endpoint (lang := fr) wrongNbGoals : CoreM String :=
pure s!"Il n’y a pas tant d’affirmations à vérifier."

implement_endpoint (lang := fr) doesNotApply (fact : Format) : CoreM String :=
pure s!"On ne peut pas appliquer {fact}."

implement_endpoint (lang := fr) couldNotInferImplVal (val : Name) : CoreM String :=
pure s!"N’a pas pu inférer la valeur implicite de {val}."

implement_endpoint (lang := fr) alsoNeedCheck (fact : Format) : CoreM String :=
pure s!"Il faut aussi vérifier {fact}"

configureAnonymousFactSplittingLemmas le_le_of_abs_le le_le_of_max_le

setLang fr

example (P : Nat → Prop) (h : ∀ n, P n) : P 0 := by
  Par h appliqué à 0 on obtient h₀

  exact h₀

example (P : Nat → Nat → Prop) (h : ∀ n k, P n (k+1)) : P 0 1 := by
  Par h appliqué à 0 et 0 on obtient (h₀ : P 0 1)
  exact h₀

example (n : Nat) (h : ∃ k, n = 2*k) : True := by
  Par h on obtient k tel que H
  trivial

example (P Q : Prop) (h : P ∧ Q)  : Q := by
  Par h on obtient (hP : P) (hQ : Q)
  exact hQ

example (x : ℝ) (h : |x| ≤ 3) : True := by
  Par h on obtient (h₁ : -3 ≤ x) (h₂ : x ≤ 3)
  trivial

example (n p q : ℕ) (h : n ≥ max p q) : True := by
  Par h on obtient (h₁ : n ≥ p) (h₂ : n ≥ q)
  trivial

noncomputable example (f : ℕ → ℕ) (h : ∀ y, ∃ x, f x = y) : ℕ → ℕ := by
  Par h on choisit g tel que (H : ∀ (y : ℕ), f (g y) = y)
  exact g

noncomputable example (f : ℕ → ℕ) (A : Set ℕ) (h : ∀ y, ∃ x ∈ A, f x = y) : ℕ → ℕ := by
  Par h on choisit g tel que (H : ∀ (y : ℕ), g y ∈ A) et (H' : ∀ (y : ℕ), f (g y) = y)
  exact g

noncomputable example (f : ℕ → ℕ) (A : Set ℕ) (h : ∀ y, ∃ x ∈ A, f x = y) : ℕ → ℕ := by
  Par h on choisit g tel que (H : ∀ (y : ℕ), g y + 0 ∈ A) et (H' : ∀ (y : ℕ), f (g y) = y)
  exact g

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  Par h il suffit de montrer que P
  exact h'

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  Par h il suffit de montrer P
  exact h'

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  Par h il suffit de montrer P
  exact hypothèse

example (P Q R : Prop) (h : P → R → Q) (hP : P) (hR : R) : Q := by
  Par h il suffit de montrer P et R
  exact hP
  exact hR

set_option linter.unusedVariables false in
example (P Q : Prop) (h : ∀ n : ℕ, P → Q) (h' : P) : Q := by
  success_if_fail_with_msg "On ne peut pas appliquer h 0 1."
    Par h appliqué à 0 et 1 il suffit de montrer P
  Par h appliqué à 0 il suffit de montrer P
  exact h'


example (Q : Prop) (h : ∀ n : ℤ, n > 0 → Q)  : Q := by
  Par h appliqué à 1 il suffit de montrer 1 > 0
  norm_num

example (Q : Prop) (h : ∀ n : ℤ, n > 0 → Q)  : Q := by
  Par h il suffit de montrer 1 > 0
  norm_num

example {P Q R : ℕ → Prop} {n k l : ℕ} (h : ∀ k l, P k → Q l → R n) (hk : P k) (hl : Q l) :
    R n := by
  success_if_fail_with_msg "Il faut aussi vérifier Q ?l"
    Par h il suffit de montrer que P k
  Par h il suffit de montrer que P k et Q l
  exact hk
  exact hl

set_option linter.unusedVariables false in
example (n : Nat) (h : ∃ n : Nat, n = n) : True := by
  success_if_fail_with_msg "Le nom n est déjà utilisé."
    Par h on obtient n tel que H
  trivial
