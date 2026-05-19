import Verbose.Tactics.By
import Verbose.Spanish.Common

open Lean Verbose.Spanish


elab "Por " e:maybeAppliedES (" tenemos " <|> " se tiene ") colGt news:newStuffES : tactic => do
obtainTac (← maybeAppliedESToTerm e) (newStuffESToArray news)

elab "Por " e:maybeAppliedES " podemos elegir " colGt news:newStuffES : tactic => do
chooseTac (← maybeAppliedESToTerm e) (newStuffESToArray news)

elab "Por " e:maybeAppliedES " basta probar " "que "? colGt arg:term : tactic => do
bySufficesTac (← maybeAppliedESToTerm e) #[arg]

elab "Por " e:maybeAppliedES " basta probar " "que "? colGt args:sepBy(term, " yy ") : tactic => do
bySufficesTac (← maybeAppliedESToTerm e) args.getElems

elab "hipótesis" : tactic => assumption'

macro "hipótesis" : term => `(by hipótesis)

lemma le_le_of_abs_le {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] {a b : α} : |a| ≤ b → -b ≤ a ∧ a ≤ b := abs_le.1

lemma le_le_of_max_le {α : Type*} [LinearOrder α] {a b c : α} : max a b ≤ c → a ≤ c ∧ b ≤ c :=
max_le_iff.1

implement_endpoint (lang := es) cannotGet : CoreM String := pure "Imposible de deducir."

implement_endpoint (lang := es) theName : CoreM String := pure "El nombre"

implement_endpoint (lang := es) needName : CoreM String :=
pure "Tienes que asignar un nombre al objeto elegido."

implement_endpoint (lang := es) wrongNbGoals : CoreM String :=
pure s!"No hay suficientes afirmaciones a verificar."

implement_endpoint (lang := es) doesNotApply (fact : Format) : CoreM String :=
pure s!"No se puede aplicar {fact}."

implement_endpoint (lang := es) couldNotInferImplVal (val : Name) : CoreM String :=
pure s!"No se ha podido inferir el valor implicito de {val}."

implement_endpoint (lang := es) alsoNeedCheck (fact : Format) : CoreM String :=
pure s!"También tienes que verificar {fact}"

configureAnonymousFactSplittingLemmas le_le_of_abs_le le_le_of_max_le

setLang es

example (P : Nat → Prop) (h : ∀ n, P n) : P 0 := by
  Por h aplicado a 0 tenemos h₀
  exact h₀

example (P : Nat → Nat → Prop) (h : ∀ n k, P n (k+1)) : P 0 1 := by
  Por h aplicado a 0 yy 0 se tiene (h₀ : P 0 1)
  exact h₀

example (n : Nat) (h : ∃ k, n = 2*k) : True := by
  Por h tenemos k tal que (H : n = 2*k)
  trivial

example (n : Nat) (h : ∃ k, n = 2*k) : True := by
  Por h tenemos k tal que H
  trivial

example (P Q : Prop) (h : P ∧ Q)  : Q := by
  Por h tenemos (hP : P) (hQ : Q)
  exact hQ

example (x : ℝ) (h : |x| ≤ 3) : True := by
  Por h tenemos (h₁ : -3 ≤ x) (h₂ : x ≤ 3)
  trivial

example (n p q : ℕ) (h : n ≥ max p q) : True := by
  Por h tenemos (h₁ : n ≥ p) (h₂ : n ≥ q)
  trivial

noncomputable example (f : ℕ → ℕ) (h : ∀ y, ∃ x, f x = y) : ℕ → ℕ := by
  Por h podemos elegir g tal que (H : ∀ (y : ℕ), f (g y) = y)
  exact g

noncomputable example (f : ℕ → ℕ) (A : Set ℕ) (h : ∀ y, ∃ x ∈ A, f x = y) : ℕ → ℕ := by
  Por h podemos elegir g tal que (H : ∀ (y : ℕ), g y ∈ A) yy (H' : ∀ (y : ℕ), f (g y) = y)
  exact g

noncomputable example (f : ℕ → ℕ) (A : Set ℕ) (h : ∀ y, ∃ x ∈ A, f x = y) : ℕ → ℕ := by
  Por h podemos elegir g tal que (H : ∀ (y : ℕ), g y + 0 ∈ A) yy (H' : ∀ (y : ℕ), f (g y) = y)
  exact g

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  Por h basta probar que  P
  exact h'

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  Por h basta probar que  P
  exact h'

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  Por h basta probar que  P
  exact hipótesis

example (P Q R : Prop) (h : P → R → Q) (hP : P) (hR : R) : Q := by
  Por h basta probar que  P yy R
  exact hP
  exact hR

set_option linter.unusedVariables false in
example (P Q : Prop) (h : ∀ n : ℕ, P → Q) (h' : P) : Q := by
  success_if_fail_with_msg "No se puede aplicar h 0 1."
    Por h aplicado a 0 yy 1 basta probar que  P
  Por h aplicado a 0 basta probar que  P
  exact h'

example (Q : Prop) (h : ∀ n : ℤ, n > 0 → Q)  : Q := by
  Por h aplicado a 1 basta probar que  1 > 0
  norm_num

example (Q : Prop) (h : ∀ n : ℤ, n > 0 → Q)  : Q := by
  Por h basta probar que  1 > 0
  norm_num

example {P Q R : ℕ → Prop} {n k l : ℕ} (h : ∀ k l, P k → Q l → R n) (hk : P k) (hl : Q l) :
    R n := by
  success_if_fail_with_msg "También tienes que verificar Q ?l"
    Por h basta probar que  P k
  Por h basta probar que  P k yy Q l
  exact hk
  exact hl

set_option linter.unusedVariables false in
example (n : Nat) (h : ∃ n : Nat, n = n) : True := by
  success_if_fail_with_msg "El nombre n ya está en uso"
    Por h tenemos n tal que H
  trivial
