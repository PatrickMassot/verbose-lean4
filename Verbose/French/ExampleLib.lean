import Mathlib.Topology.MetricSpace.Basic
import Verbose.French.All

def continue_en (f : ℝ → ℝ) (x₀ : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

def tend_vers (u : ℕ → ℝ) (l : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

notation:50 f:80 " est continue en " x₀ => continue_en f x₀
notation:50 u:80 " tend vers " l => tend_vers u l

def suite_croissante (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

notation u " est croissante" => suite_croissante u

def est_sup (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

notation M " est un supremum de " u => est_sup M u

configureUnfoldableDefs continue_en tend_vers suite_croissante est_sup

section Subset
variable {α : Type*}

/- The Mathlib definition of `Set.Subset` uses a strict-implicit
argument which confuses Verbose Lean. So let us replace it. -/

protected def Verbose.French.Subset (s₁ s₂ : Set α) :=
  ∀ a, a ∈ s₁ → a ∈ s₂

instance (priority := high) Verbose.French.hasSubset : HasSubset (Set α) :=
  ⟨Verbose.French.Subset⟩

end Subset

open Verbose.French

configureAnonymousFactSplittingLemmas le_le_of_abs_le le_le_of_max_le

configureAnonymousGoalSplittingLemmas LogicIntros AbsIntros Set.Subset.antisymm

useDefaultDataProviders

useDefaultSuggestionProviders
