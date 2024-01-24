import Mathlib.Topology.MetricSpace.Basic
import Verbose.English.All

@[unfoldable_def]
def continuous_function_at (f : ℝ → ℝ) (x₀ : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

@[unfoldable_def]
def sequence_tendsto (u : ℕ → ℝ) (l : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

notation3:50 f:80 " is continuous at " x₀ => continuous_function_at f x₀
notation3:50 u:80 " converges to " l => sequence_tendsto u l

@[unfoldable_def]
def increasing (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

notation3 u " is increasing" => increasing u

@[unfoldable_def]
def is_supremum (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

notation3 M " is a supremum of " u => is_supremum M u

section Subset
variable {α : Type*}

/- HACK: The Mathlib definition of `Set.Subset` uses a strict-implicit
argument which confuses Verbose Lean. So let us replace it. -/

protected def Verbose.English.Subset (s₁ s₂ : Set α) :=
  ∀ a, a ∈ s₁ → a ∈ s₂

instance (priority := high) Verbose.English.hasSubset : HasSubset (Set α) :=
  ⟨Verbose.English.Subset⟩

attribute [anonymous_split_lemma] Set.Subset.antisymm
end Subset
