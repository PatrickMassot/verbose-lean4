import Mathlib.Topology.MetricSpace.Basic
import Verbose.Spanish.All

def continuous_function_at (f : ℝ → ℝ) (x₀ : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

def sequence_tendsto (u : ℕ → ℝ) (l : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

notation:50 f:80 " es continua en " x₀ => continuous_function_at f x₀
notation:50 u:80 " converge a " l => sequence_tendsto u l

def increasing_seq (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

notation u " es creciente" => increasing_seq u

def is_supremum (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

notation M " es un supremo de " u => is_supremum M u

configureUnfoldableDefs continuous_function_at sequence_tendsto increasing_seq is_supremum

section Subset
variable {α : Type*}

/- The Mathlib definition of `Set.Subset` uses a strict-implicit
argument which confuses Verbose Lean. So let us replace it. -/

protected def Verbose.Spanish.Subset (s₁ s₂ : Set α) :=
  ∀ x, x ∈ s₁ → x ∈ s₂

instance (priority := high) Verbose.Spanish.hasSubset : HasSubset (Set α) :=
  ⟨Verbose.Spanish.Subset⟩

end Subset

open Verbose.Spanish

lemma le_of_abs_le' {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] {x y : α} : |x| ≤ y → -y ≤ x := fun h ↦ abs_le.1 h |>.1

configureAnonymousFactSplittingLemmas le_le_of_abs_le le_le_of_max_le le_of_max_le_left le_of_max_le_right le_of_abs_le le_of_abs_le'

configureAnonymousGoalSplittingLemmas LogicIntros AbsIntros Set.Subset.antisymm

useDefaultDataProviders

useDefaultSuggestionProviders
