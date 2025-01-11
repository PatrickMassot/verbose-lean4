import Mathlib.Topology.MetricSpace.Basic
import Verbose.English.All

def continuous_function_at (f : ℝ → ℝ) (x₀ : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

def sequence_tendsto (u : ℕ → ℝ) (l : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

notation3:50 f:80 " is " "continuous " " at " x₀ => continuous_function_at f x₀
notation3:50 u:80 " converges " "to " l => sequence_tendsto u l

def increasing_seq (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

notation3 u " is " "increasing" => increasing_seq u

def is_supremum (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

syntax term " is " &"a " "supremum " "of " term : term
macro_rules
  | `($M is a supremum of $u) => `(is_supremum $M $u)
@[app_unexpander is_supremum]
def is_supremum.unexpand : Lean.PrettyPrinter.Unexpander
  | `($(_) $M $u) => `($M is a supremum of $u)
  | _ => throw ()


configureUnfoldableDefs continuous_function_at sequence_tendsto increasing_seq is_supremum

section Subset
variable {α : Type*}

/- The Mathlib definition of `Set.Subset` uses a strict-implicit
argument which confuses Verbose Lean. So let us replace it. -/

protected def Verbose.English.Subset (s₁ s₂ : Set α) :=
  ∀ x, x ∈ s₁ → x ∈ s₂

instance (priority := high) Verbose.English.hasSubset : HasSubset (Set α) :=
  ⟨Verbose.English.Subset⟩

end Subset

open Verbose.English

configureAnonymousFactSplittingLemmas le_le_of_abs_le le_le_of_max_le

configureAnonymousGoalSplittingLemmas LogicIntros AbsIntros Set.Subset.antisymm

useDefaultDataProviders

useDefaultSuggestionProviders
