import Mathlib.Topology.MetricSpace.Basic
import Verbose.French.All

@[unfoldable_def]
def continue_en (f : ℝ → ℝ) (x₀ : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

@[unfoldable_def]
def tend_vers (u : ℕ → ℝ) (l : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

notation3:50 f:80 " est continue en " x₀ => continue_en f x₀
notation3:50 u:80 " tend vers " l => tend_vers u l

@[unfoldable_def]
def croissante (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

notation3 u " est croissante" => croissante u

@[unfoldable_def]
def est_sup (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

notation3 M " est un supremum de " u => est_sup M u
