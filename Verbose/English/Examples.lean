import Mathlib.Topology.MetricSpace.Basic
import Verbose.English.All

def continuous_function_at (f : ℝ → ℝ) (x₀ : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

def sequence_tendsto (u : ℕ → ℝ) (l : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

/-
If f is continuous at x₀ and the sequence u tends to x₀ then the sequence f ∘ u, sending n to
f (u n) tends to f x₀
-/
example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
    (hu : sequence_tendsto u x₀) (hf : continuous_function_at f x₀) :
    sequence_tendsto (f ∘ u) (f x₀) := by
  Let's prove that ∀ ε > 0, ∃ N, ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Fix ε > 0
  By hf applied to ε using ε_pos we get δ such that
    (δ_pos : δ > 0) (Hf : ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε)
  By hu applied to δ using δ_pos we get N such that Hu : ∀ n ≥ N, |u n - x₀| ≤ δ
  Let's prove that N works : ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Fix n ≥ N
  By Hf applied to u n it suffices to prove |u n - x₀| ≤ δ
  We conclude by Hu applied to n using n_ge

variable (u v w : ℕ → ℝ) (l l' : ℝ)

-- If u is constant with value l, then u tends to l
example : (∀ n, u n = l) → sequence_tendsto u l := by
  Assume h : ∀ (n : ℕ), u n = l
  Fix ε > 0
  Let's prove that ∃ N, ∀ n ≥ N, |u n - l| ≤ ε
  Let's prove that 0 works
  Fix n ≥ 0
  We rewrite using h
  We compute
  We conclude by ε_pos

lemma ge_max_iff {α : Type*} [LinearOrder α] {a b c : α} : c ≥ max a b ↔ a ≤ c ∧ b ≤ c :=
max_le_iff

example (hl : l > 0) : sequence_tendsto u l → ∃ N, ∀ n ≥ N, u n ≥ l/2 := by
  Assume h : sequence_tendsto u l
  By h applied to [l/2, half_pos hl] we get N (hN : ∀ n ≥ N, |u n - l| ≤ l / 2)
  Let's prove that N works
  Fix n ≥ N
  By hN applied to n using (n_ge : n ≥ N) we get hN' : |u n - l| ≤ l / 2
  We rewrite using abs_le at hN' which becomes -(l / 2) ≤ u n - l ∧ u n - l ≤ l / 2
  We conclude by hN'

/-
example (hu : sequence_tendsto u l) (hv : sequence_tendsto v l') :
sequence_tendsto (u + v) (l + l') := by
  Fix ε > 0
  By hu applied to [ε/2, half_pos ε_pos] we get N₁
      such that (hN₁ : ∀ (n : ℕ), n ≥ N₁ → |u n - l| ≤ ε / 2)
  By hv applied to [ε/2, half_pos ε_pos] we get N₂
      such that (hN₂ : ∀ n ≥ N₂, |v n - l'| ≤ ε / 2)
  Let's prove that max N₁ N₂ works
  Fix n ≥ max N₁ N₂
  We rewrite using ge_max_iff at n_ge --which becomes n ≥ N₁ ∧ n ≥ N₂
  By n_ge we get (hn₁ : N₁ ≤ n) (hn₂ : N₂ ≤ n)
  Fact fait₁ : |u n - l| ≤ ε/2
    We apply hN₁
  Fact fait₂ : |v n - l'| ≤ ε/2
    We conclude by hN₂ applied to [n, hn₂]
  calc
  |(u + v) n - (l + l')| = |(u n - l) + (v n - l')| := by We compute
                     _ ≤ |u n - l| + |v n - l'| := by We apply abs_add
                     _ ≤  ε/2 + ε/2             := by We combine [fait₁, fait₂]
                     _ =  ε                     := by We compute
 -/

example (hu : sequence_tendsto u l) (hw : sequence_tendsto w l)
(h : ∀ n, u n ≤ v n)
(h' : ∀ n, v n ≤ w n) : sequence_tendsto v l := by
  Fix ε > 0
  By hu applied to [ε, ε_pos] we get N such that (hN : ∀ n ≥ N, |u n - l| ≤ ε)
  By hw applied to [ε, ε_pos] we get N' such that (hN' : ∀ n ≥ N', |w n - l| ≤ ε)
  Let's prove that max N N' works
  Fix n ≥ max N N'
  We rewrite using [ge_max_iff] at n_ge
  By n_ge we get (hn : N ≤ n) (hn' : N' ≤ n)
  By hN applied to [n, hn] we get (hN₁ : |u n - l| ≤ ε)
  By hN' applied to [n, hn'] we get (hN'₁ : |w n - l| ≤ ε)
  By h applied to n we get (h₁ : u n ≤ v n)
  By h' applied to n we get (h'₁ : v n ≤ w n)
  We rewrite using abs_le everywhere
  By hN₁ we get (hNl : -ε ≤ u n - l) hNd
  By hN'₁ we get hN'l (hN'd : w n - l ≤ ε)
  Let's first prove that -ε ≤ v n - l
  calc -ε ≤ u n - l := by We conclude by hNl
      _ ≤ v n - l := by We conclude by h₁
  Let's prove that v n - l ≤ ε
  calc v n - l ≤ w n - l := by We conclude by h'₁
      _ ≤ ε := by We conclude by hN'd

example (u l) : sequence_tendsto u l ↔
 ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε := by
  Let's prove that sequence_tendsto u l → ∀ (ε : ℝ), ε > 0 → (∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → |u n - l| < ε)
  Assume hyp : sequence_tendsto u l
  Fix ε > 0
  By hyp applied to ε/2 using half_pos ε_pos we get N
      such that hN : ∀ (n : ℕ), n ≥ N → |u n - l| ≤ ε / 2
  Let's prove that N works
  Fix n ≥ N
  calc |u n - l| ≤ ε/2 := by We conclude by hN applied to [n, n_ge]
       _       < ε := by We conclude by ε_pos

  Assume hyp : ∀ (ε : ℝ), ε > 0 → (∃ N, ∀ n ≥ N, |u n - l| < ε)
  Fix ε > 0
  By hyp applied to [ε, ε_pos] we get N such that hN : ∀ n ≥ N, |u n - l| < ε
  Let's prove that N works
  Fix n ≥ N
  We conclude by hN applied to n using n_ge
/-
example : sequence_tendsto u l → sequence_tendsto u l' → l = l' := by
  Assume (hl : sequence_tendsto u l) (hl' : sequence_tendsto u l')
  By eq_of_forall_dist_le it suffices to prove that ∀ (ε : ℝ), ε > 0 → |l - l'| ≤ ε
  Fix ε > 0
  By hl applied to [ε/2, half_pos ε_pos] we get N
      such that hN : ∀ (n : ℕ), n ≥ N → |u n - l| ≤ ε / 2
  By hl' applied to [ε/2, half_pos ε_pos] we get N'
      such that hN' : ∀ n ≥ N', |u n - l'| ≤ ε / 2
  By hN applied to [max N N', le_max_left _ _]
     we get hN₁ : |u (max N N') - l| ≤ ε / 2
  By hN' applied to [max N N', le_max_right _ _]
    we get hN'₁ : |u (max N N') - l'| ≤ ε / 2
  calc |l - l'| = |(l-u (max N N')) + (u (max N N') -l')| := by We compute
  _ ≤ |l - u (max N N')| + |u (max N N') - l'| := by We apply abs_add
  _ =  |u (max N N') - l| + |u (max N N') - l'| := by We rewrite using abs_sub_comm
  _ ≤ ε/2 + ε/2 := by We combine [hN₁, hN'₁]
  _ = ε := by We compute
 -/
def increasing (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

def is_supremum (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

example (M : ℝ) (h : is_supremum M u) (h' : increasing u) :
sequence_tendsto u M := by
  Fix ε > 0
  By h we get (inf_M : ∀ (n : ℕ), u n ≤ M)
                   (sup_M_ep : ∀ ε > 0, ∃ (n₀ : ℕ), u n₀ ≥ M - ε)
  By sup_M_ep applied to [ε, ε_pos] we get n₀ such that (hn₀ : u n₀ ≥ M - ε)
  Let's prove that n₀ works : ∀ n ≥ n₀, |u n - M| ≤ ε
  Fix n ≥ n₀
  By inf_M applied to n we get (inf_M' : u n ≤ M)

  We rewrite using [abs_le]
  Let's first prove that -ε ≤ u n - M
  · By h' applied to [n₀, n, n_ge] we get h'' : u n₀ ≤ u n
    We combine [h'', hn₀]
  Let's prove that u n - M ≤ ε
  ·  We combine [inf_M', ε_pos]
