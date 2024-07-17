import Verbose.English.ExampleLib

Exercise "Continuity implies sequential continuity"
  Given: (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
  Assume: (hu : u converges to x₀) (hf : f is continuous at x₀)
  Conclusion: (f ∘ u) converges to f x₀
Proof:
  Let's prove that ∀ ε > 0, ∃ N, ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Fix ε > 0
  By hf applied to ε using that ε > 0 we get δ such that
    (δ_pos : δ > 0) and (Hf : ∀ x, |x - x₀| ≤ δ ⇒ |f x - f x₀| ≤ ε)
  By hu applied to δ using that δ > 0 we get N such that Hu : ∀ n ≥ N, |u n - x₀| ≤ δ
  Let's prove that N works : ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Fix n ≥ N
  By Hf applied to u n it suffices to prove |u n - x₀| ≤ δ
  We conclude by Hu applied to n using that n ≥ N
QED

-- Variation without referring to any assumption label
Exercise "Continuity implies sequential continuity"
  Given: (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
  Assume: (hu : u converges to x₀) (hf : f is continuous at x₀)
  Conclusion: (f ∘ u) converges to f x₀
Proof:
  Let's prove that ∀ ε > 0, ∃ N, ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Fix ε > 0
  Since f is continuous at x₀ and ε > 0 we get δ such that
    (δ_pos : δ > 0) and (Hf : ∀ x, |x - x₀| ≤ δ ⇒ |f x - f x₀| ≤ ε)
  Since u converges to x₀ and δ > 0 we get N such that Hu : ∀ n ≥ N, |u n - x₀| ≤ δ
  Let's prove that N works : ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Fix n ≥ N
  Since ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε it suffices to prove that |u n - x₀| ≤ δ
  Since ∀ n ≥ N, |u n - x₀| ≤ δ and n ≥ N we conclude that |u n - x₀| ≤ δ
  /- -- Forward reasoning variation
  Since ∀ n ≥ N, |u n - x₀| ≤ δ and n ≥ N we get h : |u n - x₀| ≤ δ
  Since ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε and |u n - x₀| ≤ δ we conclude that |f (u n) - f x₀| ≤ ε -/
QED

Example "Constant sequences converge."
  Given: (u : ℕ → ℝ) (l : ℝ)
  Assume: (h : ∀ n, u n = l)
  Conclusion: u converges to l
Proof:
  Fix ε > 0
  Let's prove that ∃ N, ∀ n ≥ N, |u n - l| ≤ ε
  Let's prove that 0 works
  Fix n ≥ 0
  Calc |u n - l| = |l - l| by We rewrite using h
   _             = 0       by We compute
   _             ≤ ε       by We conclude by ε_pos
QED

Example "A sequence converging to a positive limit is ultimately positive."
  Given: (u : ℕ → ℝ) (l : ℝ)
  Assume: (hl : l > 0) (h :u converges to l)
  Conclusion: ∃ N, ∀ n ≥ N, u n ≥ l/2
Proof:
  By h applied to l/2 using that l/2 > 0 we get N such that hN : ∀ n ≥ N, |u n - l| ≤ l/2
  Let's prove that N works
  Fix n ≥ N
  By hN applied to n using that n ≥ N we get hN' : |u n - l| ≤ l/2
  By hN' we get (h₁ : -(l/2) ≤ u n - l) (h₂ : u n - l ≤ l/2)
  We conclude by h₁
QED


Example "Addition of convergent sequences."
  Given: (u v : ℕ → ℝ) (l l' : ℝ)
  Assume: (hu : u converges to l) (hv : v converges to l')
  Conclusion: (u + v) converges to (l + l')
Proof:
  Fix ε > 0
  By hu applied to ε/2 using that ε/2 > 0 we get N₁
      such that (hN₁ : ∀ n ≥ N₁, |u n - l| ≤ ε / 2)
  By hv applied to ε/2 using that ε/2 > 0 we get N₂
      such that (hN₂ : ∀ n ≥ N₂, |v n - l'| ≤ ε / 2)
  Let's prove that max N₁ N₂ works
  Fix n ≥ max N₁ N₂
  By n_ge we get (hn₁ : N₁ ≤ n) (hn₂ : N₂ ≤ n)
  Fact fact₁ : |u n - l| ≤ ε/2
    from hN₁ applied to n using hn₁
  Fact fact₂ : |v n - l'| ≤ ε/2
    from hN₂ applied to n using hn₂
  Calc
  |(u + v) n - (l + l')| = |(u n - l) + (v n - l')| by We compute
                     _ ≤ |u n - l| + |v n - l'|     by We apply abs_add
                     _ ≤  ε/2 + ε/2                 by We combine [fact₁, fact₂]
                     _ =  ε                         by We compute
QED

Example "The squeeze theorem."
  Given: (u v w : ℕ → ℝ) (l : ℝ)
  Assume: (hu : u converges to l) (hw : w converges to l)
    (h : ∀ n, u n ≤ v n)
    (h' : ∀ n, v n ≤ w n)
  Conclusion: v converges to l
Proof:
  Let's prove that ∀ ε > 0, ∃ N, ∀ n ≥ N, |v n - l| ≤ ε
  Fix ε > 0
  Since u converges to l and ε > 0 we get N such that hN : ∀ n ≥ N, |u n - l| ≤ ε
  Since w converges to l and ε > 0 we get N' such that hN' : ∀ n ≥ N', |w n - l| ≤ ε
  Let's prove that max N N' works : ∀ n ≥ max N N', |v n - l| ≤ ε
  Fix n ≥ max N N'
  Since n ≥ max N N' we get (hn : n ≥ N) and (hn' : n ≥ N')
  Since ∀ n ≥ N, |u n - l| ≤ ε and n ≥ N we get
   (hNl : -ε ≤ u n - l) and (hNd : u n - l ≤ ε)
  Since ∀ n ≥ N', |w n - l| ≤ ε and n ≥ N' we get
    (hN'l : -ε ≤ w n - l) and (hN'd : w n - l ≤ ε)
  Let's prove that |v n - l| ≤ ε
  Let's first prove that -ε ≤ v n - l
  Calc -ε ≤ u n - l by assumption
      _   ≤ v n - l since u n ≤ v n
  Let's now prove that v n - l ≤ ε
  Calc v n - l ≤ w n - l  since v n ≤ w n
      _        ≤ ε        by assumption
QED

Example "A reformulation of the convergence definition."
  Given: (u : ℕ → ℝ) (l : ℝ)
  Assume:
  Conclusion: (u converges to l) ⇔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε
Proof:
  Let's first prove that (u converges to l) ⇒ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε
  Assume hyp : u converges to l
  Fix ε > 0
  By hyp applied to ε/2 using that ε/2 > 0 we get N
      such that hN : ∀ n ≥ N, |u n - l| ≤ ε / 2
  Let's prove that N works
  Fix n ≥ N
  Calc |u n - l| ≤ ε/2  from hN applied to n using that n ≥ N
       _         < ε    since ε > 0
  Let's now prove that (∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε) ⇒ u converges to l
  Assume hyp : ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε
  Fix ε > 0
  By hyp applied to ε using that ε > 0 we get N such that hN : ∀ n ≥ N, |u n - l| < ε
  Let's prove that N works
  Fix n ≥ N
  We conclude by hN applied to n using that n ≥ N
QED


Example "Uniqueness of limits."
  Given: (u : ℕ → ℝ) (l l' : ℝ)
  Assume: (h : u converges to l) (h': u converges to l')
  Conclusion: l = l'
Proof:
  By eq_of_forall_dist_le it suffices to prove that ∀ ε > 0, |l - l'| ≤ ε
  Fix ε > 0
  By h applied to ε/2 using that ε/2 > 0 we get N
      such that hN : ∀ n ≥ N, |u n - l| ≤ ε / 2
  By h' applied to  ε/2 using that ε/2 > 0 we get N'
      such that hN' : ∀ n ≥ N', |u n - l'| ≤ ε / 2
  By hN applied to max N N' using le_max_left _ _
     we get hN₁ : |u (max N N') - l| ≤ ε / 2
  By hN' applied to max N N' using le_max_right _ _
    we get hN'₁ : |u (max N N') - l'| ≤ ε / 2
  Calc |l - l'| = |(l-u (max N N')) + (u (max N N') -l')|  by We compute
  _             ≤ |l - u (max N N')| + |u (max N N') - l'| by We apply abs_add
  _             = |u (max N N') - l| + |u (max N N') - l'| by We rewrite using abs_sub_comm
  _             ≤ ε                                        by We combine [hN₁, hN'₁]
QED

Example "An increasing sequence having a finite supremum tends to it."
  Given: (u : ℕ → ℝ) (M : ℝ)
  Assume: (h : M is a supremum of u) (h' : u is increasing)
  Conclusion: u converges to M
Proof:
  Fix ε > 0
  By h we get (inf_M : ∀ (n : ℕ), u n ≤ M)
                   (sup_M_ep : ∀ ε > 0, ∃ (n₀ : ℕ), u n₀ ≥ M - ε)
  By sup_M_ep applied to ε using that ε > 0 we get n₀ such that (hn₀ : u n₀ ≥ M - ε)
  Let's prove that n₀ works : ∀ n ≥ n₀, |u n - M| ≤ ε
  Fix n ≥ n₀
  By inf_M applied to n we get (inf_M' : u n ≤ M)
  Let's first prove that -ε ≤ u n - M
  · By h' applied to n₀ and n using n_ge we get h'' : u n₀ ≤ u n
    We combine [h'', hn₀]
  Let's now prove that u n - M ≤ ε
  ·  We combine [inf_M', ε_pos]
QED
