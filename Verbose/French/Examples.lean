import Mathlib.Topology.MetricSpace.Basic
import Verbose.French.All

def continuous_function_at (f : ℝ → ℝ) (x₀ : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

def sequence_tendto (u : ℕ → ℝ) (l : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

notation3:50 f:80 " est continue en " x₀ => continuous_function_at f x₀
notation3:50 u:80 " tend vers " l => sequence_tendto u l

Exercice "La continuité implique la continuité séquentielle."
  Données : (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
  Hypothèses : (hu : u tend vers x₀) (hf : f est continue en x₀)
  Conclusion : f ∘ u tend vers f x₀
Démonstration :
  Montrons que ∀ ε > 0, ∃ N, ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Soit ε > 0
  Par hf appliqué à ε en utilisant ε_pos on obtient δ tel que
    (δ_pos : δ > 0) (Hf : ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε)
  Par hu appliqué à δ en utilisant δ_pos on obtient N tel que Hu : ∀ n ≥ N, |u n - x₀| ≤ δ
  Montrons que N works : ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Soit n ≥ N
  Par Hf appliqué à u n il suffit de montrer |u n - x₀| ≤ δ
  On conclut par Hu appliqué à n en utilisant n_ge
QED

Exemple "Les suites constantes convergent."
  Données : (u : ℕ → ℝ) (l : ℝ)
  Hypothèses : (h : ∀ n, u n = l)
  Conclusion : u tend vers l
Démonstration :
  Soit ε > 0
  Montrons que ∃ N, ∀ n ≥ N, |u n - l| ≤ ε
  Montrons que 0 works
  Soit n ≥ 0
  calc |u n - l| = |l - l| := by On réécrit via h
   _             = 0       := by On calcule
   _             ≤ ε       := by On conclut par ε_pos
QED

Exemple "Une suite tendant vers une limite strictement positive est ultimement strictement positive."
  Données : (u : ℕ → ℝ) (l : ℝ)
  Hypothèses : (hl : l > 0) (h :u tend vers l)
  Conclusion : ∃ N, ∀ n ≥ N, u n ≥ l/2
Démonstration :
  Par h appliqué à [l/2, half_pos hl] on obtient N (hN : ∀ n ≥ N, |u n - l| ≤ l / 2)
  Montrons que N works
  Soit n ≥ N
  Par hN appliqué à n en utilisant (n_ge : n ≥ N) on obtient hN' : |u n - l| ≤ l / 2
  Par hN' on obtient (h₁ : -(l / 2) ≤ u n - l) (h₂ : u n - l ≤ l / 2)
  On conclut par h₁
QED

Exemple "Addition de suites convergentes."
  Données : (u v : ℕ → ℝ) (l l': ℝ)
  Hypothèses : (hu : u tend vers l) (hv : v tend vers l')
  Conclusion : (u + v) tend vers (l + l')
Démonstration :
  Soit ε > 0
  Par hu appliqué à [ε/2, half_pos ε_pos] on obtient N₁
      tel que (hN₁ : ∀ (n : ℕ), n ≥ N₁ → |u n - l| ≤ ε / 2)
  Par hv appliqué à [ε/2, half_pos ε_pos] on obtient N₂
      tel que (hN₂ : ∀ n ≥ N₂, |v n - l'| ≤ ε / 2)
  Montrons que max N₁ N₂ works
  Soit n ≥ max N₁ N₂
  Par n_ge on obtient (hn₁ : N₁ ≤ n) (hn₂ : N₂ ≤ n)
  Fait fait₁ : |u n - l|  ≤ ε/2 par hN₁ appliqué à n en utilisant hn₁
  Fait fait₂ : |v n - l'| ≤ ε/2 par hN₂ appliqué à n en utilisant hn₂
  calc
  |(u + v) n - (l + l')| = |(u n - l) + (v n - l')| := by On calcule
                     _ ≤ |u n - l| + |v n - l'| := by On applique abs_add
                     _ ≤  ε/2 + ε/2             := by On combine [fait₁, fait₂]
                     _ =  ε                     := by On calcule
 QED

Exemple "Le théorème des gendarmes."
  Données : (u v w : ℕ → ℝ) (l : ℝ)
  Hypothèses : (hu : u tend vers l) (hw : w tend vers l)
    (h : ∀ n, u n ≤ v n)
    (h' : ∀ n, v n ≤ w n)
  Conclusion : v tend vers l
Démonstration :
  Soit ε > 0
  Par hu appliqué à ε en utilisant ε_pos on obtient N tel que (hN : ∀ n ≥ N, |u n - l| ≤ ε)
  Par hw appliqué à ε en utilisant ε_pos on obtient N' tel que (hN' : ∀ n ≥ N', |w n - l| ≤ ε)
  Montrons que max N N' works
  Soit n ≥ max N N'
  Par (n_ge : n ≥ max N N') on obtient (hn : N ≤ n) (hn' : N' ≤ n)
  Par hN appliqué à [n, hn] on obtient hN₁ : |u n - l| ≤ ε
  Par hN' appliqué à [n, hn'] on obtient hN'₁ : |w n - l| ≤ ε
  Par h appliqué à n on obtient h₁ : u n ≤ v n
  Par h' appliqué à n on obtient h'₁ : v n ≤ w n
  On réécrit via abs_le partout
  Par hN₁ on obtient (hNl : -ε ≤ u n - l) hNd
  Par hN'₁ on obtient hN'l (hN'd : w n - l ≤ ε)
  Montrons d'abord que -ε ≤ v n - l
  calc -ε ≤ u n - l := by On conclut par hNl
      _ ≤ v n - l := by On conclut par h₁
  Montrons maintenant que v n - l ≤ ε
  calc v n - l ≤ w n - l := by On conclut par h'₁
      _ ≤ ε := by On conclut par hN'd
QED

Exemple "Une reformulation de la définition de limite."
  Données : (u : ℕ → ℝ) (l : ℝ)
  Hypothèses :
  Conclusion : (u tend vers l) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε
Démonstration :
  Montrons d'abord que (u tend vers l) → ∀ (ε : ℝ), ε > 0 → (∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → |u n - l| < ε)
  Supposons hyp : u tend vers l
  Soit ε > 0
  Par hyp appliqué à ε/2 en utilisant half_pos ε_pos on obtient N
      tel que hN : ∀ (n : ℕ), n ≥ N → |u n - l| ≤ ε / 2
  Montrons que N works
  Soit n ≥ N
  calc |u n - l| ≤ ε/2 := by On conclut par hN appliqué à [n, n_ge]
       _       < ε := by On conclut par ε_pos
  Montrons maintenant que (∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε) → u tend vers l
  Supposons hyp : ∀ (ε : ℝ), ε > 0 → (∃ N, ∀ n ≥ N, |u n - l| < ε)
  Soit ε > 0
  Par hyp appliqué à ε en utilisant ε_pos on obtient N tel que hN : ∀ n ≥ N, |u n - l| < ε
  Montrons que N works
  Soit n ≥ N
  On conclut par hN appliqué à n en utilisant n_ge
QED

/-
example : u tend vers l → u tend vers l' → l = l' := by
  Supposons (hl : u tend vers l) (hl' : u tend vers l')
  Par eq_of_forall_dist_le il suffit de montrer que ∀ (ε : ℝ), ε > 0 → |l - l'| ≤ ε
  Soit ε > 0
  Par hl appliqué à [ε/2, half_pos ε_pos] on obtient N
      tel que hN : ∀ (n : ℕ), n ≥ N → |u n - l| ≤ ε / 2
  Par hl' appliqué à [ε/2, half_pos ε_pos] on obtient N'
      tel que hN' : ∀ n ≥ N', |u n - l'| ≤ ε / 2
  Par hN appliqué à [max N N', le_max_left _ _]
     on obtient hN₁ : |u (max N N') - l| ≤ ε / 2
  Par hN' appliqué à [max N N', le_max_right _ _]
    on obtient hN'₁ : |u (max N N') - l'| ≤ ε / 2
  calc |l - l'| = |(l-u (max N N')) + (u (max N N') -l')| := by On calcule
  _ ≤ |l - u (max N N')| + |u (max N N') - l'| := by We apply abs_add
  _ =  |u (max N N') - l| + |u (max N N') - l'| := by On réécrit en utilisant abs_sub_comm
  _ ≤ ε/2 + ε/2 := by We combine [hN₁, hN'₁]
  _ = ε := by On calcule
 -/

def croissante (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

notation3 u " est croissante" => croissante u

def est_supremum (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

notation3 M " est un supremum de " u => est_supremum M u

Exemple "Une suite croissante ayant un supremum fini tends vers lui."
  Données : (u : ℕ → ℝ) (M : ℝ)
  Hypothèses : (h : M est un supremum de u) (h' : u est croissante)
  Conclusion : u tend vers M
Démonstration :
  Soit ε > 0
  Par h on obtient (inf_M : ∀ (n : ℕ), u n ≤ M)
                   (sup_M_ep : ∀ ε > 0, ∃ (n₀ : ℕ), u n₀ ≥ M - ε)
  Par sup_M_ep appliqué à ε en utilisant ε_pos on obtient n₀ tel que (hn₀ : u n₀ ≥ M - ε)
  Montrons que n₀ works : ∀ n ≥ n₀, |u n - M| ≤ ε
  Soit n ≥ n₀
  Par inf_M appliqué à n on obtient (inf_M' : u n ≤ M)
  Montrons d'abord que -ε ≤ u n - M
  · Par h' appliqué à [n₀, n, n_ge] on obtient h'' : u n₀ ≤ u n
    On combine [h'', hn₀]
  Montrons maintenant que u n - M ≤ ε
  ·  On combine [inf_M', ε_pos]
QED
