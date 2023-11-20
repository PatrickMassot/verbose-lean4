import Verbose.French.ExampleLib

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
  Montrons que N convient : ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
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
  Montrons que 0 convient
  Soit n ≥ 0
  Calc |u n - l| = |l - l| car On réécrit via h
   _             = 0       car On calcule
   _             ≤ ε       car On conclut par ε_pos
QED

Exemple "Une suite tendant vers une limite strictement positive est ultimement strictement positive."
  Données : (u : ℕ → ℝ) (l : ℝ)
  Hypothèses : (hl : l > 0) (h :u tend vers l)
  Conclusion : ∃ N, ∀ n ≥ N, u n ≥ l/2
Démonstration :
  Par h appliqué à [l/2, half_pos hl] on obtient N (hN : ∀ n ≥ N, |u n - l| ≤ l / 2)
  Montrons que N convient
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
  Montrons que max N₁ N₂ convient
  Soit n ≥ max N₁ N₂
  Par n_ge on obtient (hn₁ : N₁ ≤ n) (hn₂ : N₂ ≤ n)
  Fait fait₁ : |u n - l|  ≤ ε/2 par hN₁ appliqué à n en utilisant hn₁
  Fait fait₂ : |v n - l'| ≤ ε/2 par hN₂ appliqué à n en utilisant hn₂
  Calc
  |(u + v) n - (l + l')| = |(u n - l) + (v n - l')| car On calcule
                     _   ≤ |u n - l| + |v n - l'|   car On applique abs_add
                     _   ≤  ε                       car On combine [fait₁, fait₂]
 QED

Exemple "Le théorème des gendarmes."
  Données : (u v w : ℕ → ℝ) (l : ℝ)
  Hypothèses :
    (hu : u tend vers l) (hw : w tend vers l)
    (h : ∀ n, u n ≤ v n) (h' : ∀ n, v n ≤ w n)
  Conclusion : v tend vers l
Démonstration :
  Soit ε > 0
  Montrons que ∃ N, ∀ n ≥ N, |v n - l| ≤ ε
  Par hu appliqué à ε en utilisant ε_pos on obtient N tel que hN : ∀ n ≥ N, |u n - l| ≤ ε
  Par hw appliqué à ε en utilisant ε_pos on obtient N' tel que hN' : ∀ n ≥ N', |w n - l| ≤ ε
  Montrons que max N N' convient : ∀ n ≥ max N N', |v n - l| ≤ ε
  Soit n ≥ max N N'
  Par (n_ge : n ≥ max N N') on obtient (hn : N ≤ n) (hn' : N' ≤ n)
  Par hN appliqué à n en utilisant hn on obtient
    (hNl : -ε ≤ u n - l) (hNd : u n - l ≤ ε)
  Par hN' appliqué à n en utilisant hn' on obtient
    (hN'l : -ε ≤ w n - l) (hN'd : w n - l ≤ ε)
  Montrons d'abord que -ε ≤ v n - l
  Calc -ε ≤ u n - l car On conclut par hNl
      _   ≤ v n - l car On conclut par h appliqué à n
  Montrons maintenant que v n - l ≤ ε
  Calc v n - l ≤ w n - l car On conclut par h' appliqué à n
      _        ≤ ε       car On conclut par hN'd
QED

Exemple "Une reformulation de la définition de limite."
  Données : (u : ℕ → ℝ) (l : ℝ)
  Hypothèses :
  Conclusion : (u tend vers l) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε
Démonstration :
  Montrons d'abord que
    (u tend vers l) → ∀ (ε : ℝ), ε > 0 → (∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → |u n - l| < ε)
  Supposons hyp : u tend vers l
  Soit ε > 0
  Par hyp appliqué à ε/2 en utilisant half_pos ε_pos on obtient N
      tel que hN : ∀ (n : ℕ), n ≥ N → |u n - l| ≤ ε / 2
  Montrons que N convient
  Soit n ≥ N
  Calc |u n - l| ≤ ε/2 car On conclut par hN appliqué à n en utilisant n_ge
       _         < ε   car On conclut par ε_pos
  Montrons maintenant que (∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε) → u tend vers l
  Supposons hyp : ∀ (ε : ℝ), ε > 0 → (∃ N, ∀ n ≥ N, |u n - l| < ε)
  Soit ε > 0
  Par hyp appliqué à ε en utilisant ε_pos on obtient N tel que hN : ∀ n ≥ N, |u n - l| < ε
  Montrons que N convient
  Soit n ≥ N
  On conclut par hN appliqué à n en utilisant n_ge
QED

Exemple "Unicité de la limite d'une suite."
  Données : (u : ℕ → ℝ) (l l': ℝ)
  Hypothèses : (h : u tend vers l) (h': u tend vers l')
  Conclusion : l = l'
Démonstration :
  Par eq_of_forall_dist_le il suffit de montrer que ∀ (ε : ℝ), ε > 0 → |l - l'| ≤ ε
  Soit ε > 0
  Par h appliqué à [ε/2, half_pos ε_pos] on obtient N
      tel que hN : ∀ (n : ℕ), n ≥ N → |u n - l| ≤ ε / 2
  Par h' appliqué à [ε/2, half_pos ε_pos] on obtient N'
      tel que hN' : ∀ n ≥ N', |u n - l'| ≤ ε / 2
  Par hN appliqué à [max N N', le_max_left _ _]
     on obtient hN₁ : |u (max N N') - l| ≤ ε / 2
  Par hN' appliqué à [max N N', le_max_right _ _]
    on obtient hN'₁ : |u (max N N') - l'| ≤ ε / 2
  Calc |l - l'| = |(l-u (max N N')) + (u (max N N') -l')|  car On calcule
    _           ≤ |l - u (max N N')| + |u (max N N') - l'| car On applique abs_add
    _           = |u (max N N') - l| + |u (max N N') - l'| car On réécrit via abs_sub_comm
    _           ≤ ε                                        car On combine [hN₁, hN'₁]
QED

Exemple "Une suite croissante ayant un supremum fini tends vers lui."
  Données : (u : ℕ → ℝ) (M : ℝ)
  Hypothèses : (h : M est un supremum de u) (h' : u est croissante)
  Conclusion : u tend vers M
Démonstration :
  Soit ε > 0
  Par h on obtient (inf_M : ∀ (n : ℕ), u n ≤ M)
                   (sup_M_ep : ∀ ε > 0, ∃ (n₀ : ℕ), u n₀ ≥ M - ε)
  Par sup_M_ep appliqué à ε en utilisant ε_pos on obtient n₀ tel que (hn₀ : u n₀ ≥ M - ε)
  Montrons que n₀ convient : ∀ n ≥ n₀, |u n - M| ≤ ε
  Soit n ≥ n₀
  Par inf_M appliqué à n on obtient (inf_M' : u n ≤ M)
  Montrons d'abord que -ε ≤ u n - M
  · Par h' appliqué à [n₀, n, n_ge] on obtient h'' : u n₀ ≤ u n
    On combine [h'', hn₀]
  Montrons maintenant que u n - M ≤ ε
  ·  On combine [inf_M', ε_pos]
QED
