import Verbose.French.ExampleLib
import Verbose.French.Statements

set_option linter.unusedTactic false

Exercice "La continuité implique la continuité séquentielle."
  Données : (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
  Hypothèses : (hu : u tend vers x₀) (hf : f est continue en x₀)
  Conclusion : f ∘ u tend vers f x₀
Démonstration :
  Montrons que ∀ ε > 0, ∃ N, ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Soit ε > 0
  Par hf appliqué à ε en utilisant que ε > 0 on obtient δ tel que
    (δ_pos : δ > 0) et (Hf : ∀ x, |x - x₀| ≤ δ ⇒ |f x - f x₀| ≤ ε)
  Par hu appliqué à δ en utilisant que δ > 0 on obtient N tel que Hu : ∀ n ≥ N, |u n - x₀| ≤ δ
  Montrons que N convient : ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Soit n ≥ N
  Par Hf appliqué à u n il suffit de montrer |u n - x₀| ≤ δ
  On conclut par Hu appliqué à n en utilisant que n ≥ N
QED

-- Variante sans se référer aux noms des hypothèses
Exercice "La continuité implique la continuité séquentielle."
  Données : (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
  Hypothèses : (hu : u tend vers x₀) (hf : f est continue en x₀)
  Conclusion : f ∘ u tend vers f x₀
Démonstration :
  Montrons que ∀ ε > 0, ∃ N, ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Soit ε > 0
  Comme f est continue en x₀ et ε > 0 on obtient δ tel que
    δ > 0 et ∀ x, |x - x₀| ≤ δ ⇒ |f x - f x₀| ≤ ε
  Comme u tend vers x₀ et δ > 0 on obtient N tel que ∀ n ≥ N, |u n - x₀| ≤ δ
  Montrons que N convient : ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Soit n ≥ N
  Comme ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε il suffit de montrer que |u n - x₀| ≤ δ
  Comme ∀ n ≥ N, |u n - x₀| ≤ δ et n ≥ N on conclut que |u n - x₀| ≤ δ
  /- -- Variante vers l'avant
  Comme ∀ n ≥ N, |u n - x₀| ≤ δ et n ≥ N on obtient que |u n - x₀| ≤ δ
  Comme ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε et |u n - x₀| ≤ δ on conclut que |f (u n) - f x₀| ≤ ε -/
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
  Calc |u n - l| = |l - l| par h
   _             = 0       par calcul
   _             ≤ ε       par ε_pos
QED

Exemple "Une suite tendant vers une limite strictement positive est ultimement strictement positive."
  Données : (u : ℕ → ℝ) (l : ℝ)
  Hypothèses : (hl : l > 0) (h :u tend vers l)
  Conclusion : ∃ N, ∀ n ≥ N, u n ≥ l/2
Démonstration :
  Par h appliqué à l/2 en utilisant que l/2 > 0 on obtient N tel que (hN : ∀ n ≥ N, |u n - l| ≤ l / 2)
  Montrons que N convient
  Soit n ≥ N
  Par hN appliqué à n en utilisant que n ≥ N on obtient hN' : |u n - l| ≤ l / 2
  Par hN' on obtient (h₁ : -(l / 2) ≤ u n - l) (h₂ : u n - l ≤ l / 2)
  On conclut par h₁
QED

open Verbose.Named in
Exemple "Addition de suites convergentes."
  Données : (u v : ℕ → ℝ) (l l': ℝ)
  Hypothèses : (hu : u tend vers l) (hv : v tend vers l')
  Conclusion : (u + v) tend vers (l + l')
Démonstration :
  Soit ε > 0
  Par hu appliqué à ε/2 en utilisant que ε/2 > 0 on obtient N₁
      tel que (hN₁ : ∀ (n : ℕ), n ≥ N₁ → |u n - l| ≤ ε / 2)
  Par hv appliqué à ε/2 en utilisant que ε/2 > 0 on obtient N₂
      tel que (hN₂ : ∀ n ≥ N₂, |v n - l'| ≤ ε / 2)
  Montrons que max N₁ N₂ convient
  Soit n ≥ max N₁ N₂
  Par n_ge on obtient (hn₁ : N₁ ≤ n) (hn₂ : N₂ ≤ n)
  Fait fait₁ : |u n - l|  ≤ ε/2 par hN₁ appliqué à n en utilisant hn₁
  Fait fait₂ : |v n - l'| ≤ ε/2 par hN₂ appliqué à n en utilisant hn₂
  Calc
  |(u + v) n - (l + l')| = |(u n - l) + (v n - l')| par calcul
                     _   ≤ |u n - l| + |v n - l'|   par abs_add_le
                     _   ≤  ε/2 + ε/2               par fait₁ et par fait₂
                     _   ≤  ε                       par calcul
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
  Comme u tend vers l et ε > 0 on obtient N  tel que ∀ n ≥ N,  |u n - l| ≤ ε
  Comme w tend vers l et ε > 0 on obtient N' tel que ∀ n ≥ N', |w n - l| ≤ ε
  Montrons que max N N' convient : ∀ n ≥ max N N', |v n - l| ≤ ε
  Soit n ≥ max N N'
  Comme ∀ n ≥ N,  |u n - l| ≤ ε et n ≥ N  on obtient que |u n - l| ≤ ε
  Comme ∀ n ≥ N', |w n - l| ≤ ε et n ≥ N' on obtient que |w n - l| ≤ ε
  Montrons d'abord que -ε ≤ v n - l
  Calc -ε ≤ u n - l puisque |u n - l| ≤ ε
      _   ≤ v n - l puisque u n ≤ v n
  Montrons maintenant que v n - l ≤ ε
  Calc v n - l ≤ w n - l puisque v n ≤ w n
      _        ≤ ε       puisque |w n - l| ≤ ε
QED

open Verbose.Named in
Exemple "Une reformulation de la définition de limite."
  Données : (u : ℕ → ℝ) (l : ℝ)
  Hypothèses :
  Conclusion : (u tend vers l) ⇔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε
Démonstration :
  Montrons d'abord que (u tend vers l) ⇒ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε
  Supposons hyp : u tend vers l
  Soit ε > 0
  Par hyp appliqué à ε/2 en utilisant que ε/2 > 0 on obtient N
      tel que hN : ∀ n ≥ N, |u n - l| ≤ ε / 2
  Montrons que N convient
  Soit n ≥ N
  Calc |u n - l| ≤ ε/2 par hN appliqué à n en utilisant que n ≥ N
       _         < ε   par ε_pos
  Montrons maintenant que (∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε) ⇒ u tend vers l
  Supposons hyp : ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε
  Soit ε > 0
  Par hyp appliqué à ε en utilisant que ε > 0 on obtient N tel que hN : ∀ n ≥ N, |u n - l| < ε
  Montrons que N convient
  Soit n ≥ N
  On conclut par hN appliqué à n en utilisant que n ≥ N
QED

Exemple "Unicité de la limite d'une suite."
  Données : (u : ℕ → ℝ) (l l': ℝ)
  Hypothèses : (h : u tend vers l) (h': u tend vers l')
  Conclusion : l = l'
Démonstration :
  Par eq_of_forall_dist_le il suffit de montrer que ∀ ε > 0, |l - l'| ≤ ε
  Soit ε > 0
  Par h appliqué à ε/2 en utilisant que ε/2 > 0 on obtient N
      tel que hN : ∀ n ≥ N, |u n - l| ≤ ε / 2
  Par h' appliqué à ε/2 en utilisant que ε/2 > 0 on obtient N'
      tel que hN' : ∀ n ≥ N', |u n - l'| ≤ ε / 2
  Par hN appliqué à max N N' en utilisant le_max_left _ _
     on obtient hN₁ : |u (max N N') - l| ≤ ε / 2
  Par hN' appliqué à max N N' en utilisant le_max_right _ _
    on obtient hN'₁ : |u (max N N') - l'| ≤ ε / 2
  Calc |l - l'| = |(l-u (max N N')) + (u (max N N') -l')|  par calcul
    _           ≤ |l - u (max N N')| + |u (max N N') - l'| par abs_add_le
    _           = |u (max N N') - l| + |u (max N N') - l'| par abs_sub_comm
    _           ≤  ε/2 + ε/2                               par hN₁ et par hN'₁
    _           = ε                                        par calcul
QED

Exemple "Une suite croissante ayant un supremum fini tends vers lui."
  Données : (u : ℕ → ℝ) (M : ℝ)
  Hypothèses : (h : M est un supremum de u) (h' : u est croissante)
  Conclusion : u tend vers M
Démonstration :
  Soit ε > 0
  Par h on obtient (inf_M : ∀ (n : ℕ), u n ≤ M)
                   (sup_M_ep : ∀ ε > 0, ∃ (n₀ : ℕ), u n₀ ≥ M - ε)
  Par sup_M_ep appliqué à ε en utilisant que ε > 0 on obtient n₀ tel que hn₀ : u n₀ ≥ M - ε
  Montrons que n₀ convient : ∀ n ≥ n₀, |u n - M| ≤ ε
  Soit n ≥ n₀
  Par inf_M appliqué à n on obtient (inf_M' : u n ≤ M)
  Montrons d'abord que -ε ≤ u n - M
  · Par h' appliqué à n₀ et n en utilisant n_ge on obtient h'' : u n₀ ≤ u n
    Calc
      -ε ≤ u n₀ - M par hn₀
      _  ≤ u n - M par h''
  Montrons maintenant que u n - M ≤ ε
  · Calc
     u n - M ≤ M - M par inf_M'
     _       = 0     par calcul
     _       ≤ ε     par ε_pos
QED
