import Verbose.Spanish.ExampleLib
set_option linter.unusedTactic false

Ejercicio "Toda función continua implica continuidad de sucesiones"
  Dado: (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
  Asumimos: (hu : u converge a x₀) (hf : f es continua en x₀)
  Conclusión: (f ∘ u) converge a f x₀
Demostración:
  Probemos que ∀ ε > 0, ∃ N, ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Sea ε > 0
  Por hf aplicado a ε usando que ε > 0 tenemos δ tal que
    (δ_pos : δ > 0) yy (Hf : ∀ x, |x - x₀| ≤ δ ⇒ |f x - f x₀| ≤ ε)
  Por hu aplicado a δ usando que δ > 0 tenemos N tal que Hu : ∀ n ≥ N, |u n - x₀| ≤ δ
  Probemos que N basta : ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Sea n ≥ N
  Por Hf aplicado a u n basta probar que |u n - x₀| ≤ δ
  Concluimos por Hu aplicado a n usando que n ≥ N
QED

-- Variation without referring to any assumption label
Ejercicio "Toda función continua implica continuidad de sucesiones"
  Dado: (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
  Asumimos: (hu : u converge a x₀) (hf : f es continua en x₀)
  Conclusión: (f ∘ u) converge a f x₀
Demostración:
  Probemos que ∀ ε > 0, ∃ N, ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Sea ε > 0
  Como f es continua en x₀ yy ε > 0 se tiene δ tal que
    δ > 0 yy ∀ x, |x - x₀| ≤ δ ⇒ |f x - f x₀| ≤ ε
  Como u converge a x₀ yy δ > 0 se tiene N tal que ∀ n ≥ N, |u n - x₀| ≤ δ
  Probemos que N basta : ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Sea n ≥ N
  Como ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε basta probar que |u n - x₀| ≤ δ
  Como ∀ n ≥ N, |u n - x₀| ≤ δ yy n ≥ N concluimos que |u n - x₀| ≤ δ
/-    -- Forward reasoning variation
  Como ∀ n ≥ N, |u n - x₀| ≤ δ yy n ≥ N tenemos que |u n - x₀| ≤ δ
  Como ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε yy |u n - x₀| ≤ δ concluimos que |f (u n) - f x₀| ≤ ε -/
QED

Ejemplo "Toda sucesión constante es convergente."
  Dado: (u : ℕ → ℝ) (l : ℝ)
  Asumimos: (h : ∀ n, u n = l)
  Conclusión: u converge a l
Demostración:
  Sea ε > 0
  Probemos que ∃ N, ∀ n ≥ N, |u n - l| ≤ ε
  Probemos que 0 basta
  Sea n ≥ 0
  Calc |u n - l| = |l - l| por h
   _             = 0       por cálculo
   _             ≤ ε       por ε_pos
QED

Ejemplo "Una sucesión que converge a un límite positivo es eventualmente positiva."
  Dado: (u : ℕ → ℝ) (l : ℝ)
  Asumimos: (hl : l > 0) (h :u converge a l)
  Conclusión: ∃ N, ∀ n ≥ N, u n ≥ l/2
Demostración:
  Por h aplicado a l/2 usando que l/2 > 0 tenemos N tal que hN : ∀ n ≥ N, |u n - l| ≤ l/2
  Probemos que N basta
  Sea n ≥ N
  Por hN aplicado a n usando que n ≥ N tenemos hN' : |u n - l| ≤ l/2
  Por hN' tenemos (h₁ : -(l/2) ≤ u n - l) (h₂ : u n - l ≤ l/2)
  Concluimos por h₁
QED


open Verbose.Named in
Ejemplo "Suma de sucesiones convergentes."
  Dado: (u v : ℕ → ℝ) (l l' : ℝ)
  Asumimos: (hu : u converge a l) (hv : v converge a l')
  Conclusión: (u + v) converge a (l + l')
Demostración:
  Sea ε > 0
  Por hu aplicado a ε/2 usando que ε/2 > 0 tenemos N₁
      tal que (hN₁ : ∀ n ≥ N₁, |u n - l| ≤ ε / 2)
  Por hv aplicado a ε/2 usando que ε/2 > 0 tenemos N₂
      tal que (hN₂ : ∀ n ≥ N₂, |v n - l'| ≤ ε / 2)
  Probemos que max N₁ N₂ basta
  Sea n ≥ max N₁ N₂
  Por n_ge tenemos (hn₁ : N₁ ≤ n) (hn₂ : N₂ ≤ n)
  Afirmación fact₁ : |u n - l| ≤ ε/2
    pues hN₁ aplicado a n usando hn₁
  Afirmación fact₂ : |v n - l'| ≤ ε/2
    pues hN₂ aplicado a n usando hn₂
  Calc
  |(u + v) n - (l + l')| = |(u n - l) + (v n - l')| por cálculo
                     _ ≤ |u n - l| + |v n - l'|     por abs_add_le
                     _ ≤  ε/2 + ε/2                 por fact₁ yy fact₂
                     _ =  ε                         por cálculo
QED

Ejemplo "Teorema del sandwhich"
  Dado: (u v w : ℕ → ℝ) (l : ℝ)
  Asumimos: (hu : u converge a l) (hw : w converge a l)
    (h : ∀ n, u n ≤ v n)
    (h' : ∀ n, v n ≤ w n)
  Conclusión: v converge a l
Demostración:
  Probemos que ∀ ε > 0, ∃ N, ∀ n ≥ N, |v n - l| ≤ ε
  Sea ε > 0
  Como u converge a l yy ε > 0 se tiene N tal que ∀ n ≥ N, |u n - l| ≤ ε
  Como w converge a l yy ε > 0 se tiene N' tal que ∀ n ≥ N', |w n - l| ≤ ε
  Probemos que max N N' basta : ∀ n ≥ max N N', |v n - l| ≤ ε
  Sea n ≥ max N N'
  Como ∀ n ≥ N,  |u n - l| ≤ ε yy n ≥ N  tenemos que |u n - l| ≤ ε
  Como ∀ n ≥ N', |w n - l| ≤ ε yy n ≥ N' tenemos que |w n - l| ≤ ε
  Probemos que |v n - l| ≤ ε
  Primero probemos que -ε ≤ v n - l
  Calc -ε ≤ u n - l ya que |u n - l| ≤ ε
       _  ≤ v n - l ya que u n ≤ v n
  Probemos ahora que v n - l ≤ ε
  Calc v n - l ≤ w n - l  ya que v n ≤ w n
       _       ≤ ε        ya que |w n - l| ≤ ε
QED

open Verbose.Named in
Ejemplo "Una reformulación de la definición de convergencia en sucesiones."
  Dado: (u : ℕ → ℝ) (l : ℝ)
  Asumimos:
  Conclusión: (u converge a l) ⇔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε
Demostración:
  Primero probemos que (u converge a l) ⇒ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε
  Supongamos hyp : u converge a l
  Sea ε > 0
  Por hyp aplicado a ε/2 usando que ε/2 > 0 tenemos N
      tal que hN : ∀ n ≥ N, |u n - l| ≤ ε / 2
  Probemos que N basta
  Sea n ≥ N
  Calc |u n - l| ≤ ε/2  por hN aplicado a n usando que n ≥ N
       _         < ε    ya que ε > 0
  Probemos ahora que (∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε) ⇒ u converge a l
  Supongamos hyp : ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε
  Sea ε > 0
  Por hyp aplicado a ε usando que ε > 0 tenemos N tal que hN : ∀ n ≥ N, |u n - l| < ε
  Probemos que N basta
  Sea n ≥ N
  Concluimos por hN aplicado a n usando que n ≥ N
QED


Ejemplo "Unicidad del límite."
  Dado: (u : ℕ → ℝ) (l l' : ℝ)
  Asumimos: (h : u converge a l) (h': u converge a l')
  Conclusión: l = l'
Demostración:
  Por eq_of_forall_dist_le basta probar que ∀ ε > 0, |l - l'| ≤ ε
  Sea ε > 0
  Por h aplicado a ε/2 usando que ε/2 > 0 tenemos N
      tal que hN : ∀ n ≥ N, |u n - l| ≤ ε / 2
  Por h' aplicado a  ε/2 usando que ε/2 > 0 tenemos N'
      tal que hN' : ∀ n ≥ N', |u n - l'| ≤ ε / 2
  Por hN aplicado a max N N' usando le_max_left _ _
     tenemos hN₁ : |u (max N N') - l| ≤ ε / 2
  Por hN' aplicado a max N N' usando le_max_right _ _
    tenemos hN'₁ : |u (max N N') - l'| ≤ ε / 2
  Calc |l - l'| = |(l-u (max N N')) + (u (max N N') -l')|  por cálculo
  _             ≤ |l - u (max N N')| + |u (max N N') - l'| por abs_add_le
  _             = |u (max N N') - l| + |u (max N N') - l'| por abs_sub_comm
  _             ≤  ε/2 + ε/2                               por hN₁ yy hN'₁
  _             = ε                                        por cálculo
QED

Ejemplo "Toda sucesión creciente con un supremo tiende a este mismo."
  Dado: (u : ℕ → ℝ) (M : ℝ)
  Asumimos: (h : M es un supremo de u) (h' : u es creciente)
  Conclusión: u converge a M
Demostración:
  Sea ε > 0
  Por h tenemos (inf_M : ∀ (n : ℕ), u n ≤ M)
                   (sup_M_ep : ∀ ε > 0, ∃ (n₀ : ℕ), u n₀ ≥ M - ε)
  Por sup_M_ep aplicado a ε usando que ε > 0 tenemos n₀ tal que (hn₀ : u n₀ ≥ M - ε)
  Probemos que n₀ basta : ∀ n ≥ n₀, |u n - M| ≤ ε
  Sea n ≥ n₀
  Por inf_M aplicado a n tenemos (inf_M' : u n ≤ M)
  Primero probemos que -ε ≤ u n - M
  · Por h' aplicado a n₀ yy n usando n_ge tenemos h'' : u n₀ ≤ u n
    Calc
      -ε ≤ u n₀ - M por hn₀
      _  ≤ u n - M por h''
  Probemos ahora que u n - M ≤ ε
  · Calc
     u n - M ≤ M - M por inf_M'
     _       = 0     por cálculo
     _       ≤ ε     por ε_pos
QED
