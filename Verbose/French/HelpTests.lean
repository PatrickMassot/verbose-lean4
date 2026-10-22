import Verbose.French.Claim
import Verbose.French.Help

set_option linter.unusedVariables false

setLang fr

configureAnonymousGoalSplittingLemmas Iff.intro Iff.intro' And.intro And.intro' abs_le_of_le_le abs_le_of_le_le'

configureHelpProviders DefaultHypHelp DefaultGoalHelp

set_option linter.unusedTactic false

/--
info: Aide
  • L'hypothèse h commence par « ∀ n > 0, ... »
    On peut l'utiliser avec :
    Par h appliqué à n₀ en utilisant hn₀ on obtient (hyp : P n₀)
    où n₀ est un nombre entier naturel et hn₀ est une démonstration du fait que n₀ > 0
    Le nom hyp peut être choisi librement parmi les noms disponibles.
-/
#guard_msgs in
example {P : ℕ → Prop} (h : ∀ n > 0, P n) : P 2 := by
  aide h
  apply h
  norm_num

/--
info: Aide
  • L'hypothèse h est de la forme « ∃ n > 0, ... »
    On peut l'utiliser avec :
    Par h on obtient n tel que (n_pos : n > 0) et (hn : P n)
    Les noms n, n_pos et hn peuvent être choisis librement parmi les noms disponibles.
-/
#guard_msgs in
example {P : ℕ → Prop} (h : ∃ n > 0, P n) : True := by
  aide h
  trivial

/--
info: Aide
  • L'hypothèse h est de la forme « ∃ ε > 0, ... »
    On peut l'utiliser avec :
    Par h on obtient ε tel que (ε_pos : ε > 0) et (hε : P ε)
    Les noms ε, ε_pos et hε peuvent être choisis librement parmi les noms disponibles.
-/
#guard_msgs in
example {P : ℝ → Prop} (h : ∃ ε > 0, P ε) : True := by
  aide h
  trivial

/--
info: Aide
  • L'hypothèse h commence par « ∀ n, ... »
    On peut l'utiliser avec :
    Par h appliqué à n₀ on obtient (hn₀ : P n₀ → Q n₀)
    où n₀ est un nombre entier naturel
    Le nom hn₀ peut être choisi librement parmi les noms disponibles.
  • Si cette hypothèse ne servira plus dans sa forme générale, on peut aussi spécialiser h par
    On applique h à n₀
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : ∀ n, P n → Q n) (h' : P 2) : Q 2 := by
  aide h
  exact h 2 h'

/--
info: Aide
  • L'hypothèse h commence par « ∀ n, ... »
    On peut l'utiliser avec :
    Par h appliqué à n₀ on obtient (hn₀ : P n₀)
    où n₀ est un nombre entier naturel
    Le nom hn₀ peut être choisi librement parmi les noms disponibles.
  • Si cette hypothèse ne servira plus dans sa forme générale, on peut aussi spécialiser h par
    On applique h à n₀
  • Comme le but est P 2, on peut utiliser :
    On conclut par h appliqué à 2
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∀ n, P n) : P 2 := by
  aide h
  exact h 2

/--
info: Aide
  • L'hypothèse h est une implication
    La conclusion de cette implication est le but courant
    On peut donc utiliser cette hypothèse avec :
    Par h il suffit de montrer P 1
  • Si vous disposez déjà d'une preuve H de P 1 alors on peut utiliser :
    On conclut par h appliqué à H
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 → Q 2) (h' : P 1) : Q 2 := by
  aide h
  exact h h'

/--
info: Aide
  • L'hypothèse h est une implication
    La prémisse de cette implication est P 1
    Si vous avez une démonstration H de P 1
    vous pouvez donc utiliser cette hypothèse avec :
    Par h appliqué à H on obtient H' : Q 2
    Le nom H' peut être choisi librement parmi les noms disponibles.
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 → Q 2) : True := by
  aide h
  trivial

/--
info: Aide
  • L'hypothèse h est de la forme « ... et ... »
    On peut l'utiliser avec :
    Par h on obtient (h_1 : P 1) (h' : Q 2)
    Les noms h_1 et h' peuvent être choisis librement parmi les noms disponibles.
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 ∧ Q 2) : True := by
  aide h
  trivial

/--
info: Aide
  • L'hypothèse h est une équivalence
    On peut s'en servir pour remplacer le membre de gauche (c'est à dire ∀ n ≥ 2, P n) par le membre de droite  (c'est à dire ∀ (l : ℕ), Q l) dans le but par :
    On réécrit via h
  • On peut s'en servir pour remplacer le membre de droite dans par le membre de gauche dans le but par :
    On réécrit via ← h
  • On peut aussi effectuer de tels remplacements dans une hypothèse hyp par
    On réécrit via h dans l'hypothèse hyp
  •  ou ⏎
    On réécrit via ← h dans l'hypothèse hyp
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : (∀ n ≥ 2, P n) ↔  ∀ l, Q l) : True := by
  aide h
  trivial

/--
info: Aide
  • Le but est de la forme « ... et ... »
    Une démonstration directe commence donc par :
    Montrons d'abord que True
    Une fois cette première démonstration achevée, il restera à montrer que 1 = 1
  • On peut aussi commencer par
    Montrons d'abord que 1 = 1
    puis, une fois cette première démonstration achevée, il restera à montrer que True
-/
#guard_msgs in
example : True ∧ 1 = 1 := by
  aide
  exact ⟨trivial, rfl⟩

/--
info: Aide
  • L'hypothèse h est de la forme « ... ou ... »
    On peut l'utiliser avec :
    On discute en utilisant h
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 ∨ Q 2) : True := by
  aide h
  trivial

/--
info: Aide
  • Le but est de la forme « ... ou ... »
    Une démonstration directe commence donc par annoncer quelle alternative va être démontrée :
    Montrons que True
  • ou bien :
    Montrons que False
-/
#guard_msgs in
example : True ∨ False := by
  aide
  left
  trivial

/-- info: Je n'ai rien à déclarer à propos de cette hypothèse. -/
#guard_msgs in
example (P : Prop) (h : P) : True := by
  aide h
  trivial

-- TODO: Improve this help message (low priority since it is very rare)
/--
info: Aide
  • Cette hypothèse est une contradiction.
    On peut en déduire tout ce qu'on veut par :
    ( Montrons une contradiction
        On conclut par h)
-/
#guard_msgs in
example (h : False) : 0 = 1 := by
  aide h
  trivial

/--
info: Aide
  • L'hypothèse h est une implication
    La prémisse de cette implication est l - n = 0
    Si vous avez une démonstration H de l - n = 0
    vous pouvez donc utiliser cette hypothèse avec :
    Par h appliqué à H on obtient H' : P l k
    Le nom H' peut être choisi librement parmi les noms disponibles.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (k l n : ℕ) (h : l - n = 0 → P l k) : True := by
  aide h
  trivial

/--
info: Aide
  • L'hypothèse h commence par « ∀ k ≥ 2, ∃ n ≥ 3, ... »
    On peut l'utiliser avec :
    Par h appliqué à k₀ en utilisant hk₀ on obtient
        n tel que (n_sup : n ≥ 3) et (hn : ∀ (l : ℕ), l - n = 0 → P l k₀)
    où k₀ est un nombre entier naturel et hk₀ est une démonstration du fait que k₀ ≥ 2.
    Les noms n, n_sup et hn peuvent être choisis librement parmi les noms disponibles.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  aide h
  trivial

/--
info: Aide
  • L'hypothèse h commence par « ∀ k n, k ≥ n ⇒ ... »
    On peut l'utiliser avec :
    Par h appliqué à k₀ et n₀ en utilisant H on obtient (h_1 : ∀ (l : ℕ), l - n₀ = 0 → P l k₀)
    où k₀ et n₀ sont des nombres entiers naturels et H est une démonstration de k₀ ≥ n₀
    Le nom h_1 peut être choisi librement parmi les noms disponibles.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k, ∀ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  aide h
  trivial

/--
info: Aide
  • L'hypothèse h commence par « ∀ k ≥ 2, ∃ n_1 ≥ 3, ... »
    On peut l'utiliser avec :
    Par h appliqué à k₀ en utilisant hk₀ on obtient
        n_1 tel que (n_1_sup : n_1 ≥ 3) et (hn_1 : ∀ (l : ℕ), l - n = 0 → P l k₀)
    où k₀ est un nombre entier naturel et hk₀ est une démonstration du fait que k₀ ≥ 2.
    Les noms n_1, n_1_sup et hn_1 peuvent être choisis librement parmi les noms disponibles.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (n : ℕ) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  aide h
  trivial

/--
info: Aide
  • L'hypothèse h est de la forme « ∃ n ≥ 5, ... »
    On peut l'utiliser avec :
    Par h on obtient n tel que (n_sup : n ≥ 5) et (hn : P n)
    Les noms n, n_sup et hn peuvent être choisis librement parmi les noms disponibles.
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∃ n ≥ 5, P n) : True := by
  aide h
  trivial

/--
info: Aide
  • L'hypothèse h commence par « ∀ k ≥ 2, ∃ n ≥ 3, ... »
    On peut l'utiliser avec :
    Par h appliqué à k₀ en utilisant hk₀ on obtient n tel que (n_sup : n ≥ 3) et (hn : P n k₀)
    où k₀ est un nombre entier naturel et hk₀ est une démonstration du fait que k₀ ≥ 2.
    Les noms n, n_sup et hn peuvent être choisis librement parmi les noms disponibles.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, P n k) : True := by
  aide h
  trivial

/--
info: Aide
  • L'hypothèse h est de la forme « ∃ n, ... »
    On peut l'utiliser avec :
    Par h on obtient n tel que (hn : P n)
    Les noms n et hn peuvent être choisis librement parmi les noms disponibles.
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∃ n : ℕ, P n) : True := by
  aide h
  trivial

/--
info: Aide
  • L'hypothèse h commence par « ∀ k, ∃ n, ... »
    On peut l'utiliser avec :
    Par h appliqué à k₀ on obtient n tel que (hn : P n k₀)
    où k₀ est un nombre entier naturel
    Les noms n et hn peuvent être choisis librement parmi les noms disponibles.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k, ∃ n : ℕ, P n k) : True := by
  aide h
  trivial

/--
info: Aide
  • L'hypothèse h commence par « ∀ k ≥ 2, ∃ n, ... »
    On peut l'utiliser avec :
    Par h appliqué à k₀ en utilisant hk₀ on obtient n tel que (hn : P n k₀)
    où k₀ est un nombre entier naturel et hk₀ est une démonstration du fait que k₀ ≥ 2
    Les noms n et hn peuvent être choisis librement parmi les noms disponibles.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n : ℕ, P n k) : True := by
  aide h
  trivial

/--
info: Aide
  • Le but commence par « ∃ n, ... »
    Une démonstration directe commence donc par :
    Montrons que n₀ convient : P n₀ → True
    où n₀ est un nombre entier naturel
-/
#guard_msgs in
example (P : ℕ → Prop): ∃ n : ℕ, P n → True := by
  aide
  use 0
  tauto

/--
info: Aide
  • Le but commence par « P ⇒ ... »
    Une démonstration directe commence donc par :
    Supposons hyp : P
    Le nom hyp peut être choisi librement parmi les noms disponibles.
-/
#guard_msgs in
example (P Q : Prop) (h : Q) : P → Q := by
  aide
  exact fun _ ↦ h

/--
info: Aide
  • Le but commence par « ∀ n ≥ 0 »
    Une démonstration directe commence donc par :
    Soit n ≥ 0
-/
#guard_msgs in
example : ∀ n ≥ 0, True := by
  aide
  intros
  trivial

/--
info: Aide
  • Le but commence par « ∀ n : ℕ, »
    Une démonstration directe commence donc par :
    Soit n : ℕ
-/
#guard_msgs in
example : ∀ n : ℕ, 0 ≤ n := by
  aide
  exact Nat.zero_le

/--
info: Aide
  • Le but commence par « ∃ n, ... »
    Une démonstration directe commence donc par :
    Montrons que n₀ convient : 0 ≤ n₀
    où n₀ est un nombre entier naturel
-/
#guard_msgs in
example : ∃ n : ℕ, 0 ≤ n := by
  aide
  use 1
  exact Nat.zero_le 1

/--
info: Aide
  • Le but commence par « ∃ n ≥ 1, ... »
    Une démonstration directe commence donc par :
    Montrons que n₀ convient : n₀ ≥ 1 ∧ True
    où n₀ est un nombre entier naturel
-/
#guard_msgs in
example : ∃ n ≥ 1, True := by
  aide
  use 1

/-- info: Je n'ai rien à déclarer à propos de cette hypothèse. -/
#guard_msgs in
example (h : Odd 3) : True := by
  aide h
  trivial

/--
info: Aide
  • Le but est l’inclusion s ⊆ t
    Une démonstration directe commence donc par :
    Soit x ∈ s
    Le nom x peut être choisi librement parmi les noms disponibles.
---
info: Aide
  • L'hypothèse h affirme l'inclusion de s dans t.
    On peut s'en servir avec :
    Par h appliqué à x_1 en utilisant hx on obtient hx' : x_1 ∈ t
    où x_1 est un nombre entier naturel et hx est une démonstration du fait que x_1 ∈ s
    Le nom hx' peut être choisi librement parmi les noms disponibles.
-/
#guard_msgs in
example (s t : Set ℕ) (h : s ⊆ t) : s ⊆ t := by
  aide
  Soit x ∈ s
  aide h
  exact h x_mem

/--
info: Aide
  • L'hypothèse h est une appartenance à une intersection
    On peut l'utiliser avec :
    Par h on obtient (h_1 : x ∈ s) (h' : x ∈ t)
    Les noms h_1 et h' peuvent être choisis librement parmi les noms disponibles.
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∩ t) : x ∈ s := by
  aide h
  Par h on obtient (h_1 : x ∈ s) (h' : x ∈ t)
  exact h_1

/--
info: Aide
  • L'hypothèse h est une appartenance à une intersection
    On peut l'utiliser avec :
    Par h on obtient (h_1 : x ∈ s) (h' : x ∈ t)
    Les noms h_1 et h' peuvent être choisis librement parmi les noms disponibles.
---
info: Aide
  • Le but est l'appartenance de x à l'intersection de t avec un autre ensemble.
    Une démonstration directe commence donc par :
    Montrons d'abord que x ∈ t
---
info: Aide
  • L’étape suivante est d'annoncer :
    Montrons maintenant que x ∈ s
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∩ t) : x ∈ t ∩ s := by
  aide h
  Par h on obtient (h_1 : x ∈ s) (h' : x ∈ t)
  aide
  Montrons d'abord que x ∈ t
  exact h'
  aide
  Montrons maintenant que x ∈ s
  exact h_1

open Verbose.Named in
/--
info: Aide
  • L'hypothèse h est une appartenance à une réunion
    On peut l'utiliser avec :
    On discute en utilisant h
---
info: Aide
  • Le but est l'appartenance de x à la réunion de t et s.
    Une démonstration directe commence donc par :
    Montrons que x ∈ t
  • ou bien par
    Montrons que x ∈ s
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∪ t) : x ∈ t ∪ s := by
  aide h
  On discute en utilisant h
  Supposons hyp : x ∈ s
  aide
  Montrons que x ∈ s
  exact hyp
  Supposons hyp : x ∈ t
  Montrons que x ∈ t
  exact  hyp

/--
info: Aide
  • Le but commence par « False ⇒ ... »
    Une démonstration directe commence donc par :
    Supposons hyp : False
    Le nom hyp peut être choisi librement parmi les noms disponibles.
-/
#guard_msgs in
example : False → True := by
  aide
  simp

/-- info: Je n'ai rien à déclarer à propos de ce but. -/
#guard_msgs in
example : True := by
  aide
  trivial

configureHelpProviders DefaultHypHelp DefaultGoalHelp helpContraposeGoal

/--
info: Aide
  • Le but commence par « False ⇒ ... »
    Une démonstration directe commence donc par :
    Supposons hyp : False
    Le nom hyp peut être choisi librement parmi les noms disponibles.
  • Le but est une implication.
    On peut débuter une démonstration par contraposition par :
    On contrapose
-/
#guard_msgs in
example : False → True := by
  aide
  On contrapose
  simp

/-- info: Je n'ai rien à déclarer à propos de ce but. -/
#guard_msgs in
example : True := by
  aide
  trivial

configureHelpProviders DefaultHypHelp DefaultGoalHelp helpByContradictionGoal

/--
info: Aide
  • On peut débuter une démonstration par l’absurde par :
    Supposons par l'absurde hyp : False
-/
#guard_msgs in
example : True := by
  aide
  trivial

/--
info: Aide
  • L'hypothèse h est de la forme « ∃ x, ... »
    On peut l'utiliser avec :
    Par h on obtient x_1 tel que (hx_1 : f x_1 = y)
    Les noms x_1 et hx_1 peuvent être choisis librement parmi les noms disponibles.
-/
#guard_msgs in
example {X Y} (f : X → Y) (x : X) (y : Y) (h : ∃ x, f x = y) : True := by
  aide h
  trivial

/--
info: Aide
  • L'hypothèse h est de la forme « ∃ x ∈ s, ... »
    On peut l'utiliser avec :
    Par h on obtient x_1 tel que (x_1_dans : x_1 ∈ s) et (hx_1 : f x_1 = y)
    Les noms x_1, x_1_dans et hx_1 peuvent être choisis librement parmi les noms disponibles.
-/
#guard_msgs in
example {X Y} (f : X → Y) (s : Set X) (x : X) (y : Y) (h : ∃ x ∈ s, f x = y) : True := by
  aide h
  trivial

/--
info: Aide
  • Le but est de montrer la négation de P, c’est à dire montrer que P implique une contradiction.
    Une démonstration directe commence donc par :
    Supposons hyp : P
    Il restera à montrer une contradiction.
-/
#guard_msgs in
example (P : Prop) (h : ¬ P) : ¬ P := by
  aide
  exact h

/--
info: Aide
  • Le but est de montrer la négation de x = y, c’est à dire montrer que x = y implique une contradiction.
    Une démonstration directe commence donc par :
    Supposons hyp : x = y
    Il restera à montrer une contradiction.
-/
#guard_msgs in
example (x y : ℕ) (h : x ≠ y) : x ≠ y := by
  aide
  exact h

allowProvingNegationsByContradiction

/--
info: Aide
  • On peut débuter une démonstration par l’absurde par :
    Supposons par l'absurde hyp : P
  • Le but est de montrer la négation de P, c’est à dire montrer que P implique une contradiction.
    Une démonstration directe commence donc par :
    Supposons hyp : P
    Il restera à montrer une contradiction.
-/
#guard_msgs in
example (P : Prop) (h : ¬ P) : ¬ P := by
  aide
  exact h

/--
info: Aide
  • On peut débuter une démonstration par l’absurde par :
    Supposons par l'absurde hyp : x = y
  • Le but est de montrer la négation de x = y, c’est à dire montrer que x = y implique une contradiction.
    Une démonstration directe commence donc par :
    Supposons hyp : x = y
    Il restera à montrer une contradiction.
-/
#guard_msgs in
example (x y : ℕ) (h : x ≠ y) : x ≠ y := by
  aide
  exact h

configureHelpProviders SinceHypHelp SinceGoalHelp helpShowContrapositiveGoal
/--
info: Aide
  • L'hypothèse h commence par « ∀ n > 0, ... »
    On peut l'utiliser avec :
    Comme ∀ n > 0, P n et n₀ > 0 on obtient que P n₀
    où n₀ est un nombre entier naturel et n₀ > 0 découle directement d’une hypothèse.
-/
#guard_msgs in
example {P : ℕ → Prop} (h : ∀ n > 0, P n) : P 2 := by
  aide h
  apply h
  norm_num

/--
info: Aide
  • L'hypothèse h est de la forme « ∃ n > 0, ... »
    On peut l'utiliser avec :
    Comme ∃ n > 0, P n on obtient n tel que (n_pos : n > 0) et (hn : P n)
    Les noms n, n_pos et hn peuvent être choisis librement parmi les noms disponibles.
-/
#guard_msgs in
example {P : ℕ → Prop} (h : ∃ n > 0, P n) : True := by
  aide h
  trivial

/--
info: Aide
  • L'hypothèse h est de la forme « ∃ ε > 0, ... »
    On peut l'utiliser avec :
    Comme ∃ ε > 0, P ε on obtient ε tel que (ε_pos : ε > 0) et (hε : P ε)
    Les noms ε, ε_pos et hε peuvent être choisis librement parmi les noms disponibles.
-/
#guard_msgs in
example {P : ℝ → Prop} (h : ∃ ε > 0, P ε) : True := by
  aide h
  trivial

/--
info: Aide
  • L'hypothèse h commence par « ∀ n, ... »
    On peut l'utiliser avec :
    Comme ∀ (n : ℕ), P n → Q n on obtient que P n₀ → Q n₀
    où n₀ est un nombre entier naturel
  • Si cette hypothèse ne servira plus dans sa forme générale, on peut aussi spécialiser h par
    On applique h à n₀
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : ∀ n, P n → Q n) (h' : P 2) : Q 2 := by
  aide h
  exact h 2 h'

/--
info: Aide
  • L'hypothèse h commence par « ∀ n, ... »
    On peut l'utiliser avec :
    Comme ∀ (n : ℕ), P n on obtient que P n₀
    où n₀ est un nombre entier naturel
  • Si cette hypothèse ne servira plus dans sa forme générale, on peut aussi spécialiser h par
    On applique h à n₀
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∀ n, P n) : P 2 := by
  aide h
  exact h 2

/--
info: Aide
  • L'hypothèse h est une implication
    La conclusion de cette implication est le but courant
    On peut donc utiliser cette hypothèse avec :
    Comme P 1 → Q 2 il suffit de montrer que P 1
  • Si vous disposez déjà d'une preuve de P 1 alors on peut utiliser :
    Comme P 1 → Q 2 et P 1 on conclut que Q 2
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 → Q 2) (h' : P 1) : Q 2 := by
  aide h
  exact h h'

/--
info: Aide
  • L'hypothèse h est une implication
    La prémisse de cette implication est P 1
    Si vous avez une démonstration de P 1
    vous pouvez donc utiliser cette hypothèse avec :
    Comme P 1 → Q 2 et P 1 on obtient que Q 2
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 → Q 2) : True := by
  aide h
  trivial

/--
info: Aide
  • L'hypothèse h est de la forme « ... et ... »
    On peut l'utiliser avec :
    Comme P 1 ∧ Q 2 on obtient que P 1 et Q 2
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 ∧ Q 2) : True := by
  aide h
  trivial

/--
info: Aide
  • L'hypothèse h est une équivalence
    On peut s'en servir pour remplacer le membre de gauche (c'est à dire ∀ n ≥ 2, P n) par le membre de droite  (c'est à dire ∀ (l : ℕ), Q l) dans le but (ou vice-versa) par :
    Comme (∀ n ≥ 2, P n) ↔ ∀ (l : ℕ), Q l il suffit de montrer que ?_
    en remplaçant le point d'interrogation par le nouveau but.
  • On peut aussi effectuer de tels remplacements dans un fait qui découle directement des hypothèses courantes par
    Comme (∀ n ≥ 2, P n) ↔ ∀ (l : ℕ), Q l et ?_ on obtient que ?_
    en remplaçant le premier point d'interrogation par le fait dans lequel on veut effectuer le remplacement et le second par le nouveau fait obtenu.
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : (∀ n ≥ 2, P n) ↔  ∀ l, Q l) : True := by
  aide h
  trivial

/--
info: Aide
  • L'hypothèse h commence par « ∀ x, ... »
    On peut l'utiliser avec :
    Comme ∀ (x y : ℝ), x ≤ y → f x ≤ f y on obtient que ∀ (y : ℝ), x₀ ≤ y → f x₀ ≤ f y
    où x₀ est un nombre réel
  • Si cette hypothèse ne servira plus dans sa forme générale, on peut aussi spécialiser h par
    On applique h à x₀
-/
#guard_msgs in
example (f : ℝ → ℝ) (h : ∀ x y, x ≤ y → f x ≤ f y) (a b : ℝ) (h' : a ≤ b) : True := by
  aide h
  trivial

/--
info: Aide
  • L'hypothèse h commence par « ∀ x > 0, ... »
    On peut l'utiliser avec :
    Comme ∀ x > 0, x = 1 → f x ≤ 0 et x₀ > 0 on obtient que x₀ = 1 → f x₀ ≤ 0
    où x₀ est un nombre réel et x₀ > 0 découle directement d’une hypothèse.
-/
#guard_msgs in
example (f : ℝ → ℝ) (h : ∀ x > 0, x = 1 → f x ≤ 0) (a b : ℝ) (h' : a ≤ b) : True := by
  aide h
  trivial

/--
info: Aide
  • L'hypothèse h est une implication
    La prémisse de cette implication est l - n = 0
    Si vous avez une démonstration de l - n = 0
    vous pouvez donc utiliser cette hypothèse avec :
    Comme l - n = 0 → P l k et l - n = 0 on obtient que P l k
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (k l n : ℕ) (h : l - n = 0 → P l k) : True := by
  aide h
  trivial

/--
info: Aide
  • L'hypothèse h commence par « ∀ k ≥ 2, ∃ n ≥ 3, ... »
    On peut l'utiliser avec :
    Comme ∀ k ≥ 2, ∃ n ≥ 3, ∀ (l : ℕ), l - n = 0 → P l k et k₀ ≥ 2 on obtient
        n tel que n ≥ 3 et ∀ (l : ℕ), l - n = 0 → P l k₀
    où k₀ est un nombre entier naturel et la relation k₀ ≥ 2 doit découler directement d’une hypothèse.
    Le nom n peut être choisi librement parmi les noms disponibles.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  aide h
  trivial

-- FIXME: completely broken case
/--
info: Aide
  • L'hypothèse h commence par « ∀ k n, k ≥ n ⇒ ... »
    On peut l'utiliser avec :
    Comme ∀ (k n : ℕ), n ≥ 3 → ∀ (l : ℕ), l - n = 0 → P l k et n ≥ 3 on obtient que
        ∀ (l : ℕ), l - n₀ = 0 → P l k₀
    où k₀ et n₀ sont des nombres entiers naturels et k₀ ≥ n₀ découle immédiatement d’une hypothèse.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k, ∀ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  aide h
  trivial

-- FIXME: completely broken case
/--
info: Aide
  • L'hypothèse h commence par « ∀ k n, k ≤ n ⇒ ... »
    On peut l'utiliser avec :
    Comme ∀ (k n : ℕ), n ≤ k → f n ≤ f k et n ≤ k on obtient que f n₀ ≤ f k₀
    où k₀ et n₀ sont des nombres entiers naturels et k₀ ≤ n₀ découle immédiatement d’une hypothèse.
-/
#guard_msgs in
example (f : ℕ → ℕ) (h : ∀ k n, n ≤ k → f n ≤ f k) : True := by
  aide h
  trivial

-- FIXME: in hn_1, n is not replaced by n_1. This is an issue in
-- helpSinceForAllRelExistsRelSuggestion (or rather the function calling it)
/--
info: Aide
  • L'hypothèse h commence par « ∀ k ≥ 2, ∃ n_1 ≥ 3, ... »
    On peut l'utiliser avec :
    Comme ∀ k ≥ 2, ∃ n ≥ 3, ∀ (l : ℕ), l - n = 0 → P l k et k₀ ≥ 2 on obtient
        n_1 tel que n_1 ≥ 3 et ∀ (l : ℕ), l - n = 0 → P l k₀
    où k₀ est un nombre entier naturel et la relation k₀ ≥ 2 doit découler directement d’une hypothèse.
    Le nom n_1 peut être choisi librement parmi les noms disponibles.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (n : ℕ) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  aide h
  Par h appliqué à 2 en utilisant le_rfl on obtient n' tel que (n_sup : n' ≥ 3) et (hn : ∀ (l : ℕ), l - n' = 0 → P l 2)
  trivial

/--
info: Aide
  • L'hypothèse h est de la forme « ∃ n ≥ 5, ... »
    On peut l'utiliser avec :
    Comme ∃ n ≥ 5, P n on obtient n tel que (n_sup : n ≥ 5) et (hn : P n)
    Les noms n, n_sup et hn peuvent être choisis librement parmi les noms disponibles.
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∃ n ≥ 5, P n) : True := by
  aide h
  trivial

/--
info: Aide
  • L'hypothèse h commence par « ∀ k ≥ 2, ∃ n ≥ 3, ... »
    On peut l'utiliser avec :
    Comme ∀ k ≥ 2, ∃ n ≥ 3, P n k et k₀ ≥ 2 on obtient n tel que n ≥ 3 et P n k₀
    où k₀ est un nombre entier naturel et la relation k₀ ≥ 2 doit découler directement d’une hypothèse.
    Le nom n peut être choisi librement parmi les noms disponibles.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, P n k) : True := by
  aide h
  trivial

/--
info: Aide
  • L'hypothèse h est de la forme « ∃ n, ... »
    On peut l'utiliser avec :
    Comme ∃ n, P n on obtient n tel que P n
    Le nom n peut être choisi librement parmi les noms disponibles.
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∃ n : ℕ, P n) : True := by
  aide h
  trivial

/--
info: Aide
  • L'hypothèse h commence par « ∀ k, ∃ n, ... »
    On peut l'utiliser avec :
    Comme ∀ (k : ℕ), ∃ n, P n k on obtient n tel que P n k₀
    où k₀ est un nombre entier naturel
    Le nom n peut être choisi librement parmi les noms disponibles.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k, ∃ n : ℕ, P n k) : True := by
  aide h
  trivial

/--
info: Aide
  • L'hypothèse h est de la forme « ... ou ... »
    On peut l'utiliser avec :
    On discute selon que P 1 ou Q 2
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 ∨ Q 2) : True := by
  aide h
  trivial

/--
info: Aide
  • L'hypothèse h est une appartenance à une intersection
    On peut l'utiliser avec :
    Comme x ∈ s ∩ t on obtient que x ∈ s et x ∈ t
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∩ t) : x ∈ s := by
  aide h
  Par h on obtient (h_1 : x ∈ s) (h' : x ∈ t)
  exact h_1

/--
info: Aide
  • L'hypothèse h est une appartenance à une intersection
    On peut l'utiliser avec :
    Comme x ∈ s ∩ t on obtient que x ∈ s et x ∈ t
---
info: Aide
  • Le but est l'appartenance de x à l'intersection de t avec un autre ensemble.
    Une démonstration directe commence donc par :
    Montrons d'abord que x ∈ t
---
info: Aide
  • L’étape suivante est d'annoncer :
    Montrons maintenant que x ∈ s
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∩ t) : x ∈ t ∩ s := by
  aide h
  Par h on obtient (h_1 : x ∈ s) (h' : x ∈ t)
  aide
  Montrons d'abord que x ∈ t
  exact h'
  aide
  Montrons maintenant que x ∈ s
  exact h_1

open Verbose.Named in
/--
info: Aide
  • L'hypothèse h est une appartenance à une réunion
    On peut l'utiliser avec :
    On discute selon que x ∈ s ou x ∈ t
---
info: Aide
  • Le but est l'appartenance de x à la réunion de t et s.
    Une démonstration directe commence donc par :
    Montrons que x ∈ t
  • ou bien par
    Montrons que x ∈ s
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∪ t) : x ∈ t ∪ s := by
  aide h
  On discute en utilisant h
  Supposons hyp : x ∈ s
  aide
  Montrons que x ∈ s
  exact hyp
  Supposons hyp : x ∈ t
  Montrons que x ∈ t
  exact  hyp

/--
info: Aide
  • L'hypothèse h est une inégalité
    Le but courant en découle immédiatement
    On peut l'utiliser avec :
    Comme ε > 0 on conclut que ε / 2 > 0
-/
#guard_msgs in
example (ε : ℝ) (h : ε > 0) : ε/2 > 0 := by
  aide h
  linarith

/--
info: Aide
  • Le but est une inégalité
    On peut commencer un calcul par
    Calc
        ε / 2 > 0 par?
    La dernière ligne du calcul n'est pas forcément une égalité, cela peut être une inégalité.
    De même la première ligne peut être une égalité. Au total les symboles de relations
    doivent s'enchaîner pour donner  > ⏎
  • Si cette inégalité découle immédiatement d’une hypothèse on peut utiliser
    Comme ?_ on conclut que ε / 2 > 0
    en remplaçant le point d’interrogation par l’énoncé de l’hypothèse
-/
#guard_msgs in
example (ε : ℝ) (h : ε > 0) : ε/2 > 0 := by
  aide
  Comme ε > 0 on conclut que ε / 2 > 0

/--
info: Aide
  • L'hypothèse h est une équivalence
    On peut s'en servir pour remplacer le membre de gauche (c'est à dire P) par le membre de droite  (c'est à dire Q) dans le but (ou vice-versa) par :
    Comme P ↔ Q il suffit de montrer que ?_
    en remplaçant le point d'interrogation par le nouveau but.
  • On peut aussi effectuer de tels remplacements dans un fait qui découle directement des hypothèses courantes par
    Comme P ↔ Q et ?_ on obtient que ?_
    en remplaçant le premier point d'interrogation par le fait dans lequel on veut effectuer le remplacement et le second par le nouveau fait obtenu.
-/
#guard_msgs in
example (P Q : Prop) (h : P ↔ Q) (h' : P) : Q := by
  aide h
  Comme P ↔ Q il suffit de montrer que P
  exact h'

/--
info: Aide
  • L'hypothèse h affirme l'inclusion de A dans B.
    On peut s'en servir avec :
    Comme A ⊆ B et x ∈ A on obtient que x ∈ B
    où x est un nombre entier naturel
-/
#guard_msgs in
example (A B : Set ℕ) (h : A ⊆ B) : True := by
  aide h
  trivial

/--
info: Aide
  • Cette hypothèse est une contradiction.
    On peut en déduire le but par :
    Comme False on conclut que 0 = 1
-/
#guard_msgs in
example (h : False) : 0 = 1 := by
  aide h
  Comme False on conclut que 0 = 1

/--
info: Aide
  • Le but est de montrer une contradiction.
    On peut par exemple appliquer une hypothèse qui est une négation
    c'est à dire, par définition, de la forme P ⇒ False.
    On peut également combiner deux faits qui se contredise directement par :
    Comme ?_ et ?_ on conclut que False
    en remplaçant les points d’interrogation par deux faits qui se contredisent directement et découlent immédiatement d’hypothèses.
  • On peut également invoquer un fait manifestement faux (comme par exemple `0 = 1`) qui découle directement des hypothèses :
    Comme ?_ on conclut que False
    en remplaçant le points d’interrogation par ce fait manifestement faux.
-/
#guard_msgs in
example (h : 0 = 1) : False := by
  aide
  Comme 0 = 1 on conclut que False

/--
info: Aide
  • Le but est une inégalité
    On peut commencer un calcul par
    Calc
        a ≤ c par?
    La dernière ligne du calcul n'est pas forcément une égalité, cela peut être une inégalité.
    De même la première ligne peut être une égalité. Au total les symboles de relations
    doivent s'enchaîner pour donner  ≤ ⏎
  • Si cette inégalité découle immédiatement d’une hypothèse on peut utiliser
    Comme ?_ on conclut que a ≤ c
    en remplaçant le point d’interrogation par l’énoncé de l’hypothèse
-/
#guard_msgs in
example (a b c : ℤ) (h : a ≤ b) (h' : b ≤ c) : a ≤ c := by
  aide
  exact le_trans h h'

/--
info: Aide
  • Le but commence par « False ⇒ ... »
    Une démonstration directe commence donc par :
    Supposons que False
  • Le but est une implication.
    On peut débuter une démonstration par contraposition par :
    Montrons la contraposée : ¬True → ¬False
-/
#guard_msgs in
example : False → True := by
  aide
  Montrons la contraposée : ¬True → ¬False
  simp

open Verbose.NameLess

/--
info: Aide
  • Le but commence par « False ⇒ ... »
    Une démonstration directe commence donc par :
    Supposons que False
  • Le but est une implication.
    On peut débuter une démonstration par contraposition par :
    Montrons la contraposée : ¬True → ¬False
-/
#guard_msgs in
example : False → True := by
  Fait: True par
    trivial
  aide
  Montrons la contraposée : ¬True → ¬False
  simp
