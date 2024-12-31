import Verbose.Tactics.We
import Verbose.French.Common

open Lean Elab Parser Tactic Verbose.French

syntax locationFR := withPosition(" dans" (locationWildcard <|> locationHyp))

def locationFR_to_location : TSyntax `locationFR → TacticM (TSyntax `Lean.Parser.Tactic.location)
| `(locationFR|dans $x) => `(location|at $x)
| _ => `(location|at *) -- should not happen

declare_syntax_cat becomesFR
syntax colGt " qui devient " term : becomesFR

def extractBecomesFR (e : Lean.TSyntax `becomesFR) : Lean.Term := ⟨e.raw[1]!⟩

elab rw:"On" " réécrit via " s:myRwRuleSeq l:(locationFR)? new:(becomesFR)? : tactic => do
  rewriteTac rw s (l.map expandLocation) (new.map extractBecomesFR)

elab rw:"On" " réécrit via " s:myRwRuleSeq " partout" : tactic => do
  rewriteTac rw s (some Location.wildcard) none

elab "On" " discute en utilisant " exp:term : tactic =>
  discussOr exp

elab "On" " discute selon que " exp:term : tactic =>
  discussEm exp

elab "On" " conclut par " e:maybeAppliedFR : tactic => do
  concludeTac (← maybeAppliedFRToTerm e)

elab "On" " combine [" prfs:term,* "]" : tactic => do
  combineTac prfs.getElems

elab "On" " calcule " loc:(locationFR)? : tactic => do
  let loc ← loc.mapM locationFR_to_location
  computeTac loc

elab "On" " applique " exp:term : tactic => do
  evalApply (← `(tactic|apply $exp))

elab "On" " applique " exp:term " dans " h:ident: tactic => do
  let loc ← ident_to_location h
  evalTactic (← `(tactic|apply_fun $exp $loc:location))

elab "On" " applique " exp:term " à " e:term : tactic => do
  evalTactic (← `(tactic|specialize $exp $e))

macro "On" " oublie" args:(ppSpace colGt term:max)+ : tactic => `(tactic|clear $args*)

macro "On" " reformule " h:ident " en " new:term : tactic => `(tactic|change $new at $h:ident)

implement_endpoint (lang := fr) renameResultSeveralLoc : CoreM String :=
pure "On ne peut spécifier le résultat du renommage que lorsqu’on ne renomme qu’à un seul endroit."

elab "On" " renomme" old:ident " en " new:ident loc:(locationFR)? become?:(becomesFR)? : tactic => do
  let loc? ← loc.mapM locationFR_to_location
  renameTac old new loc? (become?.map extractBecomesFR)

implement_endpoint (lang := fr) unfoldResultSeveralLoc : CoreM String :=
pure "On ne peut spécifier le résultat du dépliage que lorsqu’on ne déplie qu’à un seul endroit."

elab "On" " déplie " tgt:ident loc:(locationFR)? new:(becomesFR)? : tactic => do
  let loc? ← loc.mapM locationFR_to_location
  let new? := new.map extractBecomesFR
  unfoldTac tgt loc? new?

elab "On" " contrapose" : tactic => contraposeTac true

elab "On" " contrapose" " simplement": tactic => contraposeTac false

elab "On " " pousse la négation " l:(location)? new:(becomesFR)? : tactic => do
  pushNegTac (l.map expandLocation) (new.map extractBecomesFR)

implement_endpoint (lang := fr) rwResultWithoutGoal : CoreM String :=
pure "On ne peut spécifier le résultat de la réécriture que lorsqu’il reste quelque chose à démontrer."

implement_endpoint (lang := fr) rwResultSeveralLoc : CoreM String :=
pure "On ne peut spécifier le résultat de la réécriture que lorsqu’on ne réécrit qu’à un seul endroit."

implement_endpoint (lang := fr) cannotContrapose : CoreM String :=
pure "Il est impossible de contraposer car le but n’est pas une implication."

setLang fr

example (P Q : Prop) (h : P ∨ Q) : True := by
  On discute en utilisant h
  . intro _hP
    trivial
  . intro _hQ
    trivial


example (P : Prop) : True := by
  On discute selon que P
  . intro _hP
    trivial
  . intro _hnP
    trivial

set_option linter.unusedVariables false in
example (P Q R : Prop) (hRP : R → P) (hR : R) (hQ : Q) : P := by
  success_if_fail_with_msg "application type mismatch
  hRP hQ
argument
  hQ
has type
  Q : Prop
but is expected to have type
  R : Prop"
    On conclut par hRP appliqué à hQ
  On conclut par hRP appliqué à hR

example (P : ℕ → Prop) (h : ∀ n, P n) : P 0 := by
  On conclut par h appliqué à _

example (P : ℕ → Prop) (h : ∀ n, P n) : P 0 := by
  On conclut par h

example {a b : ℕ}: a + b = b + a := by
  On calcule

example {a b : ℕ} (h : a + b - a = 0) : b = 0 := by
  On calcule dans h
  On conclut par h

variable (k : Nat)

example (h : True) : True := by
  On conclut par h

example (h : ∀ _n : ℕ, True) : True := by
  On conclut par h appliqué à 0

example (h : True → True) : True := by
  On applique h
  trivial

example (h : ∀ _n _k : ℕ, True) : True := by
  On conclut par h appliqué à 0 et 1

example (a b : ℕ) (h : a < b) : a ≤ b := by
  On conclut par h

example (a b c : ℕ) (h : a < b ∧ a < c) : a ≤ b := by
  On conclut par h

example (a b c : ℕ) (h : a ≤ b) (h' : b ≤ c) : a ≤ c := by
  On combine [h, h']

example (a b c : ℤ) (h : a = b + c) (h' : b - a = c) : c = 0 := by
  On combine [h, h']

example (a b c : ℕ) (h : a ≤ b) (h' : b ≤ c ∧ a+b ≤ a+c) : a ≤ c := by
  On combine [h, h']

example (a b c : ℕ) (h : a = b) (h' : a = c) : b = c := by
  On réécrit via ← h
  On conclut par h'

example (a b c : ℕ) (h : a = b) (h' : a = c) : b = c := by
  On réécrit via h dans h'
  On conclut par h'

example (a b : Nat) (h : a = b) (h' : b = 0): a = 0 := by
  On réécrit via ← h dans h' qui devient a = 0
  exact h'

example (a b : Nat) (h : a = b) (h' : b = 0): a = 0 := by
  On réécrit via ← h dans h'
  clear h
  exact h'

example (f : ℕ → ℕ) (n : ℕ) (h : n > 0 → f n = 0) (hn : n > 0): f n = 0 := by
  On réécrit via h
  exact hn

example (f : ℕ → ℕ) (h : ∀ n > 0, f n = 0) : f 1 = 0 := by
  On réécrit via h
  norm_num

example (a b c : ℕ) (h : a = b) (h' : a = c) : b = c := by
  success_if_fail_with_msg "Le terme fourni
  a = c
n’est pas égal par définition à celui attendu
  b = c"
    On réécrit via [h] dans h' qui devient a = c
  On réécrit via [h] dans h' qui devient b = c
  On conclut par h'

example (a b c : ℕ) (h : a = b) (h' : a = c) : a = c := by
  On réécrit via h partout
  On conclut par h'


example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  On applique h à h'
  On conclut par h

example (P Q R : Prop) (h : P → Q → R) (hP : P) (hQ : Q) : R := by
  On conclut par h appliqué à hP et hQ

example (f : ℕ → ℕ) (a b : ℕ) (h : a = b) : f a = f b := by
  On applique f dans h
  On conclut par h

example (P : ℕ → Prop) (h : ∀ n, P n) : P 0 := by
  On applique h à 0
  On conclut par h

example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 := by
  On contrapose
  intro h
  use x/2
  constructor
  · On conclut par h
  · On conclut par h

example (ε : ℝ) (h : ε > 0) : ε ≥ 0 := by On conclut par h
example (ε : ℝ) (h : ε > 0) : ε/2 > 0 := by On conclut par h
example (ε : ℝ) (h : ε > 0) : ε ≥ -1 := by On conclut par h
example (ε : ℝ) (h : ε > 0) : ε/2 ≥ -3 := by On conclut par h

example (x : ℝ) (h : x = 3) : 2*x = 6 := by On conclut par h

example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 := by
  On contrapose simplement
  intro h
  On pousse la négation
  On pousse la négation at h
  use x/2
  constructor
  On conclut par h
  On conclut par h

example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 := by
  On contrapose simplement
  intro h
  success_if_fail_with_msg "Le terme fourni
  0 < x
n’est pas égal par définition à celui attendu
  ∃ ε > 0, ε < x"
    On pousse la négation qui devient 0 < x
  On pousse la négation
  success_if_fail_with_msg "Le terme fourni
  ∃ ε > 0, ε < x
n’est pas égal par définition à celui attendu
  0 < x"
    On pousse la négation at h qui devient ∃ (ε : ℝ), ε > 0 ∧ ε < x
  On pousse la négation at h qui devient 0 < x
  use x/2
  constructor
  On conclut par h
  On conclut par h

def test_majorant (A : Set ℝ) (x : ℝ) := ∀ a ∈ A, a ≤ x
def test_borne_sup (A : Set ℝ) (x : ℝ) := test_majorant A x ∧ ∀ y, test_majorant A y → x ≤ y

example {A : Set ℝ} {x : ℝ} (hx : test_borne_sup A x) :
∀ y, y < x → ∃ a ∈ A, y < a := by
  intro y
  On contrapose
  rcases hx with ⟨hx₁, hx₂⟩
  exact hx₂ y

set_option linter.unusedVariables false in
example : (∀ n : ℕ, false) → 0 = 1 := by
  On contrapose
  On calcule

example (P Q : Prop) (h : P ∨ Q) : True := by
  On discute en utilisant h
  all_goals
    intro
    trivial

example (P : Prop) (hP₁ : P → True) (hP₂ : ¬ P → True): True := by
  On discute selon que P
  intro h
  exact hP₁ h
  intro h
  exact hP₂ h

namespace Verbose.French
set_option linter.unusedVariables false

def f (n : ℕ) := 2*n

example : f 2 = 4 := by
  On déplie f
  rfl

example (h : f 2 = 4) : True → True := by
  On déplie f dans h
  guard_hyp h :ₛ 2*2 = 4
  exact id

example (h : f 2 = 4) : True → True := by
  success_if_fail_with_msg "hypothesis h has type
  2 * 2 = 4
not
  2 * 2 = 5"
    On déplie f dans h qui devient 2*2 = 5
  success_if_fail_with_msg "hypothesis h has type
  2 * 2 = 4
not
  Verbose.French.f 2 = 4"
    On déplie f dans h qui devient f 2 = 4
  On déplie f dans h qui devient 2*2 = 4
  exact id

set_option linter.unusedTactic false

example (P : ℕ → ℕ → Prop) (h : ∀ n : ℕ, ∃ k, P n k) : True := by
  On renomme n en p dans h
  On renomme k en l dans h
  guard_hyp_strict h : ∀ p, ∃ l, P p l
  trivial

example (P : ℕ → ℕ → Prop) (h : ∀ n : ℕ, ∃ k, P n k) : True := by
  On renomme n en p dans h qui devient ∀ p, ∃ k, P p k
  On renomme k en l dans h
  success_if_fail_with_msg "hypothesis h has type
  ∀ (p : ℕ), ∃ l, P p l
not
  ∀ (p : ℕ), ∃ j, P p j"
    On renomme k en l dans h qui devient ∀ p, ∃ j, P p j
  On renomme k en l dans h qui devient ∀ p, ∃ l, P p l
  guard_hyp_strict h :  ∀ p, ∃ l, P p l
  trivial

example (P : ℕ → ℕ → Prop) : (∀ n : ℕ, ∃ k, P n k) ∨ True := by
  On renomme n en p
  On renomme k en l
  guard_target_strict (∀ p, ∃ l, P p l) ∨ True
  right
  trivial

example (a b c : ℕ) : True := by
  On oublie a
  On oublie b c
  trivial

example (h : 1 + 1 = 2) : True := by
  success_if_fail_with_msg "type mismatch
  this
has type
  2 = 3 : Prop
but is expected to have type
  1 + 1 = 2 : Prop"
    On reformule h en 2 = 3
  On reformule h en 2 = 2
  trivial
