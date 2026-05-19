import Verbose.Tactics.We
import Verbose.Spanish.Common

open Lean Elab Parser Tactic Verbose.Spanish

syntax locationES := withPosition(" en la hipótesis " (locationWildcard <|> locationHyp))

def locationES_to_location : TSyntax `locationES → TacticM (TSyntax `Lean.Parser.Tactic.location)
| `(locationES|en la hipótesis $x) => `(location|at $x)
| _ => `(location|at *) -- should not happend

declare_syntax_cat becomesES
syntax colGt "que se convierte en " term : becomesES

def extractBecomesES (e : Lean.TSyntax `becomesES) : Lean.Term := ⟨e.raw[1]!⟩

elab rw:("Reescribimos "<|> "Reescribamos ") " usando " s:myRwRuleSeq l:(locationES)? new:(becomesES)? : tactic => do
  rewriteTac rw s (l.map expandLocation) (new.map extractBecomesES)

elab rw:("Reescribimos "<|> "Reescribamos ") " usando " s:myRwRuleSeq " en todas partes" : tactic => do
  rewriteTac rw s (some Location.wildcard) none

elab ("Procedemos "<|> "Procedamos ") " usando " exp:term : tactic =>
  discussOr exp

elab ("Procedemos "<|> "Procedamos ") " dependiendo de " exp:term : tactic =>
  discussEm exp

implement_endpoint (lang := es) cannotConclude : CoreM String :=
pure "No es concluyente."

elab ("Concluimos "<|> "Concluyamos ") " por " e:maybeAppliedES : tactic => do
  concludeTac (← maybeAppliedESToTerm e)

elab ("Combinamos "<|> "Combinemos ") prfs:sepBy(term, " yy ") : tactic => do
  combineTac prfs.getElems

implement_endpoint (lang := es) computeFailed (goal : MessageData) : TacticM MessageData :=
  pure m!"El objetivo {goal} no parece derivarse de ningún cálculo sin usar hipótesis locales."

elab ("Calculemos " <|> "Calculamos ") loc:(locationES)? : tactic => do
let loc ← loc.mapM locationES_to_location
computeTac loc

elab ("Usamos "<|> "Usemos ") exp:term : tactic => do
  evalApply (← `(tactic|apply $exp))

-- elab "We" " apply " exp:term " at " h:ident: tactic => do
--   let loc ← ident_to_location h
--   evalTactic (← `(tactic|apply_fun $exp $loc:location))

elab ("Usamos "<|> "Usemos ") exp:term " en " e:term : tactic => do
  evalTactic (← `(tactic|specialize $exp $e))

macro ("Olvidamos "<|> "Olvidemos ") args:(ppSpace colGt term:max)+ : tactic => `(tactic|clear $args*)

macro ("Reformulamos "<|> "Reformulemos ") h:ident " como " new:term : tactic => `(tactic|change $new at $h:ident)

implement_endpoint (lang := es) renameResultSeveralLoc : CoreM String :=
pure "Solo se puede especificar el cambio de nombre cuando el cambio se realiza en una única ubicación."

elab ("Renombramos "<|> "Renombremos ") old:ident " como " new:ident loc:(locationES)? become?:(becomesES)? : tactic => do
  let loc? ← loc.mapM locationES_to_location
  renameTac old new loc? (become?.map extractBecomesES)

implement_endpoint (lang := es) unfoldResultSeveralLoc : CoreM String :=
pure "Solo se puede especificar el despliegue cuando el cambio se realiza en una única ubicación."

elab ("Desarrollamos "<|> "Desarrollemos ") tgt:ident loc:(locationES)? new:(becomesES)? : tactic => do
  let loc? ← loc.mapM locationES_to_location
  let new? := (new.map extractBecomesES)
  unfoldTac tgt loc? new?

elab ("Contraponemos "<|> "Contrapongamos ") : tactic => contraposeTac true

elab ("Contraponemos "<|> "Contrapongamos ") " simplemente": tactic => contraposeTac false

elab ("Elaboramos "<|> "Elaboremos ") " la negación " l:(locationES)? new:(becomesES)? : tactic => do
  pushNegTac (l.map expandLocation) (new.map extractBecomesES)

implement_endpoint (lang := es) rwResultWithoutGoal : CoreM String :=
pure "Solo es posible especificar el resultado de la reescritura cuando aún queda algo por demostrar."

implement_endpoint (lang := es) rwResultSeveralLoc : CoreM String :=
pure "Solo es posible especificar el resultado de la reescritura cuando esta se realiza en una única ubicación."

implement_endpoint (lang := es) cannotContrapose : CoreM String :=
pure "No se puede contraponer: el objetivo principal no es una implicación."

setLang es

example (P Q : Prop) (h : P ∨ Q) : True := by
  Procedemos usando h
  . intro _hP
    trivial
  . intro _hQ
    trivial


example (P : Prop) : True := by
  Procedemos dependiendo de P
  . intro _hP
    trivial
  . intro _hnP
    trivial

set_option linter.unusedVariables false in
example (P Q R : Prop) (hRP : R → P) (hR : R) (hQ : Q) : P := by
  success_if_fail_with_msg "Application type mismatch: The argument
  hQ
has type
  Q
but is expected to have type
  R
in the application
  hRP hQ"
    Concluimos por hRP aplicado a hQ
  Concluimos por hRP aplicado a hR

example (P : ℕ → Prop) (h : ∀ n, P n) : P 0 := by
  Concluimos por h aplicado a _

example (P : ℕ → Prop) (h : ∀ n, P n) : P 0 := by
  Concluimos por h

example {a b : ℕ}: a + b = b + a := by
  Calculamos

example {a : ℕ}: 2*a + 1 ≥ a + 1 := by
  Calculemos

example {a b : ℕ} (h : a + b - a = 0) : b = 0 := by
  Calculemos en la hipótesis h
  Concluimos por h

addAnonymousComputeLemma abs_sub_le
addAnonymousComputeLemma abs_sub_comm

example {x y : ℝ} : |x - y| = |y - x| := by
  Calculemos

example {x y z : ℝ} : |x - y| ≤ |x - z| + |z - y| := by
  Calculemos

example {x y z : ℝ} : 2*|x - y| + 3 ≤ 2*(|x - z| + |z - y|) + 3 := by
  Calculemos

example (a : ℝ) (h : a ≤ 3) : a + 5 ≤ 3 + 5 := by
  success_if_fail_with_msg "El objetivo a + 5 ≤ 3 + 5 no parece derivarse de ningún cálculo sin usar hipótesis locales."
    Calculemos
  rel [h]

variable (k : Nat)

example (h : True) : True := by
  Concluimos por h

example (h : ∀ _n : ℕ, True) : True := by
  Concluimos por h aplicado a 0

example (h : True → True) : True := by
  Usamos h
  trivial

example (h : ∀ _n _k : ℕ, True) : True := by
  Concluimos por h aplicado a 0 yy 1

example (a b : ℕ) (h : a < b) : a ≤ b := by
  Concluimos por h

example (a b c : ℕ) (h : a < b ∧ a < c) : a ≤ b := by
  Concluimos por h

example (a b c : ℕ) (h : a ≤ b) (h' : b ≤ c) : a ≤ c := by
  Combinamos h yy h'

example (a b c : ℤ) (h : a = b + c) (h' : b - a = c) : c = 0 := by
  Combinamos h yy h'

example (a b c : ℕ) (h : a ≤ b) (h' : b ≤ c ∧ a+b ≤ a+c) : a ≤ c := by
  Combinamos h yy h'

example (a b c : ℕ) (h : a = b) (h' : a = c) : b = c := by
  Reescribimos usando ← h
  Concluimos por h'

example (a b c : ℕ) (h : a = b) (h' : a = c) : b = c := by
  Reescribimos usando h en la hipótesis h'
  Concluimos por h'

example (a b : Nat) (h : a = b) (h' : b = 0): a = 0 := by
  Reescribimos usando ← h en la hipótesis h' que se convierte en a = 0
  exact h'

example (a b : Nat) (h : a = b) (h' : b = 0): a = 0 := by
  Reescribimos usando ← h en la hipótesis h'
  clear h
  exact h'

example (f : ℕ → ℕ) (n : ℕ) (h : n > 0 → f n = 0) (hn : n > 0): f n = 0 := by
  Reescribimos usando h
  exact hn

example (f : ℕ → ℕ) (h : ∀ n > 0, f n = 0) : f 1 = 0 := by
  Reescribimos usando h
  norm_num

example (a b c : ℕ) (h : a = b) (h' : a = c) : b = c := by
/-   success_if_fail_with_msg "El término
  a = c
 no es igual por definición a
  b = c"
    Reescribamos usando h en la hipótesis h' que se convierte en a = c -/
  Reescribimos usando [h] en la hipótesis h' que se convierte en b = c
  Concluimos por h'

example (a b c : ℕ) (h : a = b) (h' : a = c) : a = c := by
  Reescribimos usando h en todas partes
  Concluimos por h'

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  Usamos h en h'
  Concluimos por h

example (P Q R : Prop) (h : P → Q → R) (hP : P) (hQ : Q) : R := by
  Concluimos por h aplicado a hP yy hQ

-- example (f : ℕ → ℕ) (a b : ℕ) (h : a = b) : f a = f b := by
--   Usamos f en la hipótesis h
--   Concluimos por h

example (P : ℕ → Prop) (h : ∀ n, P n) : P 0 := by
  Usamos h en 0
  Concluimos por h


example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 := by
  Contraponemos
  intro h
  use x/2
  constructor
  Concluimos por h
  Concluimos por h

example (ε : ℝ) (h : ε > 0) : ε ≥ 0 := by Concluimos por h
example (ε : ℝ) (h : ε > 0) : ε/2 > 0 := by Concluimos por h
example (ε : ℝ) (h : ε > 0) : ε ≥ -1 := by Concluimos por h
example (ε : ℝ) (h : ε > 0) : ε/2 ≥ -3 := by Concluimos por h

example (x : ℝ) (h : x = 3) : 2*x = 6 := by Concluimos por h

example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 := by
  Contraponemos simplemente
  intro h
  Elaboramos la negación
  Elaboramos la negación en la hipótesis h
  use x/2
  constructor
  · Concluimos por h
  · Concluimos por h

example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 := by
  Contraponemos simplemente
  intro h
/-   success_if_fail_with_msg "El término
  0 < x
 no es igual por definición a
  ∃ ε > 0, ε < x"
    Elaboremos la negación que se convierte en 0 < x -/
  Elaboramos la negación que se convierte en ∃ ε > 0, ε < x
/-   success_if_fail_with_msg "El término
  ∃ ε > 0, ε < x
 no es igual por definición a
  0 < x"
    Elaboramos la negación en la hipótesis h que se convierte en ∃ ε > 0, ε < x -/
  Elaboramos la negación en la hipótesis h que se convierte en 0 < x
  use x/2
  constructor
  · Concluimos por h
  · Concluimos por h

def test_ub (A : Set ℝ) (x : ℝ) := ∀ a ∈ A, a ≤ x
def test_sup (A : Set ℝ) (x : ℝ) := test_ub A x ∧ ∀ y, test_ub A y → x ≤ y

example {A : Set ℝ} {x : ℝ} (hx : test_sup A x) :
∀ y, y < x → ∃ a ∈ A, y < a := by
  intro y
  Contraponemos
  rcases hx with ⟨hx₁, hx₂⟩
  exact hx₂ y

set_option linter.unusedVariables false in
example : (∀ n : ℕ, False) → 0 = 1 := by
  Contraponemos
  intro h
  use 1

example (P Q : Prop) (h : P ∨ Q) : True := by
  Procedemos usando h
  all_goals
    intro
    trivial

example (P : Prop) (hP₁ : P → True) (hP₂ : ¬ P → True): True := by
  Procedemos dependiendo de P
  intro h
  exact hP₁ h
  intro h
  exact hP₂ h

set_option linter.unusedVariables false

namespace Verbose.Spanish

def f (n : ℕ) := 2*n

example : f 2 = 4 := by
  Desarrollamos  f
  rfl

example (h : f 2 = 4) : True → True := by
  Desarrollamos f en la hipótesis h
  guard_hyp h :ₛ 2*2 = 4
  exact id

example (h : f 2 = 4) : True → True := by
  success_if_fail_with_msg "hypothesis h has type
  2 * 2 = 4
not
  2 * 2 = 5"
    Desarrollamos f en la hipótesis h que se convierte en 2*2 = 5
  success_if_fail_with_msg "hypothesis h has type
  2 * 2 = 4
not
  Verbose.Spanish.f 2 = 4"
    Desarrollamos f en la hipótesis h que se convierte en f 2 = 4
  Desarrollamos f en la hipótesis h que se convierte en 2*2 = 4
  exact id

set_option linter.unusedTactic false

example (P : ℕ → ℕ → Prop) (h : ∀ n : ℕ, ∃ k, P n k) : True := by
  Renombremos  n como p en la hipótesis h
  Renombremos  k como l en la hipótesis h
  guard_hyp_strict h : ∀ p, ∃ l, P p l
  trivial

example (P : ℕ → ℕ → Prop) (h : ∀ n : ℕ, ∃ k, P n k) : True := by
  Renombremos  n como p en la hipótesis h que se convierte en ∀ p, ∃ k, P p k
  success_if_fail_with_msg "hypothesis h has type
  ∀ (p : ℕ), ∃ l, P p l
not
  ∀ (p : ℕ), ∃ j, P p j"
    Renombremos  k como l en la hipótesis h que se convierte en ∀ p, ∃ j, P p j
  Renombremos  k como l en la hipótesis h que se convierte en ∀ p, ∃ l, P p l
  guard_hyp_strict h :  ∀ p, ∃ l, P p l
  trivial

example (P : ℕ → ℕ → Prop) : (∀ n : ℕ, ∃ k, P n k) ∨ True := by
  Renombremos  n como p
  Renombremos  k como l
  guard_target_strict (∀ p, ∃ l, P p l) ∨ True
  right
  trivial

example (a b c : ℤ) (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := by
  rcases h1 with ⟨k, hk⟩
  rcases h2 with ⟨l, hl⟩
  show ∃ k, c = a * k
  Renombremos  k como m
  guard_target_strict ∃ m, c = a * m
  use k*l
  rw [hl, hk]
  ring

example (a b c : ℕ) : True := by
  Olvidamos a
  Olvidamos b c
  trivial

example (h : 1 + 1 = 2) : True := by
  success_if_fail_with_msg "
'change' tactic failed, pattern
  2 = 3
is not definitionally equal to target
  1 + 1 = 2"
    Reformulemos h como 2 = 3
  Reformulemos h como 2 = 2
  trivial
