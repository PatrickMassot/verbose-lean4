import Verbose.Tactics.Help
import Verbose.Tactics.Notations
import Verbose.English.Tactics

open Lean Meta Elab Tactic Term Verbose

namespace Verbose.English

def describe (t : Format) : String :=
match toString t with
| "ℝ" => "a real number"
| "ℕ" => "a natural number"
| "ℤ" => "an integer"
| t => "an expression with type " ++ t

def describe_pl (t : Format) : String :=
match toString t with
| "ℝ" => "some real numbers"
| "ℕ" => "some natural numbers"
| "ℤ" => "some integers"
| t => "some expressions with type " ++ t

def libre (s : Ident) : String := s!"The name {s.getId} can be chosen freely among available names."

def printIdentList (l : List Ident) : String := commaSep <| l.toArray.map (toString ·.getId)

def libres (ls : List Ident) : String :=
s!"The names {printIdentList ls} can be chosen freely among available names."

def describeHypShape (hyp : Name) (headDescr : String) : SuggestionM Unit :=
  pushCom "The assumption {hyp} has shape “{headDescr}”"

def describeHypStart (hyp : Name) (headDescr : String) : SuggestionM Unit :=
  pushCom "The assumption {hyp} starts with “{headDescr}”"


endpoint (lang := en) helpExistRelSuggestion (hyp : Name) (headDescr : String)
    (nameS ineqIdent hS : Ident) (ineqS pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term we get $nameS:ident such that ($ineqIdent : $ineqS) ($hS : $pS))
  pushComment <| libres [nameS, ineqIdent, hS]

endpoint (lang := en) helpConjunctionSuggestion (hyp : Name) (h₁I h₂I : Ident) (p₁S p₂S : Term) :
    SuggestionM Unit := do
  let headDescr := "... and ..."
  describeHypShape hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term we get ($h₁I : $p₁S) ($h₂I : $p₂S))
  pushComment <| libres [h₁I, h₂I]

endpoint (lang := en) helpDisjunctionSuggestion (hyp : Name) : SuggestionM Unit := do
  pushCom "The assumption {hyp} has shape « ... or ... »"
  pushCom "One can use it with:"
  pushTac `(tactic|We proceed using $hyp.ident:term)

endpoint (lang := en) helpImplicationSuggestion (hyp HN H'N : Name) (closes : Bool)
    (le re : Expr) : SuggestionM Unit := do
  pushCom "The assumption {hyp} is an implication"
  if closes then do
    pushCom "The conclusion of this implication is the current goal"
    pushCom "Hence one can use this assumption with:"
    pushTac `(tactic| By $hyp.ident:term it suffices to prove $(← le.stx))
    flush
    pushCom "If one already has a proof {HN} of {← le.fmt} then one can use:"
    pushTac `(tactic|We conclude by $hyp.ident:term applied to $HN.ident)
  else do
    pushCom "The premise of this implication is {← le.fmt}"
    pushCom "If you have a proof {HN} of {← le.fmt}"
    pushCom "you can use this assumption with:"
    pushTac `(tactic|By $hyp.ident:term applied to $HN.ident:term we get $H'N.ident:ident : $(← re.stx):term)
    pushComment <| libre H'N.ident

endpoint (lang := en) helpEquivalenceSuggestion (hyp hyp'N : Name) (l r : Expr) : SuggestionM Unit := do
  pushCom "The assumption {hyp} is an equivalence"
  pushCom "One can use it to replace the left-hand-side (namely {← l.fmt}) by the right-hand side (namely {← r.fmt}) in the goal with:"
  pushTac `(tactic|We rewrite using $hyp.ident:term)
  flush
  pushCom "One can use it to replace the right-hand-side in the goal with:"
  pushTac `(tactic|We rewrite using ← $hyp.ident)
  flush
  pushCom "One can also perform such replacements in an assumption {hyp'N} with"
  pushTac `(tactic|We rewrite using $hyp.ident:term at $hyp'N.ident:ident)
  flush
  pushCom "or"
  pushTac `(tactic|We rewrite using ← $hyp.ident:term at $hyp'N.ident:ident)

endpoint (lang := en) helpEqualSuggestion (hyp hyp' : Name) (closes : Bool) (l r : Expr) :
    SuggestionM Unit := do
  pushCom "The assumption {hyp} is an equality"
  if closes then
    pushComment <| s!"The current goal follows from it immediately"
    pushComment   "One can use it with:"
    pushTac `(tactic|We conclude by $hyp.ident:ident)
  else do
    pushCom "One can use it to replace the left-hand-side (namely {← l.fmt}) by the right-hand side (namely {← r.fmt}) in the goal with:"
    pushTac `(tactic|We rewrite using $hyp.ident:ident)
    flush
    pushCom "One can use it to replace the right-hand-side in the goal with:"
    pushTac `(tactic|We rewrite using ← $hyp.ident:ident)
    flush
    pushCom "One can also perform such replacements in an assumption {hyp'} with"
    pushTac `(tactic|We rewrite using $hyp.ident:ident at $hyp'.ident:ident)
    flush
    pushCom "or"
    pushTac `(tactic|We rewrite using ← $hyp.ident:ident at $hyp'.ident:ident)
    flush
    pushCom "One can also use it in a computation step, or combine it linearly to others with:"
    pushTac `(tactic|We combine [$hyp.ident:term, ?_])
    pushCom "replacing the question mark by one or more terms proving equalities."

endpoint (lang := en) helpIneqSuggestion (hyp : Name) (closes : Bool) : SuggestionM Unit := do
  pushCom "The assumption {hyp} is an inequality"
  if closes then
    flush
    pushCom "It immediately implies the current goal."
    pushCom "One can use it with:"
    pushTac `(tactic|We conclude by $hyp.ident:ident)
  else do
    flush
    pushCom "One can also use it in a computation step, or combine it linearly to others with:"
    pushTac `(tactic|We combine [$hyp.ident:term, ?_])
    pushCom "replacing the question mark by one or more terms proving equalities or inequalities."

endpoint (lang := en) helpMemInterSuggestion (hyp h₁ h₂ : Name) (elemS p₁S p₂S : Term) :
    SuggestionM Unit := do
  pushCom "The assumption {hyp} claims membership to an intersection"
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term we get ($h₁.ident : $elemS ∈ $p₁S) ($h₂.ident : $elemS ∈ $p₂S))
  pushComment <| libres [h₁.ident, h₂.ident]

endpoint (lang := en) helpMemUnionSuggestion (hyp : Name) :
    SuggestionM Unit := do
  pushCom "The assumption {hyp} claims membership to a union"
  pushCom "One can use it with:"
  pushTac `(tactic|We proceed using $hyp.ident)

endpoint (lang := en) helpGenericMemSuggestion (hyp : Name) : SuggestionM Unit := do
  pushCom "The assumption {hyp} is a membership"

endpoint (lang := en) helpContradictiomSuggestion (hypId : Ident) : SuggestionM Unit := do
  pushComment <| "This assumption is a contradiction."
  pushCom "One can deduce anything from it with:"
  pushTac `(tactic|(Let's prove it's contradictory
                    We conclude by $hypId:ident))

endpoint (lang := en) helpSubsetSuggestion (hyp x hx hx' : Name)
    (r : Expr) (l ambientTypePP : Format) : SuggestionM Unit := do
  pushCom "The assumption {hyp} ensures the inclusion of {l} in {← r.fmt}."
  pushCom "One can use it with:"
  pushTac `(tactic| By $hyp.ident:ident applied to $x.ident using $hx.ident we get $hx'.ident:ident : $x.ident ∈ $(← r.stx))
  pushCom "where {x} is {describe ambientTypePP} and {hx} proves that {x} ∈ {l}"

endpoint (lang := en) assumptionClosesSuggestion (hypId : Ident) : SuggestionM Unit := do
  pushCom "This assumption is exactly what needs to be proven"
  pushCom "One can use it with:"
  pushTac `(tactic|We conclude by $hypId:ident)

endpoint (lang := en) assumptionUnfoldingSuggestion (hypId : Ident) (expandedHypTypeS : Term) :
    SuggestionM Unit := do
  pushCom "This assumption starts with the application of a definition."
  pushCom "One can explicit it with:"
  pushTac `(tactic|We reformulate $hypId:ident as $expandedHypTypeS)
  flush

endpoint (lang := en) helpForAllRelExistsRelSuggestion (hyp var_name' n₀ hn₀ : Name)
    (headDescr hypDescr : String) (t : Format) (hn'S ineqIdent : Ident) (ineqS p'S : Term) :
    SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term applied to $n₀.ident using $hn₀.ident we get $var_name'.ident:ident such that ($ineqIdent : $ineqS) ($hn'S : $p'S))
  pushCom "where {n₀} is {describe t} and {hn₀} is a proof of the fact that {hypDescr}."
  pushComment <| libres [var_name'.ident, ineqIdent, hn'S]

endpoint (lang := en) helpForAllRelExistsSimpleSuggestion (hyp n' hn' n₀ hn₀ : Name)
    (headDescr n₀rel : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term applied to $n₀.ident using $hn₀.ident we get $n'.ident:ident such that ($hn'.ident : $p'S))
  pushCom "where {n₀} is {describe t} and {hn₀} is a proof of the fact that {n₀rel}"
  pushComment <| libres [n'.ident, hn'.ident]

endpoint (lang := en) helpForAllRelGenericSuggestion (hyp n₀ hn₀ : Name)
    (headDescr n₀rel : String) (t : Format) (newsI : Ident) (pS : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term applied to $n₀.ident using $hn₀.ident we get ($newsI : $pS))
  pushCom "where {n₀} is {describe t} and {hn₀} is a proof of the fact that {n₀rel}"
  pushComment <| libre newsI

endpoint (lang := en) helpForAllSimpleExistsRelSuggestion (hyp var_name' nn₀ : Name)
    (headDescr : String) (t : Format) (hn'S ineqIdent : Ident) (ineqS p'S : Term) :
    SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term applied to $nn₀.ident we get $var_name'.ident:ident such that ($ineqIdent : $ineqS) ($hn'S : $p'S))
  pushCom "where {nn₀} is {describe t}"
  pushComment <| libres [var_name'.ident, ineqIdent, hn'S]

endpoint (lang := en) helpForAllSimpleExistsSimpleSuggestion (hyp var_name' hn' nn₀  : Name)
    (headDescr : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term applied to $nn₀.ident we get $var_name'.ident:ident such that ($hn'.ident : $p'S))
  pushCom "where {nn₀} is {describe t}"
  pushComment <| libres [var_name'.ident, hn'.ident]

endpoint (lang := en) helpForAllSimpleForAllRelSuggestion (hyp nn₀ var_name'₀ H h : Name)
    (headDescr rel₀ : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  pushCom "The assumption {hyp} starts with “{headDescr}"
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term applied to [$nn₀.ident, $var_name'₀.ident, $H.ident] we get ($h.ident : $p'S))
  pushCom "where {nn₀} and {var_name'₀} are {describe_pl t} and {H} is a proof of {rel₀}"
  pushComment <| libre h.ident

endpoint (lang := en) helpForAllSimpleGenericSuggestion (hyp nn₀ hn₀ : Name) (headDescr : String)
    (t : Format) (pS : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term applied to $nn₀.ident we get ($hn₀.ident : $pS))
  pushCom "where {nn₀} is {describe t}"
  pushComment <| libre hn₀.ident
  flush
  pushCom "If this assumption won't be used again in its general shape, one can also specialize {hyp} with"
  pushTac `(tactic|We apply $hyp.ident:ident to $nn₀.ident)

endpoint (lang := en) helpForAllSimpleGenericApplySuggestion (prf : Expr) (but : Format) :
    SuggestionM Unit := do
  let prfS ← prf.toMaybeApplied
  pushCom "Since the goal is {but}, one can use:"
  pushTac `(tactic|We conclude by $prfS)

endpoint (lang := en) helpExistsSimpleSuggestion (hyp n hn : Name) (headDescr : String)
    (pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term we get $n.ident:ident such that ($hn.ident : $pS))
  pushComment <| libres [n.ident, hn.ident]

endpoint (lang := en) helpDataSuggestion (hyp : Name) (t : Format) : SuggestionM Unit := do
  pushComment <| s!"The object {hyp}" ++ match t with
    | "ℝ" => " is a fixed real number."
    | "ℕ" => " is a fixed natural number."
    | "ℤ" => " is a fixed integer."
    | s => s!" : {s} is fixed."

endpoint (lang := en) helpNothingSuggestion : SuggestionM Unit := do
  pushCom "I have nothing to say about this assumption."
  flush

def descrGoalHead (headDescr : String) : SuggestionM Unit :=
 pushCom "The goal starts with “{headDescr}”"

def descrGoalShape (headDescr : String) : SuggestionM Unit :=
 pushCom "The goal has shape “{headDescr}”"

def descrDirectProof : SuggestionM Unit :=
 pushCom "Hence a direct proof starts with:"

endpoint (lang := en) helpUnfoldableGoalSuggestion (expandedGoalTypeS : Term) :
    SuggestionM Unit := do
  pushCom "The goal starts with the application of a definition."
  pushCom "One can explicit it with:"
  pushTac `(tactic|Let's prove that $expandedGoalTypeS)
  flush

endpoint (lang := en) helpAnnounceGoalSuggestion (actualGoalS : Term) : SuggestionM Unit := do
  pushCom "The next step is to announce:"
  pushTac `(tactic| Let's now prove that $actualGoalS)

endpoint (lang := en) helpFixSuggestion (headDescr : String) (ineqS : TSyntax `fixDecl) :
    SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Fix $ineqS)

endpoint (lang := en) helpExistsRelGoalSuggestion (headDescr : String) (n₀ : Name) (t : Format)
    (fullTgtS : Term) : SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Let's prove that $n₀.ident works : $fullTgtS)
  pushCom "replacing {n₀} by {describe t}"

endpoint (lang := en) helpExistsGoalSuggestion (headDescr : String) (nn₀ : Name) (t : Format)
    (tgt : Term) : SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Let's prove that $nn₀.ident works : $tgt)
  pushCom "replacing {nn₀} by {describe t}"

endpoint (lang := en) helpConjunctionGoalSuggestion (p p' : Term) : SuggestionM Unit := do
  descrGoalShape "... and ..."
  descrDirectProof
  pushTac `(tactic|Let's first prove that $p)
  pushCom "After finish this first proof, it will remain to prove that {← p'.fmt}"
  flush
  pushCom "One can also start with"
  pushTac `(tactic|Let's first prove that $p')
  pushCom "then, after finishing this first proof, il will remain to prove that {← p.fmt}"

endpoint (lang := en) helpDisjunctionGoalSuggestion (p p' : Term) : SuggestionM Unit := do
  descrGoalShape "... or ..."
  pushCom "Hence a direct proof starts with announcing which alternative will be proven:"
  pushTac `(tactic|Let's prove that $p)
  flush
  pushCom "or:"
  pushTac `(tactic|Let's prove that $p')

endpoint (lang := en) helpImplicationGoalSuggestion (headDescr : String) (Hyp : Name)
    (leStx : Term) : SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic| Assume $Hyp.ident:ident : $leStx)
  pushComment <| libre Hyp.ident

endpoint (lang := en) helpEquivalenceGoalSuggestion (r l : Format) (rS lS : Term) :
    SuggestionM Unit := do
  pushCom "The goal is an equivalence. One can announce the proof of the left to right implication with:"
  pushTac `(tactic|Let's prove that $lS → $rS)
  pushCom "After proving this first statement, it will remain to prove that {r} → {l}"
  flush
  pushCom "One can also start with"
  pushTac `(tactic|Let's prove that $rS → $lS)
  pushCom "then, after finishing this first proof, il will remain to prove that {l} → {r}"

endpoint (lang := en) helpSetEqSuggestion (l r : Format) (lS rS : Term) : SuggestionM Unit := do
  -- **FIXME** this discussion isn't easy to do using tactics.
  pushCom "The goal is a set equality"
  pushCom "One can prove it by rewriting with `We rewrite using`"
  pushCom "or start a computation using"
  pushCom "  calc {l} = sorry := by sorry"
  pushCom "  ... = {r} := by sorry"
  pushCom "One can also prove it by double inclusion."
  pushCom "In this case the proof starts with:"
  pushTac `(tactic|Let's first prove that $lS ⊆ $rS)

endpoint (lang := en) helpEqGoalSuggestion (l r : Format) : SuggestionM Unit := do
  -- **FIXME** this discussion isn't easy to do using tactics.
  pushCom "The goal is an equality"
  pushCom "One can prove it by rewriting with `We rewrite using`"
  pushCom "or start a computation using"
  pushCom "  calc {l} = sorry := by sorry"
  pushCom "  ... = {r} := by sorry"
  pushCom "Of course one can have more intermediate steps."
  pushCom "One can also make linear combination of assumptions hyp₁ hyp₂... with"
  pushCom "  We combine [hyp₁, hyp₂]"

endpoint (lang := en) helpIneqGoalSuggestion (l r : Format) (rel : String) : SuggestionM Unit := do
  -- **FIXME** this discussion isn't easy to do using tactics.
  pushCom "The goal is an inequality"
  pushCom "One can start a computation using"
  pushCom "  calc {l}{rel}sorry := by sorry "
  pushCom "  ... = {r} := by sorry "
  pushCom "Of course one can have more intermediate steps."
  pushCom "The last computation line is not necessarily an equality, it can be an inequality."
  pushCom "Similarly the first line could be an equality. In total, the relation symbols"
  pushCom "must chain to give {rel}"
  pushCom "One can also make linear combination of assumptions hyp₁ hyp₂... with"
  pushCom "  We combine [hyp₁, hyp₂]"

endpoint (lang := en) helpMemInterGoalSuggestion (elem le : Expr) : SuggestionM Unit := do
  pushCom "The goal is prove {← elem.fmt} belongs to the intersection of {← le.fmt} with another set."
  pushCom "Hance a direct proof starts with:"
  pushTac `(tactic|Let's first prove that $(← elem.stx) ∈ $(← le.stx))

endpoint (lang := en) helpMemUnionGoalSuggestion (elem le re : Expr) : SuggestionM Unit := do
  pushCom "The goal is to prove {← elem.fmt} belongs to the union of {← le.fmt} and {← re.fmt}."
  descrDirectProof
  pushTac `(tactic|Let's prove that $(← elem.stx) ∈ $(← le.stx))
  flush
  pushCom "or by:"
  pushTac `(tactic|Let's prove that $(← elem.stx) ∈ $(← re.stx))

endpoint (lang := en) helpNoIdeaGoalSuggestion : SuggestionM Unit := do
  pushCom "No idea."

endpoint (lang := en) helpSubsetGoalSuggestion (l r : Format) (xN : Name) (lT : Term) :
    SuggestionM Unit := do
  pushCom "The goal is the inclusion {l} ⊆ {r}"
  descrDirectProof
  pushTac `(tactic| Fix $xN.ident:ident ∈ $lT)
  pushComment <| libre xN.ident

endpoint (lang := en) helpFalseGoalSuggestion : SuggestionM Unit := do
  pushCom "The goal is to prove a contradiction."
  pushCom "One can apply an assumption which is a negation"
  pushCom "namely, by definition, with shape P → false."

set_option linter.unusedVariables false

configureAnonymousSplitLemmas Iff.intro Iff.intro' And.intro And.intro' abs_le_of_le_le abs_le_of_le_le'

/--
info: Help
• By h applied to n₀ using hn₀ we get (hyp : P n₀)
-/
#guard_msgs in
example {P : ℕ → Prop} (h : ∀ n > 0, P n) : P 2 := by
  help h
  apply h
  norm_num

/--
info: Help
• By h we get n such that (n_pos : n > 0) (hn : P n)
-/
#guard_msgs in
example {P : ℕ → Prop} (h : ∃ n > 0, P n) : True := by
  help h
  trivial

/--
info: Help
• By h we get ε such that (ε_pos : ε > 0) (hε : P ε)
-/
#guard_msgs in
example {P : ℝ → Prop} (h : ∃ ε > 0, P ε) : True := by
  help h
  trivial

/--
info: Help
• By h applied to n₀ we get (hn₀ : P n₀ ⇒ Q n₀)
• We apply h to n₀
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : ∀ n, P n → Q n) (h' : P 2) : Q 2 := by
  help h
  exact h 2 h'

/--
info: Help
• By h applied to n₀ we get (hn₀ : P n₀)
• We apply h to n₀
• We conclude by h applied to 2
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∀ n, P n) : P 2 := by
  help h
  exact h 2

/--
info: Help
• By h it suffices to prove P 1
• We conclude by h applied to H
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 → Q 2) (h' : P 1) : Q 2 := by
  help h
  exact h h'

/--
info: Help
• By h applied to H we get H' : Q 2
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 → Q 2) : True := by
  help h
  trivial

/--
info: Help
• By h we get (h_1 : P 1) (h' : Q 2)
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 ∧ Q 2) : True := by
  help h
  trivial

/--
info: Help
• We rewrite using h
• We rewrite using ← h
• We rewrite using h at hyp
• We rewrite using ← h at hyp
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : (∀ n ≥ 2, P n) ↔  ∀ l, Q l) : True := by
  help h
  trivial

/--
info: Help
• Let's first prove that True
• Let's first prove that 1 = 1
-/
#guard_msgs in
example : True ∧ 1 = 1 := by
  help
  exact ⟨trivial, rfl⟩

/--
info: Help
• We proceed using h
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 ∨ Q 2) : True := by
  help h
  trivial

/--
info: Help
• Let's prove that True
• Let's prove that False
-/
#guard_msgs in
example : True ∨ False := by
  help
  left
  trivial

/-- info: I have nothing to say about this assumption. -/
#guard_msgs in
example (P : Prop) (h : P) : True := by
  help h
  trivial

/--
info: Help
• (
  Let's prove it's contradictory
  We conclude by h)
-/
#guard_msgs in
example (h : False) : 0 = 1 := by
  help h
  trivial

/--
info: Help
• By h applied to H we get H' : P l k
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (k l n : ℕ) (h : l - n = 0 → P l k) : True := by
  help h
  trivial

/--
info: Help
• By h applied to k₀ using hk₀ we get n such that (n_sup : n ≥ 3) (hn : ∀ (l : ℕ), l - n = 0 ⇒ P l k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  help h
  trivial

/--
info: Help
• By h applied to [k₀, n₀, H] we get (h_1 : ∀ (l : ℕ), l - n₀ = 0 ⇒ P l k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k, ∀ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  help h
  trivial

/--
info: Help
• By h applied to k₀ using hk₀ we get n_1 such that (n_1_sup : n_1 ≥ 3) (hn_1 : ∀ (l : ℕ), l - n = 0 ⇒ P l k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (n : ℕ) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  help h
  trivial

/--
info: Help
• By h we get n such that (n_sup : n ≥ 5) (hn : P n)
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∃ n ≥ 5, P n) : True := by
  help h
  trivial

/--
info: Help
• By h applied to k₀ using hk₀ we get n such that (n_sup : n ≥ 3) (hn : P n k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, P n k) : True := by
  help h
  trivial

/--
info: Help
• By h we get n such that (hn : P n)
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∃ n : ℕ, P n) : True := by
  help h
  trivial

/--
info: Help
• By h applied to k₀ we get n such that (hn : P n k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k, ∃ n : ℕ, P n k) : True := by
  help h
  trivial

/--
info: Help
• By h applied to k₀ using hk₀ we get n such that (hn : P n k₀)
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n : ℕ, P n k) : True := by
  help h
  trivial

/--
info: Help
• Let's prove that n₀ works: P n₀ ⇒ True
-/
#guard_msgs in
example (P : ℕ → Prop): ∃ n : ℕ, P n → True := by
  help
  use 0
  tauto

/--
info: Help
• Assume hyp : P
-/
#guard_msgs in
example (P Q : Prop) (h : Q) : P → Q := by
  help
  exact fun _ ↦ h

/--
info: Help
• Fix n ≥ 0
-/
#guard_msgs in
example : ∀ n ≥ 0, True := by
  help
  intros
  trivial

/--
info: Help
• Fix n : ℕ
-/
#guard_msgs in
example : ∀ n : ℕ, 0 ≤ n := by
  help
  exact Nat.zero_le

/--
info: Help
• Let's prove that n₀ works: 0 ≤ n₀
-/
#guard_msgs in
example : ∃ n : ℕ, 0 ≤ n := by
  help
  use 1
  exact Nat.zero_le 1

/--
info: Help
• Let's prove that n₀ works: n₀ ≥ 1 ∧ True
-/
#guard_msgs in
example : ∃ n ≥ 1, True := by
  help
  use 1

/-- info: I have nothing to say about this assumption. -/
#guard_msgs in
example (h : Odd 3) : True := by
  help h
  trivial

/--
info: Help
• Fix x ∈ s
---
info: Help
• By h applied to x_1 using hx we get hx' : x_1 ∈ t
-/
#guard_msgs in
example (s t : Set ℕ) (h : s ⊆ t) : s ⊆ t := by
  help
  Fix x ∈ s
  help h
  exact h x_mem

/--
info: Help
• By h we get (h_1 : x ∈ s) (h' : x ∈ t)
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∩ t) : x ∈ s := by
  help h
  By h we get (h_1 : x ∈ s) (h' : x ∈ t)
  exact h_1

/--
info: Help
• By h we get (h_1 : x ∈ s) (h' : x ∈ t)
---
info: Help
• Let's first prove that x ∈ t
---
info: Help
• Let's now prove that x ∈ s
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∩ t) : x ∈ t ∩ s := by
  help h
  By h we get (h_1 : x ∈ s) (h' : x ∈ t)
  help
  Let's first prove that x ∈ t
  exact h'
  help
  Let's now prove that x ∈ s
  exact h_1

/--
info: Help
• We proceed using h
---
info: Help
• Let's prove that x ∈ t
• Let's prove that x ∈ s
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∪ t) : x ∈ t ∪ s := by
  help h
  We proceed using h
  Assume hyp : x ∈ s
  help
  Let's prove that x ∈ s
  exact hyp
  Assume hyp : x ∈ t
  Let's prove that x ∈ t
  exact  hyp
