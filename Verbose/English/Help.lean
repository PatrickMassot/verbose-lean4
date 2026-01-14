import Verbose.Tactics.Help
import Verbose.English.Tactics

open Lean Meta Elab Tactic Term Verbose

namespace Verbose.English

implement_endpoint (lang := en) try_this : CoreM String := pure "Try this: "

implement_endpoint (lang := en) apply_suggestion : CoreM String := pure "Apply suggestion"

open Lean.Parser.Tactic in
elab "help" h:(colGt ident)? : tactic => do
unless (← verboseConfigurationExt.get).useHelpTactic do
  throwError "The help tactic is not enabled."
match h with
| some h => do
    let (s, msg) ← gatherSuggestions (helpAtHyp (← getMainGoal) h.getId)
    if s.isEmpty then
      logInfo (msg.getD "No suggestion")
    else
      addSuggestions (← getRef) s (header := "Help")
| none => do
    let (s, msg) ← gatherSuggestions (helpAtGoal (← getMainGoal))
    if s.isEmpty then
      logInfo (msg.getD "No suggestion")
    else
      addSuggestions (← getRef) s (header := "Help")

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

implement_endpoint (lang := en) helpExistRelSuggestion (hyp : Name) (headDescr : String)
    (nameS ineqIdent hS : Ident) (ineqS pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term we get $nameS:ident such that ($ineqIdent : $ineqS) and ($hS : $pS))
  pushComment <| libres [nameS, ineqIdent, hS]

implement_endpoint (lang := en) helpSinceExistRelSuggestion (hyp : Name) (headDescr : String)
    (nameS ineqIdent hS : Ident) (hypS ineqS pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|Since $hypS:term we get $nameS:ident such that ($ineqIdent : $ineqS) and ($hS : $pS))
  pushComment <| libres [nameS, ineqIdent, hS]

implement_endpoint (lang := en) helpConjunctionSuggestion (hyp : Name) (h₁I h₂I : Ident) (p₁S p₂S : Term) :
    SuggestionM Unit := do
  let headDescr := "... and ..."
  describeHypShape hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term we get ($h₁I : $p₁S) ($h₂I : $p₂S))
  pushComment <| libres [h₁I, h₂I]

implement_endpoint (lang := en) helpSinceConjunctionSuggestion (hyp : Name) (h₁I h₂I : Ident) (p₁S p₂S : Term) :
    SuggestionM Unit := do
  let headDescr := "... and ..."
  describeHypShape hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|Since $p₁S:term ∧ $p₂S we get that $p₁S:term and $p₂S)

implement_endpoint (lang := en) helpDisjunctionSuggestion (hyp : Name) : SuggestionM Unit := do
  pushCom "The assumption {hyp} has shape « ... or ... »"
  pushCom "One can use it with:"
  pushTac `(tactic|We proceed using $hyp.ident:term)

implement_endpoint (lang := en) helpSinceDisjunctionSuggestion (hyp : Name) (p₁S p₂S : Term) : SuggestionM Unit := do
  describeHypShape hyp "... or ..."
  pushCom "One can use it with:"
  pushTac `(tactic|We discuss depending on whether $p₁S:term or $p₂S)

implement_endpoint (lang := en) helpImplicationSuggestion (hyp HN H'N : Name) (closes : Bool)
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

implement_endpoint (lang := en) helpSinceImplicationSuggestion (stmt goalS leS : Term) (hyp H'N : Name) (closes : Bool)
    (le re : Expr) : SuggestionM Unit := do
  pushCom "Assumption {hyp} is an implication"
  if closes then do
    pushCom "The conclusion of this implication is the current goal"
    pushCom "Hence one can use this assumption with:"
    pushTac `(tactic| Since $stmt:term it suffices to prove that $(← le.stx):term)
    flush
    pushCom "If you already have a proof of {← le.fmt} then one can use:"
    pushTac `(tactic|Since $stmt:term and $(← le.stx):term we conclude that $goalS)
  else do
    pushCom "The premise of this implication is {← le.fmt}"
    pushCom "If you have a proof of {← le.fmt}"
    pushCom "you can use this assumption with:"
    pushTac `(tactic|Since $stmt:term and $leS:term we get that $(← re.stx):term)

implement_endpoint (lang := en) helpEquivalenceSuggestion (hyp hyp'N : Name) (l r : Expr) : SuggestionM Unit := do
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

implement_endpoint (lang := en) helpSinceEquivalenceSuggestion
    (hyp : Name) (stmt : Term) (l r : Expr) (hyp' : Ident) : SuggestionM Unit := do
  pushCom "The assumption {hyp} is an equivalence"
  pushCom "One can use it to replace the left-hand-side (namely {← l.fmt}) by the right-hand side (namely {← r.fmt}) or the other way around in the goal with:"
  pushTac `(tactic|Since $stmt:term it suffices to prove that ?_)
  pushCom "replacing the question mark by the new goal."
  flush
  pushCom "One can also perform such replacements in a statement following from one of the current assumptions with"
  pushTac `(tactic|Since $stmt:term and ?_ we get that ?_)
  pushCom "replacing the first question mark by the fact where you want to replace and the second one by the new obtained fact."

implement_endpoint (lang := en) helpEqualSuggestion (hyp hyp' : Name) (closes : Bool) (l r : String) :
    SuggestionM Unit := do
  pushCom "The assumption {hyp} is an equality"
  if closes then
    pushComment <| s!"The current goal follows from it immediately"
    pushComment   "One can use it with:"
    pushTac `(tactic|We conclude by $hyp.ident:ident)
  else do
    pushCom "One can use it to replace the left-hand-side (namely {l}) by the right-hand side (namely {r}) in the goal with:"
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

implement_endpoint (lang := en) helpSinceEqualSuggestion (hyp : Name) (news : Ident)
    (closes : Bool) (l r : String) (leS reS goalS : Term) : SuggestionM Unit := do
  pushCom "The assumption {hyp} is an equality"
  let eq ← `($leS = $reS)
  if closes then
    pushComment <| s!"The current goal follows from it immediately"
    pushComment   "One can use it with:"
    pushTac `(tactic|Since $eq:term we conclude that $goalS)
  else do
    pushCom "One can use it to replace the left-hand-side (namely {l}) by the right-hand side (namely {r}) or the other way around in the goal with:"
    pushTac `(tactic|Since $eq:term it suffices to prove that ?_)
    pushCom "replacing the question mark by the new goal."
    flush
    pushCom "One can also perform such replacements in a statement following from one of the current assumptions with"
    pushTac `(tactic|Since $eq:term and ?_ we get that ?_)
    pushCom "replacing the first question mark by the fact where you want to replace and the second one by the new obtained fact."

implement_endpoint (lang := en) helpIneqSuggestion (hyp : Name) (closes : Bool) : SuggestionM Unit := do
  pushCom "The assumption {hyp} is an inequality"
  if closes then
    pushCom "It immediately implies the current goal."
    pushCom "One can use it with:"
    pushTac `(tactic|We conclude by $hyp.ident:ident)
  else do
    pushCom "One can also use it in a computation step, or combine it linearly to others with:"
    pushTac `(tactic|We combine [$hyp.ident:term, ?_])
    pushCom "replacing the question mark by one or more terms proving equalities or inequalities."

implement_endpoint (lang := en) helpSinceIneqSuggestion (hyp : Name) (stmt goal : Term) (closes : Bool) : SuggestionM Unit := do
  pushCom "The assumption {hyp} is an inequality"
  if closes then
    pushCom "It immediately implies the current goal."
    pushCom "One can use it with:"
    pushTac `(tactic|Since $stmt:term we conclude that $goal)
  else do
    flush
    pushCom "One can also use it in a computation step, or combine it linearly to others with:"
    pushTac `(tactic| Since $stmt:term and ?_ we conclude that $goal)
    pushCom "replacing the question mark by one or more terms proving equalities or inequalities."

implement_endpoint (lang := en) helpMemInterSuggestion (hyp h₁ h₂ : Name) (elemS p₁S p₂S : Term) :
    SuggestionM Unit := do
  pushCom "The assumption {hyp} claims membership to an intersection"
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term we get ($h₁.ident : $elemS ∈ $p₁S) ($h₂.ident : $elemS ∈ $p₂S))
  pushComment <| libres [h₁.ident, h₂.ident]

implement_endpoint (lang := en) helpSinceMemInterSuggestion (stmt : Term) (hyp h₁ h₂ : Name) (elemS p₁S p₂S : Term) :
    SuggestionM Unit := do
  let mem ← `($elemS ∈ $p₁S)
  pushCom "The assumption {hyp} claims membership to an intersection"
  pushCom "One can use it with:"
  pushTac `(tactic|Since $stmt:term we get that $mem:term and $elemS ∈ $p₂S)

implement_endpoint (lang := en) helpMemUnionSuggestion (hyp : Name) :
    SuggestionM Unit := do
  pushCom "The assumption {hyp} claims membership to a union"
  pushCom "One can use it with:"
  pushTac `(tactic|We proceed using $hyp.ident)

implement_endpoint (lang := en) helpSinceMemUnionSuggestion (elemS leS reS : Term) (hyp : Name) :
    SuggestionM Unit := do
  pushCom "The assumption {hyp} claims membership to a union"
  pushCom "One can use it with:"
  pushTac `(tactic|We discuss depending on whether $elemS ∈ $leS or $elemS ∈ $reS)

implement_endpoint (lang := en) helpGenericMemSuggestion (hyp : Name) : SuggestionM Unit := do
  pushCom "The assumption {hyp} is a membership"

implement_endpoint (lang := en) helpContradictionSuggestion (hypId : Ident) : SuggestionM Unit := do
  pushComment <| "This assumption is a contradiction."
  pushCom "One can deduce anything from it with:"
  pushTac `(tactic|(Let's prove it's contradictory
                    We conclude by $hypId:ident))

implement_endpoint (lang := en) helpSinceContradictionSuggestion
     (stmt goal : Term) : SuggestionM Unit := do
  pushComment <| "This assumption is a contradiction."
  pushCom "One can deduce the goal from it with:"
  pushTac `(tactic|Since $stmt:term we conclude that $goal)

implement_endpoint (lang := en) helpSubsetSuggestion (hyp x hx hx' : Name)
    (r : Expr) (l ambientTypePP : Format) : SuggestionM Unit := do
  pushCom "The assumption {hyp} ensures the inclusion of {l} in {← r.fmt}."
  pushCom "One can use it with:"
  pushTac `(tactic| By $hyp.ident:ident applied to $x.ident using $hx.ident we get $hx'.ident:ident : $x.ident ∈ $(← r.stx))
  pushCom "where {x} is {describe ambientTypePP} and {hx} proves that {x} ∈ {l}"
  pushComment <| libre hx'.ident

implement_endpoint (lang := en) helpSinceSubsetSuggestion (hyp x hx' : Name) (stmt : Term)
    (l r : Expr) (ambientTypePP : Format) : SuggestionM Unit := do
  let new ← `($x.ident ∈ $(← r.stx))
  pushCom "The assumption {hyp} ensures the inclusion of {← l.fmt} in {← r.fmt}."
  pushCom "One can use it with:"
  pushTac `(tactic| Since $stmt:term and $x.ident ∈ $(← l.stx) we get that $new:term)
  pushCom "where {x} is {describe ambientTypePP}"

implement_endpoint (lang := en) assumptionClosesSuggestion (hypId : Ident) : SuggestionM Unit := do
  pushCom "This assumption is exactly what needs to be proven"
  pushCom "One can use it with:"
  pushTac `(tactic|We conclude by $hypId:ident)

implement_endpoint (lang := en) assumptionUnfoldingSuggestion (hypId : Ident) (expandedHypTypeS : Term) :
    SuggestionM Unit := do
  pushCom "This assumption starts with the application of a definition."
  pushCom "One can make it explicit with:"
  pushTac `(tactic|We reformulate $hypId:ident as $expandedHypTypeS)
  flush

implement_endpoint (lang := en) helpForAllRelExistsRelSuggestion (hyp var_name' n₀ hn₀ : Name)
    (headDescr hypDescr : String) (t : Format) (hn'S ineqIdent : Ident) (ineqS p'S : Term) :
    SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term applied to $n₀.ident using $hn₀.ident we get $var_name'.ident:ident such that ($ineqIdent : $ineqS) and ($hn'S : $p'S))
  pushCom "where {n₀} is {describe t} and {hn₀} is a proof of the fact that {hypDescr}."
  pushComment <| libres [var_name'.ident, ineqIdent, hn'S]

implement_endpoint (lang := en) helpSinceForAllRelExistsRelSuggestion (stmt :
    Term) (hyp var_name' n₀ : Name) (stmtn₀ : Term)
    (stmtn₀Str headDescr : String) (t : Format) (hn'S ineqIdent : Ident) (ineqS p'S : Term) :
    SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|Since $stmt:term and $stmtn₀ we get $var_name'.ident:ident such that $ineqS and $p'S)
  pushCom "where {n₀} is {describe t} and the relation {stmtn₀Str} must follow immediately from an assumption."
  pushComment <| libre var_name'.ident

implement_endpoint (lang := en) helpForAllRelExistsSimpleSuggestion (hyp n' hn' n₀ hn₀ : Name)
    (headDescr n₀rel : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term applied to $n₀.ident using $hn₀.ident we get $n'.ident:ident such that ($hn'.ident : $p'S))
  pushCom "where {n₀} is {describe t} and {hn₀} is a proof of the fact that {n₀rel}"
  pushComment <| libres [n'.ident, hn'.ident]

implement_endpoint (lang := en) helpSinceForAllRelExistsSimpleSuggestion (stmt : Term)
  (hyp n' hn' n₀ : Name)
  (stmtn₀ : Term) (stmtn₀Str headDescr : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|Since $stmt:term and $stmtn₀ we get $n'.ident:ident such that $p'S)
  pushCom "where {n₀} is {describe t} and the relation {stmtn₀Str} must follow immediately from an assumption."
  pushComment <| libre n'.ident

implement_endpoint (lang := en) helpForAllRelGenericSuggestion (hyp n₀ hn₀ : Name)
    (headDescr n₀rel : String) (t : Format) (newsI : Ident) (pS : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term applied to $n₀.ident using $hn₀.ident we get ($newsI : $pS))
  pushCom "where {n₀} is {describe t} and {hn₀} is a proof of the fact that {n₀rel}"
  pushComment <| libre newsI

implement_endpoint (lang := en) helpSinceForAllRelGenericSuggestion (stmt : Term) (hyp n₀ : Name)
  (stmtn₀ : Term)
  (stmtn₀Str headDescr : String) (t : Format) (newsI : Ident) (pS : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|Since $stmt:term and $stmtn₀ we get that $pS:term)
  pushCom "where {n₀} is {describe t} and {stmtn₀Str} follows immediately from an assumption."

implement_endpoint (lang := en) helpForAllSimpleExistsRelSuggestion (hyp var_name' nn₀ : Name)
    (headDescr : String) (t : Format) (hn'S ineqIdent : Ident) (ineqS p'S : Term) :
    SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term applied to $nn₀.ident we get $var_name'.ident:ident such that ($ineqIdent : $ineqS) and ($hn'S : $p'S))
  pushCom "where {nn₀} is {describe t}"
  pushComment <| libres [var_name'.ident, ineqIdent, hn'S]

implement_endpoint (lang := en) helpSinceForAllSimpleExistsRelSuggestion (stmt : Term) (hyp var_name' nn₀ : Name)
    (headDescr : String) (t : Format) (hn'S ineqIdent : Ident) (ineqS p'S : Term) :
    SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|Since $stmt:term we get $var_name'.ident:ident such that $ineqS and $p'S)
  pushCom "where {nn₀} is {describe t}"
  pushComment <| libre var_name'.ident

implement_endpoint (lang := en) helpForAllSimpleExistsSimpleSuggestion (hyp var_name' hn' nn₀  : Name)
    (headDescr : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term applied to $nn₀.ident we get $var_name'.ident:ident such that ($hn'.ident : $p'S))
  pushCom "where {nn₀} is {describe t}"
  pushComment <| libres [var_name'.ident, hn'.ident]

implement_endpoint (lang := en) helpSinceForAllSimpleExistsSimpleSuggestion (stmt : Term) (hyp var_name' hn' nn₀  : Name)
    (headDescr : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|Since $stmt:term we get $var_name'.ident:ident such that $p'S)
  pushCom "where {nn₀} is {describe t}"
  pushComment <| libre var_name'.ident

implement_endpoint (lang := en) helpForAllSimpleForAllRelSuggestion (hyp nn₀ var_name'₀ H h : Name)
    (headDescr rel₀ : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  pushCom "The assumption {hyp} starts with “{headDescr}"
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term applied to $nn₀.ident and $var_name'₀.ident using $H.ident we get ($h.ident : $p'S))
  pushCom "where {nn₀} and {var_name'₀} are {describe_pl t} and {H} is a proof of {rel₀}"
  pushComment <| libre h.ident

implement_endpoint (lang := en) helpSinceForAllSimpleForAllRelSuggestion (stmt rel₀S : Term) (hyp nn₀ var_name'₀ h : Name)
    (headDescr rel₀ : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|Since $stmt:term and $rel₀S:term we get that $p'S:term)
  pushCom "where {nn₀} and {var_name'₀} are {describe_pl t} and {rel₀} follows immediately from an assumption."

implement_endpoint (lang := en) helpForAllSimpleGenericSuggestion (hyp nn₀ hn₀ : Name) (headDescr : String)
    (t : Format) (pS : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term applied to $nn₀.ident we get ($hn₀.ident : $pS))
  pushCom "where {nn₀} is {describe t}"
  pushComment <| libre hn₀.ident
  flush
  pushCom "If this assumption won't be used again in its general shape, one can also specialize {hyp} with"
  pushTac `(tactic|We apply $hyp.ident:ident to $nn₀.ident)

implement_endpoint (lang := en) helpSinceForAllSimpleGenericSuggestion (stmt : Term) (hyp nn₀ hn₀ : Name) (headDescr : String)
    (t : Format) (pS : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|Since $stmt:term we get that $pS:term)
  pushCom "where {nn₀} is {describe t}"
  flush
  pushCom "If this assumption won't be used again in its general shape, one can also specialize {hyp} with"
  pushTac `(tactic|We apply $hyp.ident:ident to $nn₀.ident)

implement_endpoint (lang := en) helpForAllSimpleGenericApplySuggestion (prf : Expr) (but : Format) :
    SuggestionM Unit := do
  let prfS ← prf.toMaybeApplied
  pushCom "Since the goal is {but}, one can use:"
  pushTac `(tactic|We conclude by $prfS)

implement_endpoint (lang := en) helpExistsSimpleSuggestion (hyp n hn : Name) (headDescr : String)
    (pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term we get $n.ident:ident such that ($hn.ident : $pS))
  pushComment <| libres [n.ident, hn.ident]

implement_endpoint (lang := en) helpSinceExistsSimpleSuggestion (stmt : Term) (hyp n hn : Name) (headDescr : String)
    (pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic| Since $stmt:term we get $n.ident:ident such that $pS)
  pushComment <| libre n.ident

implement_endpoint (lang := en) helpDataSuggestion (hyp : Name) (t : Format) : SuggestionM Unit := do
  pushComment <| s!"The object {hyp}" ++ match t with
    | "ℝ" => " is a fixed real number."
    | "ℕ" => " is a fixed natural number."
    | "ℤ" => " is a fixed integer."
    | s => s!" : {s} is fixed."

implement_endpoint (lang := en) helpNothingSuggestion : SuggestionM Unit := do
  pushCom "I have nothing to say about this assumption."
  flush

implement_endpoint (lang := en) helpNothingGoalSuggestion : SuggestionM Unit := do
  pushCom "I have nothing to say about this goal."
  flush

def descrGoalHead (headDescr : String) : SuggestionM Unit :=
 pushCom "The goal starts with “{headDescr}”"

def descrGoalShape (headDescr : String) : SuggestionM Unit :=
 pushCom "The goal has shape “{headDescr}”"

def descrDirectProof : SuggestionM Unit :=
 pushCom "Hence a direct proof starts with:"

implement_endpoint (lang := en) helpUnfoldableGoalSuggestion (expandedGoalTypeS : Term) :
    SuggestionM Unit := do
  pushCom "The goal starts with the application of a definition."
  pushCom "One can make it explicit with:"
  pushTac `(tactic|Let's prove that $expandedGoalTypeS)
  flush

implement_endpoint (lang := en) helpAnnounceGoalSuggestion (actualGoalS : Term) : SuggestionM Unit := do
  pushCom "The next step is to announce:"
  pushTac `(tactic| Let's now prove that $actualGoalS)

implement_endpoint (lang := en) helpFixSuggestion (headDescr : String) (ineqS : TSyntax `fixDecl) :
    SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Fix $ineqS)

implement_endpoint (lang := en) helpExistsRelGoalSuggestion (headDescr : String) (n₀ : Name) (t : Format)
    (fullTgtS : Term) : SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Let's prove that $n₀.ident works : $fullTgtS)
  pushCom "replacing {n₀} by {describe t}"

implement_endpoint (lang := en) helpExistsGoalSuggestion (headDescr : String) (nn₀ : Name) (t : Format)
    (tgt : Term) : SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Let's prove that $nn₀.ident works : $tgt)
  pushCom "replacing {nn₀} by {describe t}"

implement_endpoint (lang := en) helpConjunctionGoalSuggestion (p p' : Term) : SuggestionM Unit := do
  descrGoalShape "... and ..."
  descrDirectProof
  pushTac `(tactic|Let's first prove that $p)
  pushCom "After finish this first proof, it will remain to prove that {← p'.fmt}"
  flush
  pushCom "One can also start with"
  pushTac `(tactic|Let's first prove that $p')
  pushCom "then, after finishing this first proof, il will remain to prove that {← p.fmt}"

implement_endpoint (lang := en) helpDisjunctionGoalSuggestion (p p' : Term) : SuggestionM Unit := do
  descrGoalShape "... or ..."
  pushCom "Hence a direct proof starts with announcing which alternative will be proven:"
  pushTac `(tactic|Let's prove that $p)
  flush
  pushCom "or:"
  pushTac `(tactic|Let's prove that $p')

implement_endpoint (lang := en) helpImplicationGoalSuggestion (headDescr : String) (Hyp : Name)
    (leStx : Term) : SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic| Assume $Hyp.ident:ident : $leStx)
  pushComment <| libre Hyp.ident

implement_endpoint (lang := en) helpEquivalenceGoalSuggestion (mpF mrF : Format) (mpS mrS : Term) :
    SuggestionM Unit := do
  pushCom "The goal is an equivalence. One can announce the proof of the left to right implication with:"
  pushTac `(tactic|Let's first prove that $mpS)
  pushCom "After proving this first statement, it will remain to prove that {mrF}"
  flush
  pushCom "One can also start with"
  pushTac `(tactic|Let's first prove that $mrS)
  pushCom "then, after finishing this first proof, il will remain to prove that {mpF}"

implement_endpoint (lang := en) helpSetEqSuggestion (lS rS : Term) : SuggestionM Unit := do
  pushCom "The goal is a set equality"
  pushCom "One can prove it by rewriting using:"
  pushTac `(tactic|We rewrite using ?_)
  flush
  pushCom "or start a computation using"
  pushTac `(tactic|Calc $lS:term = $rS since?)
  flush
  pushCom "One can also prove it by double inclusion."
  pushCom "In this case the proof starts with:"
  pushTac `(tactic|Let's first prove that $lS ⊆ $rS)

implement_endpoint (lang := en) helpSinceSetEqSuggestion (lS rS : Term) : SuggestionM Unit := do
  pushCom "The goal is a set equality"
  pushCom "One can prove it by rewriting using:"
  pushTac `(tactic|Since ?_ it suffices to prove that ?_)
  flush
  pushCom "or start a computation using"
  pushTac `(tactic|Calc $lS:term = $rS since?)
  flush
  pushCom "One can also prove it by double inclusion."
  pushCom "In this case the proof starts with:"
  pushTac `(tactic|Let's first prove that $lS ⊆ $rS)

implement_endpoint (lang := en) helpEqGoalSuggestion (lS rS : Term) : SuggestionM Unit := do
  pushCom "The goal is an equality"
  pushCom "One can prove it by rewriting using:"
  pushTac `(tactic|We rewrite using ?_)
  flush
  pushCom "or start a computation using"
  pushTac `(tactic|Calc $lS:term = $rS since?)
  flush
  pushCom "One can also make linear combination of assumptions with"
  pushTac `(tactic|We combine [?_, ?_])

implement_endpoint (lang := en) helpSinceEqGoalSuggestion (goal : Term) : SuggestionM Unit := do
  pushCom "The goal is an equality"
  pushCom "One can prove it by rewriting using:"
  pushTac `(tactic|Since ?_ we conclude that $goal)
  flush
  pushCom "or start a computation using"
  pushTac `(tactic|Calc $goal:term since?)

implement_endpoint (lang := en) helpIneqGoalSuggestion (goal : Term) (rel : String) : SuggestionM Unit := do
  pushCom "The goal is an inequality"
  pushCom "One can start a computation using"
  pushTac `(tactic|Calc $goal:term since?)
  pushCom "The last computation line is not necessarily an equality, it can be an inequality."
  pushCom "Similarly the first line could be an equality. In total, the relation symbols"
  pushCom "must chain to give {rel}"
  flush
  pushCom "One can also make linear combination of assumptions with"
  pushTac `(tactic| We combine [?_, ?_])

implement_endpoint (lang := en) helpSinceIneqGoalSuggestion (goal : Term) (rel : String) : SuggestionM Unit := do
  pushCom "The goal is an inequality"
  pushCom "One can start a computation using"
  pushTac `(tactic|Calc $goal:term since?)
  pushCom "The last computation line is not necessarily an equality, it can be an inequality."
  pushCom "Similarly the first line could be an equality. In total, the relation symbols"
  pushCom "must chain to give {rel}"
  flush
  pushCom "If this inequality follows immediately from an assumption, one can use:"
  pushTac `(tactic|Since ?_ we conclude that $goal)
  pushCom "replacing the question mark by the statement of the assumption."

implement_endpoint (lang := en) helpMemInterGoalSuggestion (elem le : Expr) : SuggestionM Unit := do
  pushCom "The goal is prove {← elem.fmt} belongs to the intersection of {← le.fmt} with another set."
  pushCom "Hance a direct proof starts with:"
  pushTac `(tactic|Let's first prove that $(← elem.stx) ∈ $(← le.stx))

implement_endpoint (lang := en) helpMemUnionGoalSuggestion (elem le re : Expr) : SuggestionM Unit := do
  pushCom "The goal is to prove {← elem.fmt} belongs to the union of {← le.fmt} and {← re.fmt}."
  descrDirectProof
  pushTac `(tactic|Let's prove that $(← elem.stx) ∈ $(← le.stx))
  flush
  pushCom "or by:"
  pushTac `(tactic|Let's prove that $(← elem.stx) ∈ $(← re.stx))

implement_endpoint (lang := en) helpNoIdeaGoalSuggestion : SuggestionM Unit := do
  pushCom "No idea."

implement_endpoint (lang := en) helpSubsetGoalSuggestion (l r : Format) (xN : Name) (lT : Term) :
    SuggestionM Unit := do
  pushCom "The goal is the inclusion {l} ⊆ {r}"
  descrDirectProof
  pushTac `(tactic| Fix $xN.ident:ident ∈ $lT)
  pushComment <| libre xN.ident

implement_endpoint (lang := en) helpFalseGoalSuggestion : SuggestionM Unit := do
  pushCom "The goal is to prove a contradiction."
  pushCom "One can apply an assumption which is a negation"
  pushCom "namely, by definition, with shape P → false."

implement_endpoint (lang := en) helpSinceFalseGoalSuggestion (goal : Term) : SuggestionM Unit := do
  pushCom "The goal is to prove a contradiction."
  pushCom "One can apply an assumption which is a negation"
  pushCom "namely, by definition, with shape P → false."
  pushCom "One can also combine two facts that clearly contradict each other using:"
  pushTac `(tactic|Since ?_ and ?_ we conclude that $goal)
  pushCom "replacing the question marks by those two facts that follow immediately from assumptions."
  flush
  pushCom "One can also invoke a clearly false fact (such as `0 = 1`) that follows directly from an assumption."
  pushTac `(tactic|Since ?_ we conclude that $goal)
  pushCom "replacing the question mark by this clearly false fact."

implement_endpoint (lang := en) helpContraposeGoalSuggestion : SuggestionM Unit := do
  pushCom "The goal is an implication."
  pushCom "One can start a proof by contraposition using"
  pushTac `(tactic| We contrapose)

implement_endpoint (lang := en) helpShowContrapositiveGoalSuggestion (stmt : Term) :
    SuggestionM Unit := do
  pushCom "The goal is an implication."
  pushCom "One can start a proof by contraposition using"
  pushTac `(tactic| Let's prove the contrapositive: $stmt)

implement_endpoint (lang := en) helpByContradictionSuggestion (hyp : Ident) (assum : Term) : SuggestionM Unit := do
  pushCom "One can start a proof by contradiction using"
  pushTac `(tactic| Assume for contradiction $hyp:ident : $assum)

implement_endpoint (lang := en) helpNegationGoalSuggestion (hyp : Ident) (p : Format) (assum : Term) :
    SuggestionM Unit := do
  pushCom "The goal is the negation of {p}, which means {p} implies a contradiction."
  pushCom "Hence a direct proof starts with:"
  pushTac `(tactic| Assume $hyp:ident : $assum)
  pushCom "And then it will remain to prove a contradiction."

implement_endpoint (lang := en) helpNeGoalSuggestion (l r : Format) (lS rS : Term) (Hyp : Ident):
    SuggestionM Unit := do
  pushCom "The goal is the negation of  {l} = {r}, which means {l} = {r} implies a contradiction."
  pushCom "Hence a direct proof starts with:"
  pushTac `(tactic| Assume $Hyp:ident : $lS = $rS)
  pushCom "And then it will remain to prove a contradiction."

set_option linter.unusedVariables false

configureAnonymousGoalSplittingLemmas Iff.intro Iff.intro' And.intro And.intro' abs_le_of_le_le abs_le_of_le_le'

configureHelpProviders DefaultHypHelp DefaultGoalHelp

set_option linter.unusedTactic false

/--
info: Help
  • The assumption h starts with “∀ n > 0, ...”
    One can use it with:
    By h applied to n₀ using hn₀ we get (hyp : P n₀)
    where n₀ is a natural number and hn₀ is a proof of the fact that n₀ > 0
    The name hyp can be chosen freely among available names.
-/
#guard_msgs in
example {P : ℕ → Prop} (h : ∀ n > 0, P n) : P 2 := by
  help h
  apply h
  norm_num

/--
info: Help
  • The assumption h has shape “∃ n > 0, ...”
    One can use it with:
    By h we get n such that (n_pos : n > 0) and (hn : P n)
    The names n, n_pos and hn can be chosen freely among available names.
-/
#guard_msgs in
example {P : ℕ → Prop} (h : ∃ n > 0, P n) : True := by
  help h
  trivial

/--
info: Help
  • The assumption h has shape “∃ ε > 0, ...”
    One can use it with:
    By h we get ε such that (ε_pos : ε > 0) and (hε : P ε)
    The names ε, ε_pos and hε can be chosen freely among available names.
-/
#guard_msgs in
example {P : ℝ → Prop} (h : ∃ ε > 0, P ε) : True := by
  help h
  trivial

/--
info: Help
  • The assumption h starts with “∀ n, ...”
    One can use it with:
    By h applied to n₀ we get (hn₀ : P n₀ → Q n₀)
    where n₀ is a natural number
    The name hn₀ can be chosen freely among available names.
  • If this assumption won't be used again in its general shape, one can also specialize h with
    We apply h to n₀
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : ∀ n, P n → Q n) (h' : P 2) : Q 2 := by
  help h
  exact h 2 h'

/--
info: Help
  • The assumption h starts with “∀ n, ...”
    One can use it with:
    By h applied to n₀ we get (hn₀ : P n₀)
    where n₀ is a natural number
    The name hn₀ can be chosen freely among available names.
  • If this assumption won't be used again in its general shape, one can also specialize h with
    We apply h to n₀
  • Since the goal is P 2, one can use:
    We conclude by h applied to 2
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∀ n, P n) : P 2 := by
  help h
  exact h 2

/--
info: Help
  • The assumption h is an implication
    The conclusion of this implication is the current goal
    Hence one can use this assumption with:
    By h it suffices to prove P 1
  • If one already has a proof H of P 1 then one can use:
    We conclude by h applied to H
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 → Q 2) (h' : P 1) : Q 2 := by
  help h
  exact h h'

/--
info: Help
  • The assumption h is an implication
    The premise of this implication is P 1
    If you have a proof H of P 1
    you can use this assumption with:
    By h applied to H we get H' : Q 2
    The name H' can be chosen freely among available names.
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 → Q 2) : True := by
  help h
  trivial

/--
info: Help
  • The assumption h has shape “... and ...”
    One can use it with:
    By h we get (h_1 : P 1) (h' : Q 2)
    The names h_1 and h' can be chosen freely among available names.
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 ∧ Q 2) : True := by
  help h
  trivial

/--
info: Help
  • The assumption h is an equivalence
    One can use it to replace the left-hand-side (namely ∀ n ≥ 2, P n) by the right-hand side (namely ∀ (l : ℕ), Q l) in the goal with:
    We rewrite using h
  • One can use it to replace the right-hand-side in the goal with:
    We rewrite using ← h
  • One can also perform such replacements in an assumption hyp with
    We rewrite using h at hyp
  • or
    We rewrite using ← h at hyp
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : (∀ n ≥ 2, P n) ↔  ∀ l, Q l) : True := by
  help h
  trivial

/--
info: Help
  • The goal has shape “... and ...”
    Hence a direct proof starts with:
    Let's first prove that True
    After finish this first proof, it will remain to prove that 1 = 1
  • One can also start with
    Let's first prove that 1 = 1
    then, after finishing this first proof, il will remain to prove that True
-/
#guard_msgs in
example : True ∧ 1 = 1 := by
  help
  exact ⟨trivial, rfl⟩

/--
info: Help
  • The assumption h has shape « ... or ... »
    One can use it with:
    We proceed using h
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 ∨ Q 2) : True := by
  help h
  trivial

/--
info: Help
  • The goal has shape “... or ...”
    Hence a direct proof starts with announcing which alternative will be proven:
    Let's prove that True
  • or:
    Let's prove that False
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

-- TODO: Improve this help message (low priority since it is very rare)
/--
info: Help
  • This assumption is a contradiction.
    One can deduce anything from it with:
    ( Let's prove it's contradictory
        We conclude by h)
-/
#guard_msgs in
example (h : False) : 0 = 1 := by
  help h
  trivial

/--
info: Help
  • The assumption h is an implication
    The premise of this implication is l - n = 0
    If you have a proof H of l - n = 0
    you can use this assumption with:
    By h applied to H we get H' : P l k
    The name H' can be chosen freely among available names.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (k l n : ℕ) (h : l - n = 0 → P l k) : True := by
  help h
  trivial

/--
info: Help
  • The assumption h starts with “∀ k ≥ 2, ∃ n ≥ 3, ...”
    One can use it with:
    By h applied to k₀ using hk₀ we get
        n such that (n_sup : n ≥ 3) and (hn : ∀ (l : ℕ), l - n = 0 → P l k₀)
    where k₀ is a natural number and hk₀ is a proof of the fact that k₀ ≥ 2.
    The names n, n_sup and hn can be chosen freely among available names.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  help h
  trivial

/--
info: Help
  • The assumption h starts with “∀ k n, k ≥ n ⇒ ...
    One can use it with:
    By h applied to k₀ and n₀ using H we get (h_1 : ∀ (l : ℕ), l - n₀ = 0 → P l k₀)
    where k₀ and n₀ are some natural numbers and H is a proof of k₀ ≥ n₀
    The name h_1 can be chosen freely among available names.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k, ∀ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  help h
  trivial

/--
info: Help
  • The assumption h starts with “∀ k ≥ 2, ∃ n_1 ≥ 3, ...”
    One can use it with:
    By h applied to k₀ using hk₀ we get
        n_1 such that (n_1_sup : n_1 ≥ 3) and (hn_1 : ∀ (l : ℕ), l - n = 0 → P l k₀)
    where k₀ is a natural number and hk₀ is a proof of the fact that k₀ ≥ 2.
    The names n_1, n_1_sup and hn_1 can be chosen freely among available names.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (n : ℕ) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  help h
  trivial

/--
info: Help
  • The assumption h has shape “∃ n ≥ 5, ...”
    One can use it with:
    By h we get n such that (n_sup : n ≥ 5) and (hn : P n)
    The names n, n_sup and hn can be chosen freely among available names.
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∃ n ≥ 5, P n) : True := by
  help h
  trivial

/--
info: Help
  • The assumption h starts with “∀ k ≥ 2, ∃ n ≥ 3, ...”
    One can use it with:
    By h applied to k₀ using hk₀ we get n such that (n_sup : n ≥ 3) and (hn : P n k₀)
    where k₀ is a natural number and hk₀ is a proof of the fact that k₀ ≥ 2.
    The names n, n_sup and hn can be chosen freely among available names.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, P n k) : True := by
  help h
  trivial

/--
info: Help
  • The assumption h has shape “∃ n, ...”
    One can use it with:
    By h we get n such that (hn : P n)
    The names n and hn can be chosen freely among available names.
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∃ n : ℕ, P n) : True := by
  help h
  trivial

/--
info: Help
  • The assumption h starts with “∀ k, ∃ n, ...”
    One can use it with:
    By h applied to k₀ we get n such that (hn : P n k₀)
    where k₀ is a natural number
    The names n and hn can be chosen freely among available names.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k, ∃ n : ℕ, P n k) : True := by
  help h
  trivial

/--
info: Help
  • The assumption h starts with “∀ k ≥ 2, ∃ n, ...”
    One can use it with:
    By h applied to k₀ using hk₀ we get n such that (hn : P n k₀)
    where k₀ is a natural number and hk₀ is a proof of the fact that k₀ ≥ 2
    The names n and hn can be chosen freely among available names.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n : ℕ, P n k) : True := by
  help h
  trivial

/--
info: Help
  • The goal starts with “∃ n, ...”
    Hence a direct proof starts with:
    Let's prove that n₀ works: P n₀ → True
    replacing n₀ by a natural number
-/
#guard_msgs in
example (P : ℕ → Prop): ∃ n : ℕ, P n → True := by
  help
  use 0
  tauto

/--
info: Help
  • The goal starts with “P ⇒ ...”
    Hence a direct proof starts with:
    Assume hyp : P
    The name hyp can be chosen freely among available names.
-/
#guard_msgs in
example (P Q : Prop) (h : Q) : P → Q := by
  help
  exact fun _ ↦ h

/--
info: Help
  • The goal starts with “∀ n ≥ 0”
    Hence a direct proof starts with:
    Fix n ≥ 0
-/
#guard_msgs in
example : ∀ n ≥ 0, True := by
  help
  intros
  trivial

/--
info: Help
  • The goal starts with “∀ n : ℕ,”
    Hence a direct proof starts with:
    Fix n : ℕ
-/
#guard_msgs in
example : ∀ n : ℕ, 0 ≤ n := by
  help
  exact Nat.zero_le

/--
info: Help
  • The goal starts with “∃ n, ...”
    Hence a direct proof starts with:
    Let's prove that n₀ works: 0 ≤ n₀
    replacing n₀ by a natural number
-/
#guard_msgs in
example : ∃ n : ℕ, 0 ≤ n := by
  help
  use 1
  exact Nat.zero_le 1

/--
info: Help
  • The goal starts with “∃ n ≥ 1, ...”
    Hence a direct proof starts with:
    Let's prove that n₀ works: n₀ ≥ 1 ∧ True
    replacing n₀ by a natural number
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
  • The goal is the inclusion s ⊆ t
    Hence a direct proof starts with:
    Fix x ∈ s
    The name x can be chosen freely among available names.
---
info: Help
  • The assumption h ensures the inclusion of s in t.
    One can use it with:
    By h applied to x_1 using hx we get hx' : x_1 ∈ t
    where x_1 is a natural number and hx proves that x_1 ∈ s
    The name hx' can be chosen freely among available names.
-/
#guard_msgs in
example (s t : Set ℕ) (h : s ⊆ t) : s ⊆ t := by
  help
  Fix x ∈ s
  help h
  exact h x_mem

/--
info: Help
  • The assumption h claims membership to an intersection
    One can use it with:
    By h we get (h_1 : x ∈ s) (h' : x ∈ t)
    The names h_1 and h' can be chosen freely among available names.
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∩ t) : x ∈ s := by
  help h
  By h we get (h_1 : x ∈ s) (h' : x ∈ t)
  exact h_1

/--
info: Help
  • The assumption h claims membership to an intersection
    One can use it with:
    By h we get (h_1 : x ∈ s) (h' : x ∈ t)
    The names h_1 and h' can be chosen freely among available names.
---
info: Help
  • The goal is prove x belongs to the intersection of t with another set.
    Hance a direct proof starts with:
    Let's first prove that x ∈ t
---
info: Help
  • The next step is to announce:
    Let's now prove that x ∈ s
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
  • The assumption h claims membership to a union
    One can use it with:
    We proceed using h
---
info: Help
  • The goal is to prove x belongs to the union of t and s.
    Hence a direct proof starts with:
    Let's prove that x ∈ t
  • or by:
    Let's prove that x ∈ s
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

/--
info: Help
  • The goal starts with “False ⇒ ...”
    Hence a direct proof starts with:
    Assume hyp : False
    The name hyp can be chosen freely among available names.
-/
#guard_msgs in
example : False → True := by
  help
  simp

/-- info: I have nothing to say about this goal. -/
#guard_msgs in
example : True := by
  help
  trivial

configureHelpProviders DefaultHypHelp DefaultGoalHelp helpContraposeGoal

/--
info: Help
  • The goal starts with “False ⇒ ...”
    Hence a direct proof starts with:
    Assume hyp : False
    The name hyp can be chosen freely among available names.
  • The goal is an implication.
    One can start a proof by contraposition using
    We contrapose
-/
#guard_msgs in
example : False → True := by
  help
  We contrapose
  simp

/-- info: I have nothing to say about this goal. -/
#guard_msgs in
example : True := by
  help
  trivial

configureHelpProviders DefaultHypHelp DefaultGoalHelp helpByContradictionGoal

/--
info: Help
  • One can start a proof by contradiction using
    Assume for contradiction hyp : False
-/
#guard_msgs in
example : True := by
  help
  trivial

/--
info: Help
  • The assumption h has shape “∃ x, ...”
    One can use it with:
    By h we get x_1 such that (hx_1 : f x_1 = y)
    The names x_1 and hx_1 can be chosen freely among available names.
-/
#guard_msgs in
example {X Y} (f : X → Y) (x : X) (y : Y) (h : ∃ x, f x = y) : True := by
  help h
  trivial

/--
info: Help
  • The assumption h has shape “∃ x ∈ s, ...”
    One can use it with:
    By h we get x_1 such that (x_1_dans : x_1 ∈ s) and (hx_1 : f x_1 = y)
    The names x_1, x_1_dans and hx_1 can be chosen freely among available names.
-/
#guard_msgs in
example {X Y} (f : X → Y) (s : Set X) (x : X) (y : Y) (h : ∃ x ∈ s, f x = y) : True := by
  help h
  trivial

/--
info: Help
  • The goal is the negation of P, which means P implies a contradiction.
    Hence a direct proof starts with:
    Assume hyp : P
    And then it will remain to prove a contradiction.
-/
#guard_msgs in
example (P : Prop) (h : ¬ P) : ¬ P := by
  help
  exact h

/--
info: Help
  • The goal is the negation of  x = y, which means x = y implies a contradiction.
    Hence a direct proof starts with:
    Assume hyp : x = y
    And then it will remain to prove a contradiction.
-/
#guard_msgs in
example (x y : ℕ) (h : x ≠ y) : x ≠ y := by
  help
  exact h

allowProvingNegationsByContradiction

/--
info: Help
  • One can start a proof by contradiction using
    Assume for contradiction hyp : P
  • The goal is the negation of P, which means P implies a contradiction.
    Hence a direct proof starts with:
    Assume hyp : P
    And then it will remain to prove a contradiction.
-/
#guard_msgs in
example (P : Prop) (h : ¬ P) : ¬ P := by
  help
  exact h

/--
info: Help
  • One can start a proof by contradiction using
    Assume for contradiction hyp : x = y
  • The goal is the negation of  x = y, which means x = y implies a contradiction.
    Hence a direct proof starts with:
    Assume hyp : x = y
    And then it will remain to prove a contradiction.
-/
#guard_msgs in
example (x y : ℕ) (h : x ≠ y) : x ≠ y := by
  help
  exact h

configureHelpProviders SinceHypHelp SinceGoalHelp helpShowContrapositiveGoal
/--
info: Help
  • The assumption h starts with “∀ n > 0, ...”
    One can use it with:
    Since ∀ n > 0, P n and n₀ > 0 we get that P n₀
    where n₀ is a natural number and n₀ > 0 follows immediately from an assumption.
-/
#guard_msgs in
example {P : ℕ → Prop} (h : ∀ n > 0, P n) : P 2 := by
  help h
  apply h
  norm_num

/--
info: Help
  • The assumption h has shape “∃ n > 0, ...”
    One can use it with:
    Since ∃ n > 0, P n we get n such that (n_pos : n > 0) and (hn : P n)
    The names n, n_pos and hn can be chosen freely among available names.
-/
#guard_msgs in
example {P : ℕ → Prop} (h : ∃ n > 0, P n) : True := by
  help h
  trivial

/--
info: Help
  • The assumption h has shape “∃ ε > 0, ...”
    One can use it with:
    Since ∃ ε > 0, P ε we get ε such that (ε_pos : ε > 0) and (hε : P ε)
    The names ε, ε_pos and hε can be chosen freely among available names.
-/
#guard_msgs in
example {P : ℝ → Prop} (h : ∃ ε > 0, P ε) : True := by
  help h
  trivial

/--
info: Help
  • The assumption h starts with “∀ n, ...”
    One can use it with:
    Since ∀ (n : ℕ), P n → Q n we get that P n₀ → Q n₀
    where n₀ is a natural number
  • If this assumption won't be used again in its general shape, one can also specialize h with
    We apply h to n₀
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : ∀ n, P n → Q n) (h' : P 2) : Q 2 := by
  help h
  exact h 2 h'

/--
info: Help
  • The assumption h starts with “∀ n, ...”
    One can use it with:
    Since ∀ (n : ℕ), P n we get that P n₀
    where n₀ is a natural number
  • If this assumption won't be used again in its general shape, one can also specialize h with
    We apply h to n₀
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∀ n, P n) : P 2 := by
  help h
  exact h 2

/--
info: Help
  • Assumption h is an implication
    The conclusion of this implication is the current goal
    Hence one can use this assumption with:
    Since P 1 → Q 2 it suffices to prove that P 1
  • If you already have a proof of P 1 then one can use:
    Since P 1 → Q 2 and P 1 we conclude that Q 2
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 → Q 2) (h' : P 1) : Q 2 := by
  help h
  exact h h'

/--
info: Help
  • Assumption h is an implication
    The premise of this implication is P 1
    If you have a proof of P 1
    you can use this assumption with:
    Since P 1 → Q 2 and P 1 we get that Q 2
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 → Q 2) : True := by
  help h
  trivial

/--
info: Help
  • The assumption h has shape “... and ...”
    One can use it with:
    Since P 1 ∧ Q 2 we get that P 1 and Q 2
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 ∧ Q 2) : True := by
  help h
  trivial

/--
info: Help
  • The assumption h is an equivalence
    One can use it to replace the left-hand-side (namely ∀ n ≥ 2, P n) by the right-hand side (namely ∀ (l : ℕ), Q l) or the other way around in the goal with:
    Since (∀ n ≥ 2, P n) ↔ ∀ (l : ℕ), Q l it suffices to prove that ?_
    replacing the question mark by the new goal.
  • One can also perform such replacements in a statement following from one of the current assumptions with
    Since (∀ n ≥ 2, P n) ↔ ∀ (l : ℕ), Q l and ?_ we get that ?_
    replacing the first question mark by the fact where you want to replace and the second one by the new obtained fact.
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : (∀ n ≥ 2, P n) ↔  ∀ l, Q l) : True := by
  help h
  trivial

/--
info: Help
  • The assumption h starts with “∀ x, ...”
    One can use it with:
    Since ∀ (x y : ℝ), x ≤ y → f x ≤ f y we get that ∀ (y : ℝ), x₀ ≤ y → f x₀ ≤ f y
    where x₀ is a real number
  • If this assumption won't be used again in its general shape, one can also specialize h with
    We apply h to x₀
-/
#guard_msgs in
example (f : ℝ → ℝ) (h : ∀ x y, x ≤ y → f x ≤ f y) (a b : ℝ) (h' : a ≤ b) : True := by
  help h
  trivial

/--
info: Help
  • The assumption h starts with “∀ x > 0, ...”
    One can use it with:
    Since ∀ x > 0, x = 1 → f x ≤ 0 and x₀ > 0 we get that x₀ = 1 → f x₀ ≤ 0
    where x₀ is a real number and x₀ > 0 follows immediately from an assumption.
-/
#guard_msgs in
example (f : ℝ → ℝ) (h : ∀ x > 0, x = 1 → f x ≤ 0) (a b : ℝ) (h' : a ≤ b) : True := by
  help h
  trivial

/--
info: Help
  • Assumption h is an implication
    The premise of this implication is l - n = 0
    If you have a proof of l - n = 0
    you can use this assumption with:
    Since l - n = 0 → P l k and l - n = 0 we get that P l k
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (k l n : ℕ) (h : l - n = 0 → P l k) : True := by
  help h
  trivial

/--
info: Help
  • The assumption h starts with “∀ k ≥ 2, ∃ n ≥ 3, ...”
    One can use it with:
    Since ∀ k ≥ 2, ∃ n ≥ 3, ∀ (l : ℕ), l - n = 0 → P l k and k₀ ≥ 2 we get
        n such that n ≥ 3 and ∀ (l : ℕ), l - n = 0 → P l k₀
    where k₀ is a natural number and the relation k₀ ≥ 2 must follow immediately from an assumption.
    The name n can be chosen freely among available names.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  help h
  trivial

-- FIXME: completely broken case
/--
info: Help
  • The assumption h starts with “∀ k n, k ≥ n ⇒ ...”
    One can use it with:
    Since ∀ (k n : ℕ), n ≥ 3 → ∀ (l : ℕ), l - n = 0 → P l k and n ≥ 3 we get that
        ∀ (l : ℕ), l - n₀ = 0 → P l k₀
    where k₀ and n₀ are some natural numbers and k₀ ≥ n₀ follows immediately from an assumption.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k, ∀ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  help h
  trivial

-- FIXME: completely broken case
/--
info: Help
  • The assumption h starts with “∀ k n, k ≤ n ⇒ ...”
    One can use it with:
    Since ∀ (k n : ℕ), n ≤ k → f n ≤ f k and n ≤ k we get that f n₀ ≤ f k₀
    where k₀ and n₀ are some natural numbers and k₀ ≤ n₀ follows immediately from an assumption.
-/
#guard_msgs in
example (f : ℕ → ℕ) (h : ∀ k n, n ≤ k → f n ≤ f k) : True := by
  help h
  trivial

-- FIXME: in hn_1, n is not replaced by n_1. This is an issue in
-- helpSinceForAllRelExistsRelSuggestion (or rather the function calling it)
/--
info: Help
  • The assumption h starts with “∀ k ≥ 2, ∃ n_1 ≥ 3, ...”
    One can use it with:
    Since ∀ k ≥ 2, ∃ n ≥ 3, ∀ (l : ℕ), l - n = 0 → P l k and k₀ ≥ 2 we get
        n_1 such that n_1 ≥ 3 and ∀ (l : ℕ), l - n = 0 → P l k₀
    where k₀ is a natural number and the relation k₀ ≥ 2 must follow immediately from an assumption.
    The name n_1 can be chosen freely among available names.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (n : ℕ) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  help h
  By h applied to 2 using le_rfl we get n' such that (n_sup : n' ≥ 3) and (hn : ∀ (l : ℕ), l - n' = 0 → P l 2)
  trivial

/--
info: Help
  • The assumption h has shape “∃ n ≥ 5, ...”
    One can use it with:
    Since ∃ n ≥ 5, P n we get n such that (n_sup : n ≥ 5) and (hn : P n)
    The names n, n_sup and hn can be chosen freely among available names.
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∃ n ≥ 5, P n) : True := by
  help h
  trivial

/--
info: Help
  • The assumption h starts with “∀ k ≥ 2, ∃ n ≥ 3, ...”
    One can use it with:
    Since ∀ k ≥ 2, ∃ n ≥ 3, P n k and k₀ ≥ 2 we get n such that n ≥ 3 and P n k₀
    where k₀ is a natural number and the relation k₀ ≥ 2 must follow immediately from an assumption.
    The name n can be chosen freely among available names.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, P n k) : True := by
  help h
  trivial

/--
info: Help
  • The assumption h has shape “∃ n, ...”
    One can use it with:
    Since ∃ n, P n we get n such that P n
    The name n can be chosen freely among available names.
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∃ n : ℕ, P n) : True := by
  help h
  trivial

/--
info: Help
  • The assumption h starts with “∀ k, ∃ n, ...”
    One can use it with:
    Since ∀ (k : ℕ), ∃ n, P n k we get n such that P n k₀
    where k₀ is a natural number
    The name n can be chosen freely among available names.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k, ∃ n : ℕ, P n k) : True := by
  help h
  trivial

/--
info: Help
  • The assumption h has shape “... or ...”
    One can use it with:
    We discuss depending on whether P 1 or Q 2
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 ∨ Q 2) : True := by
  help h
  trivial

/--
info: Help
  • The assumption h claims membership to an intersection
    One can use it with:
    Since x ∈ s ∩ t we get that x ∈ s and x ∈ t
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∩ t) : x ∈ s := by
  help h
  By h we get (h_1 : x ∈ s) (h' : x ∈ t)
  exact h_1

/--
info: Help
  • The assumption h claims membership to an intersection
    One can use it with:
    Since x ∈ s ∩ t we get that x ∈ s and x ∈ t
---
info: Help
  • The goal is prove x belongs to the intersection of t with another set.
    Hance a direct proof starts with:
    Let's first prove that x ∈ t
---
info: Help
  • The next step is to announce:
    Let's now prove that x ∈ s
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
  • The assumption h claims membership to a union
    One can use it with:
    We discuss depending on whether x ∈ s or x ∈ t
---
info: Help
  • The goal is to prove x belongs to the union of t and s.
    Hence a direct proof starts with:
    Let's prove that x ∈ t
  • or by:
    Let's prove that x ∈ s
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

/--
info: Help
  • The assumption h is an inequality
    It immediately implies the current goal.
    One can use it with:
    Since ε > 0 we conclude that ε / 2 > 0
-/
#guard_msgs in
example (ε : ℝ) (h : ε > 0) : ε/2 > 0 := by
  help h
  linarith

/--
info: Help
  • The goal is an inequality
    One can start a computation using
    Calc
        ε / 2 > 0 since?
    The last computation line is not necessarily an equality, it can be an inequality.
    Similarly the first line could be an equality. In total, the relation symbols
    must chain to give  > ⏎
  • If this inequality follows immediately from an assumption, one can use:
    Since ?_ we conclude that ε / 2 > 0
    replacing the question mark by the statement of the assumption.
-/
#guard_msgs in
example (ε : ℝ) (h : ε > 0) : ε/2 > 0 := by
  help
  Since ε > 0 we conclude that ε / 2 > 0

/--
info: Help
  • The assumption h is an equivalence
    One can use it to replace the left-hand-side (namely P) by the right-hand side (namely Q) or the other way around in the goal with:
    Since P ↔ Q it suffices to prove that ?_
    replacing the question mark by the new goal.
  • One can also perform such replacements in a statement following from one of the current assumptions with
    Since P ↔ Q and ?_ we get that ?_
    replacing the first question mark by the fact where you want to replace and the second one by the new obtained fact.
-/
#guard_msgs in
example (P Q : Prop) (h : P ↔ Q) (h' : P) : Q := by
  help h
  Since P ↔ Q it suffices to prove that P
  exact h'

/--
info: Help
  • The assumption h ensures the inclusion of A in B.
    One can use it with:
    Since A ⊆ B and x ∈ A we get that x ∈ B
    where x is a natural number
-/
#guard_msgs in
example (A B : Set ℕ) (h : A ⊆ B) : True := by
  help h
  trivial

/--
info: Help
  • This assumption is a contradiction.
    One can deduce the goal from it with:
    Since False we conclude that 0 = 1
-/
#guard_msgs in
example (h : False) : 0 = 1 := by
  help h
  Since False we conclude that 0 = 1

/--
info: Help
  • The goal is to prove a contradiction.
    One can apply an assumption which is a negation
    namely, by definition, with shape P → false.
    One can also combine two facts that clearly contradict each other using:
    Since ?_ and ?_ we conclude that False
    replacing the question marks by those two facts that follow immediately from assumptions.
  • One can also invoke a clearly false fact (such as `0 = 1`) that follows directly from an assumption.
    Since ?_ we conclude that False
    replacing the question mark by this clearly false fact.
-/
#guard_msgs in
example (h : 0 = 1) : False := by
  help
  Since 0 = 1 we conclude that False

/--
info: Help
  • The goal is an inequality
    One can start a computation using
    Calc
        a ≤ c since?
    The last computation line is not necessarily an equality, it can be an inequality.
    Similarly the first line could be an equality. In total, the relation symbols
    must chain to give  ≤ ⏎
  • If this inequality follows immediately from an assumption, one can use:
    Since ?_ we conclude that a ≤ c
    replacing the question mark by the statement of the assumption.
-/
#guard_msgs in
example (a b c : ℤ) (h : a ≤ b) (h' : b ≤ c) : a ≤ c := by
  help
  exact le_trans h h'

/--
info: Help
  • The goal starts with “False ⇒ ...”
    Hence a direct proof starts with:
    Assume hyp : False
    The name hyp can be chosen freely among available names.
  • The goal is an implication.
    One can start a proof by contraposition using
    Let's prove the contrapositive: ¬True → ¬False
-/
#guard_msgs in
example : False → True := by
  help
  Let's prove the contrapositive: ¬True → ¬False
  simp
