import Verbose.Tactics.Help
import Verbose.French.Tactics

open Lean Meta Elab Tactic Term Verbose

namespace Verbose.French

implement_endpoint (lang := fr) try_this : CoreM String := pure "Essayer : "

implement_endpoint (lang := fr) apply_suggestion : CoreM String := pure "Appliquer la suggestion"

open Lean.Parser.Tactic in
elab "aide" h:(colGt ident)? : tactic => do
unless (← verboseConfigurationExt.get).useHelpTactic do
  throwError "La tactique d’aide n’est pas activée."
match h with
| some h => do
    let (s, msg) ← gatherSuggestions (helpAtHyp (← getMainGoal) h.getId)
    if s.isEmpty then
      logInfo (msg.getD "Pas de suggestion")
    else
      addSuggestions (← getRef) s (header := "Aide")
| none => do
    let (s, msg) ← gatherSuggestions (helpAtGoal (← getMainGoal))
    if s.isEmpty then
      logInfo (msg.getD "Pas de suggestion")
    else
      addSuggestions (← getRef) s (header := "Aide")

def describe (t : Format) : String :=
match toString t with
| "ℝ" => "un nombre réel"
| "ℕ" => "un nombre entier naturel"
| "ℤ" => "un nombre entier relatif"
| t => "une expression de type " ++ t

def describe_pl (t : Format) : String :=
match toString t with
| "ℝ" => "des nombres réels"
| "ℕ" => "des nombres entiers naturels"
| "ℤ" => "des nombres entiers relatifs"
| t => "des expressions de type " ++ t

def libre (s : Ident) : String := s!"Le nom {s.getId} peut être choisi librement parmi les noms disponibles."

def printIdentList (l : List Ident) : String := commaSep (l.toArray.map (toString ·.getId)) "et"

def libres (ls : List Ident) : String :=
s!"Les noms {printIdentList ls} peuvent être choisis librement parmi les noms disponibles."

def describeHypShape (hyp : Name) (headDescr : String) : SuggestionM Unit :=
  pushCom "L'hypothèse {hyp} est de la forme « {headDescr} »"

def describeHypStart (hyp : Name) (headDescr : String) : SuggestionM Unit :=
  pushCom "L'hypothèse {hyp} commence par « {headDescr} »"

implement_endpoint (lang := fr) helpExistRelSuggestion (hyp : Name) (headDescr : String)
    (nameS ineqIdent hS : Ident) (ineqS pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Par $hyp.ident:term on obtient $nameS:ident tel que ($ineqIdent : $ineqS) et ($hS : $pS))
  pushComment <| libres [nameS, ineqIdent, hS]

implement_endpoint (lang := fr) helpSinceExistRelSuggestion (hyp : Name) (headDescr : String)
    (nameS ineqIdent hS : Ident) (hypS ineqS pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Comme $hypS:term on obtient $nameS:ident tel que ($ineqIdent : $ineqS) et ($hS : $pS))
  pushComment <| libres [nameS, ineqIdent, hS]

implement_endpoint (lang := fr) helpConjunctionSuggestion (hyp : Name) (h₁I h₂I : Ident) (p₁S p₂S : Term) :
    SuggestionM Unit := do
  let headDescr := "... et ..."
  describeHypShape hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Par $hyp.ident:term on obtient ($h₁I : $p₁S) ($h₂I : $p₂S))
  pushComment <| libres [h₁I, h₂I]

implement_endpoint (lang := fr) helpSinceConjunctionSuggestion (hyp : Name) (p₁S p₂S : Term) :
    SuggestionM Unit := do
  let headDescr := "... et ..."
  describeHypShape hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Comme $p₁S:term ∧ $p₂S on obtient que $p₁S:term et $p₂S)

implement_endpoint (lang := fr) helpDisjunctionSuggestion (hyp : Name) : SuggestionM Unit := do
  describeHypShape hyp "... ou ..."
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|On discute en utilisant $hyp.ident:term)

implement_endpoint (lang := fr) helpSinceDisjunctionSuggestion (hyp : Name) (p₁S p₂S : Term) : SuggestionM Unit := do
  describeHypShape hyp "... ou ..."
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|On discute selon que $p₁S:term ou $p₂S)

implement_endpoint (lang := fr) helpImplicationSuggestion (hyp HN H'N : Name) (closes : Bool)
    (le re : Expr) : SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une implication"
  if closes then do
    pushCom "La conclusion de cette implication est le but courant"
    pushCom "On peut donc utiliser cette hypothèse avec :"
    pushTac `(tactic| Par $hyp.ident:term il suffit de montrer $(← le.stx))
    flush
    pushCom "Si vous disposez déjà d'une preuve {HN} de {← le.fmt} alors on peut utiliser :"
    pushTac `(tactic|On conclut par $hyp.ident:term appliqué à $HN.ident)
  else do
    pushCom "La prémisse de cette implication est {← le.fmt}"
    pushCom "Si vous avez une démonstration {HN} de {← le.fmt}"
    pushCom "vous pouvez donc utiliser cette hypothèse avec :"
    pushTac `(tactic|Par $hyp.ident:term appliqué à $HN.ident:term on obtient $H'N.ident:ident : $(← re.stx):term)
    pushComment <| libre H'N.ident

implement_endpoint (lang := fr) helpSinceImplicationSuggestion (stmt goalS leS : Term) (hyp : Name) (closes : Bool)
    (le re : Expr) : SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une implication"
  if closes then do
    pushCom "La conclusion de cette implication est le but courant"
    pushCom "On peut donc utiliser cette hypothèse avec :"
    pushTac `(tactic| Comme $stmt:term il suffit de montrer que $(← le.stx):term)
    flush
    pushCom "Si vous disposez déjà d'une preuve de {← le.fmt} alors on peut utiliser :"
    pushTac `(tactic|Comme $stmt:term et $(← le.stx):term on conclut que $goalS)
  else do
    pushCom "La prémisse de cette implication est {← le.fmt}"
    pushCom "Si vous avez une démonstration de {← le.fmt}"
    pushCom "vous pouvez donc utiliser cette hypothèse avec :"
    pushTac `(tactic|Comme $stmt:term et $leS:term on obtient que $(← re.stx):term)

implement_endpoint (lang := fr) helpEquivalenceSuggestion (hyp hyp'N : Name) (l r : Expr) : SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une équivalence"
  pushCom "On peut s'en servir pour remplacer le membre de gauche (c'est à dire {← l.fmt}) par le membre de droite  (c'est à dire {← r.fmt}) dans le but par :"
  pushTac `(tactic|On réécrit via $hyp.ident:term)
  flush
  pushCom "On peut s'en servir pour remplacer le membre de droite dans par le membre de gauche dans le but par :"
  pushTac `(tactic|On réécrit via ← $hyp.ident)
  flush
  pushCom "On peut aussi effectuer de tels remplacements dans une hypothèse {hyp'N} par"
  pushTac `(tactic|On réécrit via $hyp.ident:term dans l'hypothèse $hyp'N.ident:ident)
  flush
  pushCom " ou "
  pushTac `(tactic|On réécrit via ← $hyp.ident:term dans l'hypothèse $hyp'N.ident:ident)

implement_endpoint (lang := fr) helpSinceEquivalenceSuggestion
    (hyp : Name) (stmt : Term) (l r : Expr) : SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une équivalence"
  pushCom "On peut s'en servir pour remplacer le membre de gauche (c'est à dire {← l.fmt}) par le membre de droite  (c'est à dire {← r.fmt}) dans le but (ou vice-versa) par :"
  pushTac `(tactic|Comme $stmt:term il suffit de montrer que ?_)
  pushCom "en remplaçant le point d'interrogation par le nouveau but."
  flush
  pushCom "On peut aussi effectuer de tels remplacements dans un fait qui découle directement des hypothèses courantes par"
  pushTac `(tactic|Comme $stmt:term et ?_ on obtient que ?_)
  pushCom "en remplaçant le premier point d'interrogation par le fait dans lequel on veut effectuer le remplacement et le second par le nouveau fait obtenu."

implement_endpoint (lang := fr) helpEqualSuggestion (hyp hyp' : Name) (closes : Bool) (l r : String) :
    SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une égalité"
  if closes then
    pushComment <| s!"Le but courant en découle immédiatement"
    pushComment   "On peut l'utiliser avec :"
    pushTac `(tactic|On conclut par $hyp.ident:ident)
  else do
    pushCom "On peut s'en servir pour remplacer le membre de gauche (c'est à dire {l}) par le membre de droite  (c'est à dire {r}) dans le but par :"
    pushTac `(tactic|On réécrit via $hyp.ident:ident)
    flush
    pushCom "On peut s'en servir pour remplacer le membre de droite dans par le membre de gauche dans le but par :"
    pushTac `(tactic|On réécrit via ← $hyp.ident:ident)
    flush
    pushCom "On peut aussi effectuer de tels remplacements dans une hypothèse {hyp'} par"
    pushTac `(tactic|On réécrit via $hyp.ident:ident dans l'hypothèse $hyp'.ident:ident)
    flush
    pushCom " ou "
    pushTac `(tactic|On réécrit via ← $hyp.ident:ident dans l'hypothèse $hyp'.ident:ident)
    flush
    pushCom "On peut aussi s'en servir comme étape dans un calcul, ou bien combinée linéairement à d'autres par :"
    pushTac `(tactic| On combine [$hyp.ident:term, ?_])
    pushCom "en remplaçant le point d'interrogation par un ou plusieurs termes prouvant des égalités."

implement_endpoint (lang := fr) helpSinceEqualSuggestion (hyp : Name)
    (closes : Bool) (l r : String) (leS reS goalS : Term) : SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une égalité"
  let eq ← `($leS = $reS)
  if closes then
    pushComment <| s!"Le but courant en découle immédiatement"
    pushComment   "On peut l'utiliser avec :"
    pushTac `(tactic|Comme $eq:term on conclut que $goalS)
  else do
    pushCom "On peut s'en servir pour remplacer le membre de gauche (c'est à dire {l}) par le membre de droite  (c'est à dire {r}) (ou dans l’autre sens) dans le but par :"
    pushTac `(tactic|Comme $eq:term il suffit de montrer que ?_)
    pushCom "en écrivant bien sûr le nouveau but à la place du ?_"
    flush
    pushCom "On peut aussi effectuer de tels remplacements dans dans un fait qui découle directement des hypothèses courantes  par"
    pushTac `(tactic|Comme $eq:term et ?_ on obtient que ?_)
    pushCom "où le premier ?_ est à remplacer par l’affirmation de ce fait et le second par la nouvelle information obtenue."

implement_endpoint (lang := fr) helpIneqSuggestion (hyp : Name) (closes : Bool) : SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une inégalité"
  if closes then
    pushCom "Le but courant en découle immédiatement"
    pushCom "On peut l'utiliser avec :"
    pushTac `(tactic|On conclut par $hyp.ident:ident)
  else do
    pushCom "On peut s'en servir comme étape dans un calcul, ou bien combinée linéairement à d'autres par :"
    pushTac `(tactic| On combine [$hyp.ident:term, ?_])
    pushCom "en remplaçant le point d'interrogation par un ou plusieurs termes prouvant des égalités ou inégalités."

implement_endpoint (lang := fr) helpSinceIneqSuggestion (hyp : Name) (stmt goal : Term) (closes : Bool) : SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une inégalité"
  if closes then
    pushCom "Le but courant en découle immédiatement"
    pushCom "On peut l'utiliser avec :"
    pushTac `(tactic|Comme $stmt:term on conclut que $goal)
  else do
    flush
    pushCom "On peut s'en servir comme étape dans un calcul, ou bien combinée linéairement à d'autres par :"
    pushTac `(tactic| Comme $stmt:term et ?_ on conclut que $goal)
    pushCom "en remplaçant le point d'interrogation par un ou plusieurs termes prouvant des égalités ou inégalités."

implement_endpoint (lang := fr) helpMemInterSuggestion (hyp h₁ h₂ : Name) (elemS p₁S p₂S : Term) :
    SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une appartenance à une intersection"
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Par $hyp.ident:term on obtient ($h₁.ident : $elemS ∈ $p₁S) ($h₂.ident : $elemS ∈ $p₂S))
  pushComment <| libres [h₁.ident, h₂.ident]

implement_endpoint (lang := fr) helpSinceMemInterSuggestion (stmt : Term) (hyp : Name) (mem₁ mem₂ : Term) :
    SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une appartenance à une intersection"
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Comme $stmt:term on obtient que $mem₁:term et $mem₂)

implement_endpoint (lang := fr) helpMemUnionSuggestion (hyp : Name) :
    SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une appartenance à une réunion"
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|On discute en utilisant $hyp.ident)

implement_endpoint (lang := fr) helpSinceMemUnionSuggestion (elemS leS reS : Term) (hyp : Name) :
    SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une appartenance à une réunion"
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|On discute selon que $elemS ∈ $leS ou $elemS ∈ $reS)

implement_endpoint (lang := fr) helpGenericMemSuggestion (hyp : Name) : SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} est une appartenance"

implement_endpoint (lang := fr) helpContradictionSuggestion (hypId : Ident) : SuggestionM Unit := do
  pushComment <| "Cette hypothèse est une contradiction."
  pushCom "On peut en déduire tout ce qu'on veut par :"
  pushTac `(tactic|(Montrons une contradiction
                    On conclut par $hypId:ident))

implement_endpoint (lang := fr) helpSinceContradictionSuggestion
     (stmt goal : Term) : SuggestionM Unit := do
  pushComment <| "Cette hypothèse est une contradiction."
  pushCom "On peut en déduire le but par :"
  pushTac `(tactic|Comme $stmt:term on conclut que $goal)

implement_endpoint (lang := fr) helpSubsetSuggestion (hyp x hx hx' : Name)
    (r : Expr) (l ambientTypePP : Format) : SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} affirme l'inclusion de {l} dans {← r.fmt}."
  pushCom "On peut s'en servir avec :"
  pushTac `(tactic| Par $hyp.ident:ident appliqué à $x.ident en utilisant $hx.ident on obtient $hx'.ident:ident : $x.ident ∈ $(← r.stx))
  pushCom "où {x} est {describe ambientTypePP} et {hx} est une démonstration du fait que {x} ∈ {l}"
  pushComment <| libre hx'.ident

implement_endpoint (lang := fr) helpSinceSubsetSuggestion (hyp x : Name) (stmt new : Term)
    (l r : Expr) (ambientTypePP : Format) : SuggestionM Unit := do
  pushCom "L'hypothèse {hyp} affirme l'inclusion de {← l.fmt} dans {← r.fmt}."
  pushCom "On peut s'en servir avec :"
  pushTac `(tactic| Comme $stmt:term et $x.ident ∈ $(← l.stx) on obtient que $new:term)
  pushCom "où {x} est {describe ambientTypePP}"

implement_endpoint (lang := fr) assumptionClosesSuggestion (hypId : Ident) : SuggestionM Unit := do
  pushCom "Cette hypothèse est exactement ce qu'il faut démontrer"
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|On conclut par $hypId:ident)

implement_endpoint (lang := fr) assumptionUnfoldingSuggestion (hypId : Ident) (expandedHypTypeS : Term) :
    SuggestionM Unit := do
  pushCom "Cette hypothèse commence par l'application d'une définition."
  pushCom "On peut l'expliciter avec :"
  pushTac `(tactic|On reformule l'hypothèse $hypId:ident en $expandedHypTypeS)
  flush

implement_endpoint (lang := fr) helpForAllRelExistsRelSuggestion (hyp var_name' n₀ hn₀ : Name)
    (headDescr hypDescr : String) (t : Format) (hn'S ineqIdent : Ident) (ineqS p'S : Term) :
    SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Par $hyp.ident:term appliqué à $n₀.ident en utilisant $hn₀.ident on obtient $var_name'.ident:ident tel que ($ineqIdent : $ineqS) et ($hn'S : $p'S))
  pushCom "où {n₀} est {describe t} et {hn₀} est une démonstration du fait que {hypDescr}."
  pushComment <| libres [var_name'.ident, ineqIdent, hn'S]

implement_endpoint (lang := fr) helpSinceForAllRelExistsRelSuggestion (stmt :
    Term) (hyp var_name' n₀ : Name) (stmtn₀ : Term)
    (stmtn₀Str headDescr : String) (t : Format) (ineqS p'S : Term) :
    SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Comme $stmt:term et $stmtn₀ on obtient $var_name'.ident:ident tel que $ineqS et $p'S)
  pushCom "où {n₀} est {describe t} et la relation {stmtn₀Str} doit découler directement d’une hypothèse."
  pushComment <| libre var_name'.ident

implement_endpoint (lang := fr) helpForAllRelExistsSimpleSuggestion (hyp n' hn' n₀ hn₀ : Name)
    (headDescr n₀rel : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Par $hyp.ident:term appliqué à $n₀.ident en utilisant $hn₀.ident on obtient $n'.ident:ident tel que ($hn'.ident : $p'S))
  pushCom "où {n₀} est {describe t} et h{n₀} est une démonstration du fait que {n₀rel}"
  pushComment <| libres [n'.ident, hn'.ident]

implement_endpoint (lang := fr) helpSinceForAllRelExistsSimpleSuggestion (stmt : Term)
  (hyp n' n₀ : Name)
  (stmtn₀ : Term) (stmtn₀Str headDescr : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Comme $stmt:term et $stmtn₀ on obtient $n'.ident:ident tel que $p'S)
  pushCom "où {n₀} est {describe t} et la relation {stmtn₀Str} doit découler directement d’une hypothèse."
  pushComment <| libre n'.ident

implement_endpoint (lang := fr) helpForAllRelGenericSuggestion (hyp n₀ hn₀ : Name)
    (headDescr n₀rel : String) (t : Format) (newsI : Ident) (pS : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Par $hyp.ident:term appliqué à $n₀.ident en utilisant $hn₀.ident on obtient ($newsI : $pS))
  pushCom "où {n₀} est {describe t} et {hn₀} est une démonstration du fait que {n₀rel}"
  pushComment <| libre newsI

implement_endpoint (lang := fr) helpSinceForAllRelGenericSuggestion (stmt : Term) (hyp n₀ : Name)
  (stmtn₀ : Term)
  (stmtn₀Str headDescr : String) (t : Format) (pS : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Comme $stmt:term et $stmtn₀ on obtient que $pS:term)
  pushCom "où {n₀} est {describe t} et {stmtn₀Str} découle directement d’une hypothèse."

implement_endpoint (lang := fr) helpForAllSimpleExistsRelSuggestion (hyp var_name' nn₀ : Name)
    (headDescr : String) (t : Format) (hn'S ineqIdent : Ident) (ineqS p'S : Term) :
    SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Par $hyp.ident:term appliqué à $nn₀.ident on obtient $var_name'.ident:ident tel que (ineqIdent : $ineqS) et ($hn'S : $p'S))
  pushCom "où {nn₀} est {describe t}"
  pushComment <| libres [var_name'.ident, ineqIdent, hn'S]

implement_endpoint (lang := fr) helpSinceForAllSimpleExistsRelSuggestion (stmt : Term) (hyp var_name' nn₀ : Name)
    (headDescr : String) (t : Format) (ineqS p'S : Term) :
    SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Comme $stmt:term on obtient $var_name'.ident:ident tel que $ineqS et $p'S)
  pushCom "où {nn₀} est {describe t}"
  pushComment <| libre var_name'.ident

implement_endpoint (lang := fr) helpForAllSimpleExistsSimpleSuggestion (hyp var_name' hn' nn₀  : Name)
    (headDescr : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Par $hyp.ident:term appliqué à $nn₀.ident on obtient $var_name'.ident:ident tel que ($hn'.ident : $p'S))
  pushCom "où {nn₀} est {describe t}"
  pushComment <| libres [var_name'.ident, hn'.ident]

implement_endpoint (lang := fr) helpSinceForAllSimpleExistsSimpleSuggestion (stmt : Term) (hyp var_name' nn₀  : Name)
    (headDescr : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Comme $stmt:term on obtient $var_name'.ident:ident tel que $p'S)
  pushCom "où {nn₀} est {describe t}"
  pushComment <| libre var_name'.ident

implement_endpoint (lang := fr) helpForAllSimpleForAllRelSuggestion (hyp nn₀ var_name'₀ H h : Name)
    (headDescr rel₀ : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Par $hyp.ident:term appliqué à $nn₀.ident et $var_name'₀.ident en utilisant $H.ident on obtient ($h.ident : $p'S))
  pushCom "où {nn₀} et {var_name'₀} sont {describe_pl t} et {H} est une démonstration de {rel₀}"
  pushComment <| libre h.ident

implement_endpoint (lang := fr) helpSinceForAllSimpleForAllRelSuggestion (stmt rel₀S : Term) (hyp nn₀ var_name'₀ : Name)
    (headDescr rel₀ : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Comme $stmt:term et $rel₀S on obtient que $p'S:term)
  pushCom "où {nn₀} et {var_name'₀} sont {describe_pl t} et {rel₀} découle immédiatement d’une hypothèse."

implement_endpoint (lang := fr) helpForAllSimpleGenericSuggestion (hyp nn₀ hn₀ : Name) (headDescr : String)
    (t : Format) (pS : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Par $hyp.ident:term appliqué à $nn₀.ident on obtient ($hn₀.ident : $pS))
  pushCom "où {nn₀} est {describe t}"
  pushComment <| libre hn₀.ident
  flush
  pushCom "Si cette hypothèse ne servira plus dans sa forme générale, on peut aussi spécialiser {hyp} par"
  pushTac `(tactic|On applique $hyp.ident:ident à $nn₀.ident)

implement_endpoint (lang := fr) helpSinceForAllSimpleGenericSuggestion (stmt : Term) (hyp nn₀ : Name) (headDescr : String)
    (t : Format) (pS : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Comme $stmt:term on obtient que $pS:term)
  pushCom "où {nn₀} est {describe t}"
  flush
  pushCom "Si cette hypothèse ne servira plus dans sa forme générale, on peut aussi spécialiser {hyp} par"
  pushTac `(tactic|On applique $hyp.ident:ident à $nn₀.ident)

implement_endpoint (lang := fr) helpForAllSimpleGenericApplySuggestion (prf : Expr) (but : Format) :
    SuggestionM Unit := do
  let prfS ← prf.toMaybeAppliedFR
  pushCom "Comme le but est {but}, on peut utiliser :"
  pushTac `(tactic|On conclut par $prfS)

implement_endpoint (lang := fr) helpExistsSimpleSuggestion (hyp n hn : Name) (headDescr : String)
    (pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic| Par $hyp.ident:term on obtient $n.ident:ident tel que ($hn.ident : $pS))
  pushComment <| libres [n.ident, hn.ident]

implement_endpoint (lang := fr) helpSinceExistsSimpleSuggestion (stmt : Term) (hyp n : Name) (headDescr : String)
    (pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic| Comme $stmt:term on obtient $n.ident:ident tel que $pS)
  pushComment <| libre n.ident

implement_endpoint (lang := fr) helpDataSuggestion (hyp : Name) (t : Format) : SuggestionM Unit := do
  pushComment <| s!"L'objet {hyp}" ++ match t with
          | "ℝ" => " est un nombre réel fixé."
          | "ℕ" => " est un nombre entier naturel fixé."
          | "ℤ" => " est un nombre entier relatif fixé."
          | s => s!" : {s} est fixé."

implement_endpoint (lang := fr) helpNothingSuggestion : SuggestionM Unit := do
  pushCom "Je n'ai rien à déclarer à propos de cette hypothèse."
  flush

implement_endpoint (lang := fr) helpNothingGoalSuggestion : SuggestionM Unit := do
  pushCom "Je n'ai rien à déclarer à propos de ce but."
  flush

def descrGoalHead (headDescr : String) : SuggestionM Unit :=
 pushCom "Le but commence par « {headDescr} »"

def descrGoalShape (headDescr : String) : SuggestionM Unit :=
 pushCom "Le but est de la forme « {headDescr} »"

def descrDirectProof : SuggestionM Unit :=
 pushCom "Une démonstration directe commence donc par :"

implement_endpoint (lang := fr) helpUnfoldableGoalSuggestion (expandedGoalTypeS : Term) :
    SuggestionM Unit := do
  pushCom "Le but commence par l’application d’une définition."
  pushCom "On peut l’expliciter par :"
  pushTac `(tactic|Montrons que $expandedGoalTypeS)
  flush

implement_endpoint (lang := fr) helpAnnounceGoalSuggestion (actualGoalS : Term) : SuggestionM Unit := do
  pushCom "L’étape suivante est d'annoncer :"
  pushTac `(tactic| Montrons maintenant que $actualGoalS)

implement_endpoint (lang := fr) helpFixSuggestion (headDescr : String) (ineqS : TSyntax `fixDecl) :
    SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Soit $ineqS)

implement_endpoint (lang := fr) helpExistsRelGoalSuggestion (headDescr : String) (n₀ : Name) (t : Format)
    (fullTgtS : Term) : SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Montrons que $n₀.ident convient : $fullTgtS)
  pushCom "où {n₀} est {describe t}"

implement_endpoint (lang := fr) helpExistsGoalSuggestion (headDescr : String) (nn₀ : Name) (t : Format)
    (tgt : Term) : SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Montrons que $nn₀.ident convient : $tgt)
  pushCom "où {nn₀} est {describe t}"

implement_endpoint (lang := fr) helpConjunctionGoalSuggestion (p p' : Term) : SuggestionM Unit := do
  descrGoalShape "... et ..."
  descrDirectProof
  pushTac `(tactic|Montrons d'abord que $p)
  pushCom "Une fois cette première démonstration achevée, il restera à montrer que {← p'.fmt}"
  flush
  pushCom "On peut aussi commencer par"
  pushTac `(tactic|Montrons d'abord que $p')
  pushCom "puis, une fois cette première démonstration achevée, il restera à montrer que {← p.fmt}"

implement_endpoint (lang := fr) helpDisjunctionGoalSuggestion (p p' : Term) : SuggestionM Unit := do
  descrGoalShape "... ou ..."
  pushCom "Une démonstration directe commence donc par annoncer quelle alternative va être démontrée :"
  pushTac `(tactic|Montrons que $p)
  flush
  pushCom "ou bien :"
  pushTac `(tactic|Montrons que $p')

open Verbose.Named in
implement_endpoint (lang := fr) helpImplicationGoalSuggestion (headDescr : String) (Hyp : Name)
    (leStx : Term) : SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Supposons $Hyp.ident:ident : $leStx)
  pushComment <| libre Hyp.ident

open Verbose.NameLess in
implement_endpoint (lang := fr) helpImplicationGoalNLSuggestion (headDescr : String) (leStx : Term) : SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Supposons que $leStx)

implement_endpoint (lang := fr) helpEquivalenceGoalSuggestion (mpF mrF : Format) (mpS mrS : Term) :
    SuggestionM Unit := do
  pushCom "Le but est une équivalence. On peut annoncer la démonstration de l'implication de la gauche vers la droite par :"
  pushTac `(tactic|Montrons d'abord que $mpS)
  pushCom "Une fois cette première démonstration achevée, il restera à montrer que {mrF}"
  flush
  pushCom "On peut aussi commencer par"
  pushTac `(tactic|Montrons d'abord que $mrS)
  pushCom "puis, une fois cette première démonstration achevée, il restera à montrer que {mpF}"

implement_endpoint (lang := fr) helpSetEqSuggestion (lS rS : Term) : SuggestionM Unit := do
  pushCom "Le but est une égalité entre ensembles"
  pushCom "On peut la démontrer par réécriture avec la commande"
  pushTac `(tactic|On réécrit via ?_)
  flush
  pushCom "On peut commencer un calcul par"
  pushTac `(tactic|Calc $lS:term = $rS par?)
  flush
  pushCom "On peut aussi la démontrer par double inclusion."
  pushCom "Dans ce cas la démonstration commence par :"
  pushTac `(tactic|Montrons d'abord que $lS ⊆ $rS)

implement_endpoint (lang := fr) helpSinceSetEqSuggestion (lS rS : Term) : SuggestionM Unit := do
  pushCom "Le but est une égalité entre ensembles"
  pushCom "On peut la démontrer par réécriture avec la commande"
  pushTac `(tactic|Comme ?_ il suffit de montrer que ?_)
  flush
  pushCom "On peut commencer un calcul par"
  pushTac `(tactic|Calc $lS:term = $rS par?)
  flush
  pushCom "On peut aussi la démontrer par double inclusion."
  pushCom "Dans ce cas la démonstration commence par :"
  pushTac `(tactic|Montrons d'abord que $lS ⊆ $rS)

implement_endpoint (lang := fr) helpEqGoalSuggestion (lS rS : Term) : SuggestionM Unit := do
  pushCom "Le but est une égalité"
  pushCom "On peut la démontrer par réécriture avec la commande"
  pushTac `(tactic|On réécrit via ?_)
  flush
  pushCom "ou bien commencer un calcul par"
  pushTac `(tactic|Calc $lS:term = $rS par?)
  flush
  pushCom "On peut aussi tenter des combinaisons linéaires d'hypothèses avec"
  pushTac `(tactic|On combine [?_, ?_])

implement_endpoint (lang := fr) helpSinceEqGoalSuggestion (goal : Term) : SuggestionM Unit := do
  pushCom "Le but est une égalité"
  pushCom "On peut la démontrer par réécriture "
  pushTac `(tactic|Comme ?_ on conclut que $goal)
  flush
  pushCom "ou bien commencer un calcul par"
  pushTac `(tactic|Calc $goal:term par?)

implement_endpoint (lang := fr) helpIneqGoalSuggestion (goal : Term) (rel : String) : SuggestionM Unit := do
  pushCom "Le but est une inégalité"
  pushCom "On peut commencer un calcul par"
  pushTac `(tactic|Calc $goal:term par?)
  pushCom "La dernière ligne du calcul n'est pas forcément une égalité, cela peut être une inégalité."
  pushCom "De même la première ligne peut être une égalité. Au total les symboles de relations"
  pushCom "doivent s'enchaîner pour donner {rel}"
  flush
  pushCom "On peut aussi tenter des combinaisons linéaires d'hypothèses avec"
  pushTac `(tactic| On combine [?_, ?_])

implement_endpoint (lang := fr) helpSinceIneqGoalSuggestion (goal : Term) (rel : String) : SuggestionM Unit := do
  pushCom "Le but est une inégalité"
  pushCom "On peut commencer un calcul par"
  pushTac `(tactic|Calc $goal:term par?)
  pushCom "La dernière ligne du calcul n'est pas forcément une égalité, cela peut être une inégalité."
  pushCom "De même la première ligne peut être une égalité. Au total les symboles de relations"
  pushCom "doivent s'enchaîner pour donner {rel}"
  flush
  pushCom "Si cette inégalité découle immédiatement d’une hypothèse on peut utiliser"
  pushTac `(tactic|Comme ?_ on conclut que $goal)
  pushCom "en remplaçant le point d’interrogation par l’énoncé de l’hypothèse"

implement_endpoint (lang := fr) helpMemInterGoalSuggestion (elem le : Expr) : SuggestionM Unit := do
  pushCom "Le but est l'appartenance de {← elem.fmt} à l'intersection de {← le.fmt} avec un autre ensemble."
  pushCom "Une démonstration directe commence donc par :"
  pushTac `(tactic|Montrons d'abord que $(← elem.stx) ∈ $(← le.stx))

implement_endpoint (lang := fr) helpMemUnionGoalSuggestion (elem le re : Expr) : SuggestionM Unit := do
  pushCom "Le but est l'appartenance de {← elem.fmt} à la réunion de {← le.fmt} et {← re.fmt}."
  pushCom "Une démonstration directe commence donc par :"
  pushTac `(tactic|Montrons que $(← elem.stx) ∈ $(← le.stx))
  flush
  pushCom "ou bien par"
  pushTac `(tactic|Montrons que $(← elem.stx) ∈ $(← re.stx))

implement_endpoint (lang := fr) helpNoIdeaGoalSuggestion : SuggestionM Unit := do
  pushCom "Pas d’idée."

implement_endpoint (lang := fr) helpSubsetGoalSuggestion (l r : Format) (xN : Name) (lT : Term) :
    SuggestionM Unit := do
  pushCom "Le but est l’inclusion {l} ⊆ {r}"
  pushCom "Une démonstration directe commence donc par :"
  pushTac `(tactic| Soit $xN.ident:ident ∈ $lT)
  pushComment <| libre xN.ident

implement_endpoint (lang := fr) helpFalseGoalSuggestion : SuggestionM Unit := do
  pushCom "Le but est de montrer une contradiction."
  pushCom "On peut par exemple appliquer une hypothèse qui est une négation"
  pushCom "c'est à dire, par définition, de la forme P ⇒ False."

implement_endpoint (lang := fr) helpSinceFalseGoalSuggestion (goal : Term) : SuggestionM Unit := do
  pushCom "Le but est de montrer une contradiction."
  pushCom "On peut par exemple appliquer une hypothèse qui est une négation"
  pushCom "c'est à dire, par définition, de la forme P ⇒ False."
  pushCom "On peut également combiner deux faits qui se contredise directement par :"
  pushTac `(tactic|Comme ?_ et ?_ on conclut que $goal)
  pushCom "en remplaçant les points d’interrogation par deux faits qui se contredisent directement et découlent immédiatement d’hypothèses."
  flush
  pushCom "On peut également invoquer un fait manifestement faux (comme par exemple `0 = 1`) qui découle directement des hypothèses :"
  pushTac `(tactic|Comme ?_ on conclut que $goal)
  pushCom "en remplaçant le points d’interrogation par ce fait manifestement faux."

implement_endpoint (lang := fr) helpContraposeGoalSuggestion : SuggestionM Unit := do
  pushCom "Le but est une implication."
  pushCom "On peut débuter une démonstration par contraposition par :"
  pushTac `(tactic| On contrapose)

implement_endpoint (lang := fr) helpShowContrapositiveGoalSuggestion (stmt : Term) :
    SuggestionM Unit := do
  pushCom "Le but est une implication."
  pushCom "On peut débuter une démonstration par contraposition par :"
  pushTac `(tactic| Montrons la contraposée : $stmt)

open Verbose.Named in
implement_endpoint (lang := fr) helpByContradictionSuggestion (hyp : Ident) (assum : Term) : SuggestionM Unit := do
  pushCom "On peut débuter une démonstration par l’absurde par :"
  pushTac `(tactic| Supposons par l'absurde $hyp:ident : $assum)

open Verbose.NameLess in
implement_endpoint (lang := fr) helpByContradictionNLSuggestion (assum : Term) : SuggestionM Unit := do
  pushCom "On peut débuter une démonstration par l’absurde par :"
  pushTac `(tactic| Supposons par l'absurde que $assum)

open Verbose.Named in
implement_endpoint (lang := fr) helpNegationGoalSuggestion (hyp : Ident) (p : Format) (assum : Term) :
    SuggestionM Unit := do
  pushCom "Le but est de montrer la négation de {p}, c’est à dire montrer que {p} implique une contradiction."
  pushCom "Une démonstration directe commence donc par :"
  pushTac `(tactic| Supposons $hyp:ident : $assum)
  pushCom "Il restera à montrer une contradiction."

open Verbose.NameLess in
implement_endpoint (lang := fr) helpNegationNLGoalSuggestion (p : Format) (assum : Term) :
    SuggestionM Unit := do
  pushCom "Le but est de montrer la négation de {p}, c’est à dire montrer que {p} implique une contradiction."
  pushCom "Une démonstration directe commence donc par :"
  pushTac `(tactic| Supposons que $assum)
  pushCom "Il restera à montrer une contradiction."

open Verbose.Named in
implement_endpoint (lang := fr) helpNeGoalSuggestion (l r : Format) (lS rS : Term) (Hyp : Ident):
    SuggestionM Unit := do
  pushCom "Le but est de montrer la négation de {l} = {r}, c’est à dire montrer que {l} = {r} implique une contradiction."
  pushCom "Une démonstration directe commence donc par :"
  pushTac `(tactic| Supposons $Hyp:ident : $lS = $rS)
  pushCom "Il restera à montrer une contradiction."

open Verbose.NameLess in
implement_endpoint (lang := fr) helpNeGoalNLSuggestion (l r : Format) (lS rS : Term) :
    SuggestionM Unit := do
  pushCom "Le but est de montrer la négation de {l} = {r}, c’est à dire montrer que {l} = {r} implique une contradiction."
  pushCom "Une démonstration directe commence donc par :"
  pushTac `(tactic| Supposons que $lS = $rS)
  pushCom "Il restera à montrer une contradiction."

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
