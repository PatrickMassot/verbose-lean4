import Verbose.Tactics.Help
import Verbose.Spanish.Tactics

open Lean Meta Elab Tactic Term Verbose

namespace Verbose.Spanish

implement_endpoint (lang := es) try_this : CoreM String := pure "Intenta usar esto: "

implement_endpoint (lang := es) apply_suggestion : CoreM String := pure "Usar sugerencia"

open Lean.Parser.Tactic in
elab "ayuda" h:(colGt ident)? : tactic => do
unless (← verboseConfigurationExt.get).useHelpTactic do
  throwError "La táctica de ayuda no está habilitada."
match h with
| some h => do
    let (s, msg) ← gatherSuggestions (helpAtHyp (← getMainGoal) h.getId)
    if s.isEmpty then
      logInfo (msg.getD "Sin sugerencia")
    else
      addSuggestions (← getRef) s (header := "Ayuda")
| none => do
    let (s, msg) ← gatherSuggestions (helpAtGoal (← getMainGoal))
    if s.isEmpty then
      logInfo (msg.getD "Sin sugerencia")
    else
      addSuggestions (← getRef) s (header := "Ayuda")

def describe (t : Format) : String :=
match toString t with
| "ℝ" => "un número real"
| "ℕ" => "un número natural"
| "ℤ" => "un numero entero"
| t => "una expresión de tipo " ++ t

def describe_pl (t : Format) : String :=
match toString t with
| "ℝ" => "unos números reales"
| "ℕ" => "unos números naturales"
| "ℤ" => "unos números enteros"
| t => "unas expresiones de tipo " ++ t

def libre (s : Ident) : String := s!"El nombre {s.getId} puede libremente ser escogido entre los nombres disponibles."

def printIdentList (l : List Ident) : String := commaSep <| l.toArray.map (toString ·.getId)

def libres (ls : List Ident) : String :=
s!"Los nombres {printIdentList ls} pueden ser libremente escogidos entre los nombres disponibles."

def describeHypShape (hyp : Name) (headDescr : String) : SuggestionM Unit :=
  pushCom "La hipótesis {hyp} es de la forma “{headDescr}”"

def describeHypStart (hyp : Name) (headDescr : String) : SuggestionM Unit :=
  pushCom "La hipótesis {hyp} empieza con “{headDescr}”"

implement_endpoint (lang := es) helpExistRelSuggestion (hyp : Name) (headDescr : String)
    (nameS ineqIdent hS : Ident) (ineqS pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "Se puede usar con:"
  pushTac `(tactic|Por $hyp.ident:term tenemos $nameS:ident tal que ($ineqIdent : $ineqS) yy ($hS : $pS))
  pushComment <| libres [nameS, ineqIdent, hS]

implement_endpoint (lang := es) helpSinceExistRelSuggestion (hyp : Name) (headDescr : String)
    (nameS ineqIdent hS : Ident) (hypS ineqS pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "Se puede usar con:"
  pushTac `(tactic|Como $hypS:term elegimos $nameS:ident tal que ($ineqIdent : $ineqS) yy ($hS : $pS))
  pushComment <| libres [nameS, ineqIdent, hS]

implement_endpoint (lang := es) helpConjunctionSuggestion (hyp : Name) (h₁I h₂I : Ident) (p₁S p₂S : Term) :
    SuggestionM Unit := do
  let headDescr := "... yy ..."
  describeHypShape hyp headDescr
  pushCom "Se puede usar con:"
  pushTac `(tactic|Por $hyp.ident:term tenemos ($h₁I : $p₁S) ($h₂I : $p₂S))
  pushComment <| libres [h₁I, h₂I]

implement_endpoint (lang := es) helpSinceConjunctionSuggestion (hyp : Name) (p₁S p₂S : Term) :
    SuggestionM Unit := do
  let headDescr := "... yy ..."
  describeHypShape hyp headDescr
  pushCom "Se puede usar con:"
  pushTac `(tactic|Como $p₁S:term ∧ $p₂S se tiene $p₁S:term yy $p₂S)

implement_endpoint (lang := es) helpDisjunctionSuggestion (hyp : Name) : SuggestionM Unit := do
  pushCom "La hipótesis {hyp} tiene forma de « ... o ... »"
  pushCom "Se puede usar con:"
  pushTac `(tactic|Procedemos usando $hyp.ident:term)

implement_endpoint (lang := es) helpSinceDisjunctionSuggestion (hyp : Name) (p₁S p₂S : Term) : SuggestionM Unit := do
  describeHypShape hyp "... o ..."
  pushCom "Se puede usar con:"
  pushTac `(tactic|Decidimos en función de si $p₁S:term o $p₂S)

implement_endpoint (lang := es) helpImplicationSuggestion (hyp HN H'N : Name) (closes : Bool)
    (le re : Expr) : SuggestionM Unit := do
  pushCom "La hipótesis {hyp} es una implicación"
  if closes then do
    pushCom "La conclusión de esta implicación es el objetivo actual"
    pushCom "Hence one can use this assumption with:"
    pushTac `(tactic| Por $hyp.ident:term basta probar que $(← le.stx))
    flush
    pushCom "If one already has a proof {HN} of {← le.fmt} then one can use:"
    pushTac `(tactic|Concluimos por $hyp.ident:term aplicado a $HN.ident)
  else do
    pushCom "The premise de esta implicación is {← le.fmt}"
    pushCom "If you have a proof {HN} of {← le.fmt}"
    pushCom "Puedes usar esta hipótesis con:"
    pushTac `(tactic|Por $hyp.ident:term aplicado a $HN.ident:term tenemos $H'N.ident:ident : $(← re.stx):term)
    pushComment <| libre H'N.ident

implement_endpoint (lang := es) helpSinceImplicationSuggestion (stmt goalS leS : Term) (hyp : Name) (closes : Bool)
    (le re : Expr) : SuggestionM Unit := do
  pushCom "Assumption {hyp} es una implicación"
  if closes then do
    pushCom "La conclusión de esta implicación es el objetivo actual"
    pushCom "Entonces, uno puede usar esta hipótesis con:"
    pushTac `(tactic| Como $stmt:term basta probar que $(← le.stx):term)
    flush
    pushCom "Si ya tienes una prueba de {← le.fmt} puedes probar con:"
    pushTac `(tactic|Como $stmt:term yy $(← le.stx):term concluimos que $goalS)
  else do
    pushCom "la premisa de está implicación es {← le.fmt}"
    pushCom "Si tienes una prueba de {← le.fmt}"
    pushCom "Puedes usar esta hipótesis con:"
    pushTac `(tactic|Como $stmt:term yy $leS:term tenemos que $(← re.stx):term)

implement_endpoint (lang := es) helpEquivalenceSuggestion (hyp hyp'N : Name) (l r : Expr) : SuggestionM Unit := do
  pushCom "La hipótesis {hyp} es una equivalencia"
  pushCom "Se puede reemplazar el lado izquierdo ({← l.fmt}) con el lado derecho ({← r.fmt}) en el objetivo con:"
  pushTac `(tactic|Reescribimos usando $hyp.ident:term)
  flush
  pushCom "Se puede reemplazar el lado derecho del objetivo con:"
  pushTac `(tactic|Reescribimos usando ← $hyp.ident)
  flush
  pushCom "También se puede aplicar la misma sustitución en {hyp'N} con"
  pushTac `(tactic|Reescribimos usando $hyp.ident:term en la hipótesis $hyp'N.ident:ident)
  flush
  pushCom "o"
  pushTac `(tactic|Reescribimos usando ← $hyp.ident:term en la hipótesis $hyp'N.ident:ident)

implement_endpoint (lang := es) helpSinceEquivalenceSuggestion
    (hyp : Name) (stmt : Term) (l r : Expr) : SuggestionM Unit := do
  pushCom "La hipótesis {hyp} es una equivalencia"
  pushCom "Se puede reemplazar el lado izquierdo ({← l.fmt}) con el lado derecho ({← r.fmt}) en el objetivo o viceversa en el objetivo con:"
  pushTac `(tactic|Como $stmt:term basta probar que ?_)
  pushCom "reemplazando el signo de interrogación por el nuevo objetivo ."
  flush
  pushCom "Estas sustituciones también se pueden derivar de algunas de las hipótesis actuales con:"
  pushTac `(tactic|Como $stmt:term yy ?_ tenemos que ?_)
  pushCom "reemplzando el primer signo de interrogación por la información que quieras sustituir, luego sustituye el segundo por el nuevo dato obtenido."

implement_endpoint (lang := es) helpEqualSuggestion (hyp hyp' : Name) (closes : Bool) (l r : String) :
    SuggestionM Unit := do
  pushCom "La hipótesis {hyp} es una igualdad"
  if closes then
    pushComment <| s!"El objetivo actual es inmediato"
    pushComment   "Se puede usar con:"
    pushTac `(tactic|Concluimos por $hyp.ident:ident)
  else do
    pushCom "Puedes sustituir el lado izquierdo (es decir, {l}) por el lado derecho (es decir, {r}) en el objetivo con:"
    pushTac `(tactic|Reescribimos usando $hyp.ident:ident)
    flush
    pushCom "Puedes sustituir la parte derecha del objetivo por:"
    pushTac `(tactic|Reescribimos usando ← $hyp.ident:ident)
    flush
    pushCom "También puedes hacer las mismas sustituciones en otra hipótesis {hyp'} con: "
    pushTac `(tactic|Reescribimos usando $hyp.ident:ident en la hipótesis $hyp'.ident:ident)
    flush
    pushCom "o"
    pushTac `(tactic|Reescribimos usando ← $hyp.ident:ident en la hipótesis $hyp'.ident:ident)
    flush
    pushCom "Puede usarse en algún cálculo o combinación linear con:"
    pushTac `(tactic|Combinemos [$hyp.ident:term, ?_])
    pushCom "sustituyendo el signo de interrogación por uno o varios términos que demuestren las igualdades."

implement_endpoint (lang := es) helpSinceEqualSuggestion (hyp : Name)
    (closes : Bool) (l r : String) (leS reS goalS : Term) : SuggestionM Unit := do
  pushCom "La hipótesis {hyp} es una igualdad"
  let eq ← `($leS = $reS)
  if closes then
    pushComment <| s!"El objetivo actual es inmediato"
    pushComment   "La puedes usar con:"
    pushTac `(tactic|Como $eq:term concluimos que  $goalS)
  else do
    pushCom "Puedes sustituir el lado izquierdo (es decir, {l}) por el lado derecho (es decir, {r}) o viceversa en el objetivo con: "
    pushTac `(tactic|Como $eq:term basta probar que ?_)
    pushCom "reemplazando el signo de interrogación por un nuevo objetivo."
    flush
    pushCom "También se pueden realizar tales sustituciones en una expresión derivada de una de las hipótesis actuales mediante: "
    pushTac `(tactic|Como $eq:term yy ?_ tenemos que ?_)
    pushCom "sustituyendo el primer signo de interrogación por el dato que quieras sustituir, luego sustituye el segundo por el nuevo dato obtenido."

implement_endpoint (lang := es) helpIneqSuggestion (hyp : Name) (closes : Bool) : SuggestionM Unit := do
  pushCom "La hipótesis {hyp} es una desigualdad"
  if closes then
    pushCom "El objetivo actual se deriva inmediatamente de esta."
    pushCom "Se puede usar con:"
    pushTac `(tactic|Concluimos por $hyp.ident:ident)
  else do
    pushCom "Puede usarse en algún cálculo o combinación linear con:"
    pushTac `(tactic|Combinemos [$hyp.ident:term, ?_])
    pushCom "sustituyendo el signo de interrogación por uno o varios términos que demuestren igualdades o desigualdades."

implement_endpoint (lang := es) helpSinceIneqSuggestion (hyp : Name) (stmt goal : Term) (closes : Bool) : SuggestionM Unit := do
  pushCom "La hipótesis {hyp} es una desigualdad"
  if closes then
    pushCom "El objetivo actual se deriva inmediate de esta."
    pushCom "Se puede usar con:"
    pushTac `(tactic|Como $stmt:term concluimos que  $goal)
  else do
    flush
    pushCom "Puede usarse en algún cálculo o combinación linear con:"
    pushTac `(tactic| Como $stmt:term yy ?_ concluimos que  $goal)
    pushCom "sustituyendo el signo de interrogación por uno o varios términos que demuestren igualdades o desigualdades."

implement_endpoint (lang := es) helpMemInterSuggestion (hyp h₁ h₂ : Name) (elemS p₁S p₂S : Term) :
    SuggestionM Unit := do
  pushCom "La hipótesis {hyp} pertenece a una intersección"
  pushCom "Se puede usar con:"
  pushTac `(tactic|Por $hyp.ident:term tenemos ($h₁.ident : $elemS ∈ $p₁S) ($h₂.ident : $elemS ∈ $p₂S))
  pushComment <| libres [h₁.ident, h₂.ident]

implement_endpoint (lang := es) helpSinceMemInterSuggestion (stmt : Term) (hyp : Name) (mem₁ mem₂ : Term) :
    SuggestionM Unit := do
  pushCom "La hipótesis {hyp} pertenece a una intersección"
  pushCom "Se puede usar con:"
  pushTac `(tactic|Como $stmt:term tenemos que $mem₁:term yy $mem₂)

implement_endpoint (lang := es) helpMemUnionSuggestion (hyp : Name) :
    SuggestionM Unit := do
  pushCom "La hipótesis {hyp} pertenece a una unión"
  pushCom "Se puede usar con:"
  pushTac `(tactic|Procedemos usando $hyp.ident)

implement_endpoint (lang := es) helpSinceMemUnionSuggestion (elemS leS reS : Term) (hyp : Name) :
    SuggestionM Unit := do
  pushCom "La hipótesis {hyp} pertenece a una unión"
  pushCom "Se puede usar con:"
  pushTac `(tactic|Decidimos en función de si $elemS ∈ $leS o $elemS ∈ $reS)

implement_endpoint (lang := es) helpGenericMemSuggestion (hyp : Name) : SuggestionM Unit := do
  pushCom "La hipótesis {hyp} is una relación de pertenencia."

implement_endpoint (lang := es) helpContradictionSuggestion (hypId : Ident) : SuggestionM Unit := do
  pushComment <| "¡Esta hipótesis es una contradicción!"
  pushCom "Se puede deducir cualquier cosa:"
  pushTac `(tactic|(Probemos que hay una contradicción
                    Concluimos por $hypId:ident))

implement_endpoint (lang := es) helpSinceContradictionSuggestion
     (stmt goal : Term) : SuggestionM Unit := do
  pushComment <| "¡Esta hipótesis es una contradicción!"
  pushCom "Puedes deducir el objetivo de ella:"
  pushTac `(tactic|Como $stmt:term concluimos que  $goal)

implement_endpoint (lang := es) helpSubsetSuggestion (hyp x hx hx' : Name)
    (r : Expr) (l ambientTypePP : Format) : SuggestionM Unit := do
  pushCom "La hipótesis {hyp} demuestra la inclusión de {l} en {← r.fmt}."
  pushCom "Se puede usar con:"
  pushTac `(tactic| Por $hyp.ident:ident aplicado a $x.ident usando $hx.ident tenemos $hx'.ident:ident : $x.ident ∈ $(← r.stx))
  pushCom "donde {x} es {describe ambientTypePP} yy {hx} demostrando que {x} ∈ {l}."
  pushComment <| libre hx'.ident

implement_endpoint (lang := es) helpSinceSubsetSuggestion (hyp x : Name) (stmt new : Term)
    (l r : Expr) (ambientTypePP : Format) : SuggestionM Unit := do
  pushCom "La hipótesis {hyp} demuestra la inclusión de {← l.fmt} in {← r.fmt}."
  pushCom "Se puede usar con:"
  pushTac `(tactic| Como $stmt:term yy $x.ident ∈ $(← l.stx) tenemos que $new:term)
  pushCom "donde {x} es {describe ambientTypePP}"

implement_endpoint (lang := es) assumptionClosesSuggestion (hypId : Ident) : SuggestionM Unit := do
  pushCom "Esta hipótesis es exactamente lo qué se necesita probar"
  pushCom "Se puede usar con:"
  pushTac `(tactic|Concluimos por $hypId:ident)

implement_endpoint (lang := es) assumptionUnfoldingSuggestion (hypId : Ident) (expandedHypTypeS : Term) :
    SuggestionM Unit := do
  pushCom "Esta hipótesis empieza aplicando una definición."
  pushCom "Puedes hacerla explícita con:"
  pushTac `(tactic|Reformulamos $hypId:ident como$expandedHypTypeS)
  flush

implement_endpoint (lang := es) helpForAllRelExistsRelSuggestion (hyp var_name' n₀ hn₀ : Name)
    (headDescr hypDescr : String) (t : Format) (hn'S ineqIdent : Ident) (ineqS p'S : Term) :
    SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Se puede usar con:"
  pushTac `(tactic|Por $hyp.ident:term aplicado a $n₀.ident usando $hn₀.ident tenemos $var_name'.ident:ident tal que ($ineqIdent : $ineqS) yy ($hn'S : $p'S))
  pushCom "donde {n₀} es {describe t} yy {hn₀} es una demostración de {hypDescr}."
  pushComment <| libres [var_name'.ident, ineqIdent, hn'S]

implement_endpoint (lang := es) helpSinceForAllRelExistsRelSuggestion (stmt :
    Term) (hyp var_name' n₀ : Name) (stmtn₀ : Term)
    (stmtn₀Str headDescr : String) (t : Format) (ineqS p'S : Term) :
    SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Se puede usar con:"
  pushTac `(tactic|Como $stmt:term yy $stmtn₀ se tiene $var_name'.ident:ident tal que $ineqS yy $p'S)
  pushCom "donde {n₀} es {describe t} luego la relación {stmtn₀Str} se sigue inmediatamente por alguna hipótesis."
  pushComment <| libre var_name'.ident

implement_endpoint (lang := es) helpForAllRelExistsSimpleSuggestion (hyp n' hn' n₀ hn₀ : Name)
    (headDescr n₀rel : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Se puede usar con:"
  pushTac `(tactic|Por $hyp.ident:term aplicado a $n₀.ident usando $hn₀.ident tenemos $n'.ident:ident tal que ($hn'.ident : $p'S))
  pushCom "donde {n₀} es {describe t} yy {hn₀} una demostración de {n₀rel}"
  pushComment <| libres [n'.ident, hn'.ident]

implement_endpoint (lang := es) helpSinceForAllRelExistsSimpleSuggestion (stmt : Term)
  (hyp n' n₀ : Name)
  (stmtn₀ : Term) (stmtn₀Str headDescr : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Se puede usar con:"
  pushTac `(tactic|Como $stmt:term yy $stmtn₀ tenemos que $n'.ident:ident yy $p'S)
  pushCom "donde {n₀} es {describe t} yy la relación {stmtn₀Str} se sigue directamente de alguna hipótesis."
  pushComment <| libre n'.ident

implement_endpoint (lang := es) helpForAllRelGenericSuggestion (hyp n₀ hn₀ : Name)
    (headDescr n₀rel : String) (t : Format) (newsI : Ident) (pS : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Se puede usar con:"
  pushTac `(tactic|Por $hyp.ident:term aplicado a $n₀.ident usando $hn₀.ident tenemos ($newsI : $pS))
  pushCom "donde {n₀} es {describe t} yy {hn₀} una demostración de {n₀rel}"
  pushComment <| libre newsI

implement_endpoint (lang := es) helpSinceForAllRelGenericSuggestion (stmt : Term) (hyp n₀ : Name)
  (stmtn₀ : Term)
  (stmtn₀Str headDescr : String) (t : Format) (pS : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Se puede usar con:"
  pushTac `(tactic|Como $stmt:term yy $stmtn₀ tenemos que $pS:term)
  pushCom "donde {n₀} es {describe t} luego {stmtn₀Str} se sigue inmediatamente de alguna hipótesis."

implement_endpoint (lang := es) helpForAllSimpleExistsRelSuggestion (hyp var_name' nn₀ : Name)
    (headDescr : String) (t : Format) (hn'S ineqIdent : Ident) (ineqS p'S : Term) :
    SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Se puede usar con:"
  pushTac `(tactic|Por $hyp.ident:term aplicado a $nn₀.ident tenemos $var_name'.ident:ident tal que ($ineqIdent : $ineqS) yy ($hn'S : $p'S))
  pushCom "donde {nn₀} es {describe t}"
  pushComment <| libres [var_name'.ident, ineqIdent, hn'S]

implement_endpoint (lang := es) helpSinceForAllSimpleExistsRelSuggestion (stmt : Term) (hyp var_name' nn₀ : Name)
    (headDescr : String) (t : Format) (ineqS p'S : Term) :
    SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Se puede usar con:"
  pushTac `(tactic|Como $stmt:term se tiene $var_name'.ident:ident tal que $ineqS yy $p'S)
  pushCom "donde {nn₀} es {describe t}"
  pushComment <| libre var_name'.ident

implement_endpoint (lang := es) helpForAllSimpleExistsSimpleSuggestion (hyp var_name' hn' nn₀  : Name)
    (headDescr : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Se puede usar con:"
  pushTac `(tactic|Por $hyp.ident:term aplicado a $nn₀.ident tenemos $var_name'.ident:ident tal que ($hn'.ident : $p'S))
  pushCom "donde {nn₀} es {describe t}"
  pushComment <| libres [var_name'.ident, hn'.ident]

implement_endpoint (lang := es) helpSinceForAllSimpleExistsSimpleSuggestion (stmt : Term) (hyp var_name' nn₀  : Name)
    (headDescr : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Se puede usar con:"
  pushTac `(tactic|Como $stmt:term se tiene $var_name'.ident:ident tal que $p'S)
  pushCom "donde {nn₀} es {describe t}"
  pushComment <| libre var_name'.ident

implement_endpoint (lang := es) helpForAllSimpleForAllRelSuggestion (hyp nn₀ var_name'₀ H h : Name)
    (headDescr rel₀ : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  pushCom "La hipótesis {hyp} empieza con “{headDescr}"
  pushCom "Se puede usar con:"
  pushTac `(tactic|Por $hyp.ident:term aplicado a $nn₀.ident yy $var_name'₀.ident usando $H.ident tenemos ($h.ident : $p'S))
  pushCom "donde {nn₀} yy {var_name'₀} forman {describe_pl t} yy {H} una demostración de {rel₀}"
  pushComment <| libre h.ident

implement_endpoint (lang := es) helpSinceForAllSimpleForAllRelSuggestion (stmt rel₀S : Term) (hyp nn₀ var_name'₀ : Name)
    (headDescr rel₀ : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Se puede usar con:"
  pushTac `(tactic|Como $stmt:term yy $rel₀S:term tenemos que $p'S:term)
  pushCom "donde {nn₀} yy {var_name'₀} forman {describe_pl t} yy {rel₀} que se sigue inmediatamente por alguna hipótesis."

implement_endpoint (lang := es) helpForAllSimpleGenericSuggestion (hyp nn₀ hn₀ : Name) (headDescr : String)
    (t : Format) (pS : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Se puede usar con:"
  pushTac `(tactic|Por $hyp.ident:term aplicado a $nn₀.ident tenemos ($hn₀.ident : $pS))
  pushCom "donde {nn₀} es {describe t}"
  pushComment <| libre hn₀.ident
  flush
  pushCom "Si esta hipótesis no se va a volver a utilizar en su forma general, también se puede especializar {hyp} con"
  pushTac `(tactic|Usamos $hyp.ident:ident en $nn₀.ident)

implement_endpoint (lang := es) helpSinceForAllSimpleGenericSuggestion (stmt : Term) (hyp nn₀ : Name) (headDescr : String)
    (t : Format) (pS : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Se puede usar con:"
  pushTac `(tactic|Como $stmt:term tenemos que $pS:term)
  pushCom "donde {nn₀} es {describe t}"
  flush
  pushCom "Si esta hipótesis no se va a volver a utilizar en su forma general, también se puede especializar {hyp} con"
  pushTac `(tactic|Usamos $hyp.ident:ident en $nn₀.ident)

implement_endpoint (lang := es) helpForAllSimpleGenericApplySuggestion (prf : Expr) (but : Format) :
    SuggestionM Unit := do
  let prfS ← prf.toMaybeAppliedES
  pushCom "Como el objetivo es {but}, se puede usar:"
  pushTac `(tactic|Concluimos por $prfS)

implement_endpoint (lang := es) helpExistsSimpleSuggestion (hyp n hn : Name) (headDescr : String)
    (pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "Se puede usar con:"
  pushTac `(tactic|Por $hyp.ident:term tenemos $n.ident:ident tal que ($hn.ident : $pS))
  pushComment <| libres [n.ident, hn.ident]

implement_endpoint (lang := es) helpSinceExistsSimpleSuggestion (stmt : Term) (hyp n : Name) (headDescr : String)
    (pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "Se puede usar con:"
  pushTac `(tactic| Como $stmt:term tenemos que $n.ident:ident yy $pS)
  pushComment <| libre n.ident

implement_endpoint (lang := es) helpDataSuggestion (hyp : Name) (t : Format) : SuggestionM Unit := do
  pushComment <| s!"El objeto {hyp}" ++ match t with
    | "ℝ" => " es un número real fijo."
    | "ℕ" => " es un número natural fijo."
    | "ℤ" => " es un número entero fijo"
    | s => s!" : {s} está fijado."

implement_endpoint (lang := es) helpNothingSuggestion : SuggestionM Unit := do
  pushCom "No tengo nada que decir de esta hipótesis."
  flush

implement_endpoint (lang := es) helpNothingGoalSuggestion : SuggestionM Unit := do
  pushCom "No tengo nada que decir de este objetivo."
  flush

def descrGoalHead (headDescr : String) : SuggestionM Unit :=
 pushCom "El objetivo empieza con “{headDescr}”"

def descrGoalShape (headDescr : String) : SuggestionM Unit :=
 pushCom "El objetivo tiene la forma de “{headDescr}”"

def descrDirectProof : SuggestionM Unit :=
 pushCom "Luego una demostración directa puede empezar con: "

implement_endpoint (lang := es) helpUnfoldableGoalSuggestion (expandedGoalTypeS : Term) :
    SuggestionM Unit := do
  pushCom "El objetivo empieza aplicando una definición."
  pushCom "Se puede hacer explícita con:"
  pushTac `(tactic|Probemos que $expandedGoalTypeS)
  flush

implement_endpoint (lang := es) helpAnnounceGoalSuggestion (actualGoalS : Term) : SuggestionM Unit := do
  pushCom "El siguiente paso es anunciarlo:"
  pushTac `(tactic| Probemos ahora que $actualGoalS)

implement_endpoint (lang := es) helpFixSuggestion (headDescr : String) (ineqS : TSyntax `fixDecl) :
    SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Sea $ineqS)

implement_endpoint (lang := es) helpExistsRelGoalSuggestion (headDescr : String) (n₀ : Name) (t : Format)
    (fullTgtS : Term) : SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Probemos que $n₀.ident basta : $fullTgtS)
  pushCom "reemplazando {n₀} por {describe t}"

implement_endpoint (lang := es) helpExistsGoalSuggestion (headDescr : String) (nn₀ : Name) (t : Format)
    (tgt : Term) : SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Probemos que $nn₀.ident basta : $tgt)
  pushCom "replacing {nn₀} by {describe t}"

implement_endpoint (lang := es) helpConjunctionGoalSuggestion (p p' : Term) : SuggestionM Unit := do
  descrGoalShape "... yy ..."
  descrDirectProof
  pushTac `(tactic|Primero probemos que $p)
  pushCom "Una vez terminada esta primera demostración, quedará por demostrar que {← p'.fmt}"
  flush
  pushCom "One can also start with"
  pushTac `(tactic|Primero probemos que $p')
  pushCom "Una vez terminada esta primera demostración, quedará por demostrar que {← p.fmt}"

implement_endpoint (lang := es) helpDisjunctionGoalSuggestion (p p' : Term) : SuggestionM Unit := do
  descrGoalShape "... o ..."
  pushCom "Por lo tanto, una demostración directa comienza indicando qué afirmación se va a demostrar:"
  pushTac `(tactic|Probemos que $p)
  flush
  pushCom "o:"
  pushTac `(tactic|Probemos que $p')

open Verbose.Named in
implement_endpoint (lang := es) helpImplicationGoalSuggestion (headDescr : String) (Hyp : Name)
    (leStx : Term) : SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic| Supongamos $Hyp.ident:ident : $leStx)
  pushComment <| libre Hyp.ident

open Verbose.NameLess in
implement_endpoint (lang := es) helpImplicationGoalNLSuggestion (headDescr : String) (leStx : Term) : SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic| Supongamos que $leStx)

implement_endpoint (lang := es) helpEquivalenceGoalSuggestion (mpF mrF : Format) (mpS mrS : Term) :
    SuggestionM Unit := do
  pushCom "El objetivo es una equivalencia (↔). Se puede demostrar la implicación de izquierda a derecha con:"
  pushTac `(tactic|Primero probemos que $mpS)
  pushCom "Una vez demostrada esta primera afirmación, quedará por demostrar que {mrF}"
  flush
  pushCom "También se puede empezar por: "
  pushTac `(tactic|Primero probemos que $mrS)
  pushCom "Entonces, una vez terminada esta primera demostración, quedará por demostrar que {mpF}"

implement_endpoint (lang := es) helpSetEqSuggestion (lS rS : Term) : SuggestionM Unit := do
  pushCom "El objetivo es una igualdad entre conjuntos"
  pushCom "Se puede reescribirla usando:"
  pushTac `(tactic|Reescribimos usando ?_)
  flush
  pushCom "o mediante cálculos usando"
  pushTac `(tactic|Calc $lS:term = $rS since?)
  flush
  pushCom "también puede demostrarse por doble inclusión."
  pushCom "En tal caso, la prueba empezaría por:"
  pushTac `(tactic|Primero probemos que $lS ⊆ $rS)

implement_endpoint (lang := es) helpSinceSetEqSuggestion (lS rS : Term) : SuggestionM Unit := do
  pushCom "El objetivo es una igualdad entre conjuntos"
  pushCom "Se puede reescribirla usando:"
  pushTac `(tactic|Como ?_ basta probar que ?_)
  flush
  pushCom "o mediante cálculos usando"
  pushTac `(tactic|Calc $lS:term = $rS since?)
  flush
  pushCom "también puede demostrarse por doble inclusión."
  pushCom "En tal caso, la prueba empezaría por:"
  pushTac `(tactic|Primero probemos que $lS ⊆ $rS)

implement_endpoint (lang := es) helpEqGoalSuggestion (lS rS : Term) : SuggestionM Unit := do
  pushCom "El objetivo es una igualdad"
  pushCom "Se puede reescribirla usando:"
  pushTac `(tactic|Reescribimos usando ?_)
  flush
  pushCom "o mediante cálculos usando"
  pushTac `(tactic|Calc $lS:term = $rS since?)
  flush
  pushCom "también puedes aplicar una combinación lineal de tus hipótesis con"
  pushTac `(tactic|Combinemos [?_, ?_])

implement_endpoint (lang := es) helpSinceEqGoalSuggestion (goal : Term) : SuggestionM Unit := do
  pushCom "El objetivo es una igualdad"
  pushCom "Se puede reescribirla usando:"
  pushTac `(tactic|Como ?_ concluimos que  $goal)
  flush
  pushCom "o start a computation usando"
  pushTac `(tactic|Calc $goal:term since?)

implement_endpoint (lang := es) helpIneqGoalSuggestion (goal : Term) (rel : String) : SuggestionM Unit := do
  pushCom "El objetivo es una desigualdad"
  pushCom "Puede calcularse usando"
  pushTac `(tactic|Calc $goal:term since?)
  pushCom "El último cálculo no es necesariamente una igualdad, sino una desigualdad."
  pushCom "De la misma forma, la primera línea puede ser una igualdad. Al final los símbolos de relación "
  pushCom "deben componerse para obtener {rel}"
  flush
  pushCom "también puedes aplicar una combinación lineal de tus hipótesis con"
  pushTac `(tactic| Combinemos [?_, ?_])

implement_endpoint (lang := es) helpSinceIneqGoalSuggestion (goal : Term) (rel : String) : SuggestionM Unit := do
  pushCom "El objetivo es una desigualdad"
  pushCom "Puede calcularse usando"
  pushTac `(tactic|Calc $goal:term since?)
  pushCom "El último cálculo no es necesariamente una igualdad, sino una desigualdad."
  pushCom "De la misma forma, la primera línea puede ser una igualdad. Al final los símbolos de relación "
  pushCom "deben componerse para obtener {rel}"
  flush
  pushCom "Si esta desigualdad se sigue directamente de una hipótesis, se puede usar:"
  pushTac `(tactic|Como ?_ concluimos que  $goal)
  pushCom "sustituyendo el signo de interrogación por la formulación de la hipótesis."

implement_endpoint (lang := es) helpMemInterGoalSuggestion (elem le : Expr) : SuggestionM Unit := do
  pushCom "El objetivo es demostrar que {← elem.fmt} pertenece a la intersección de {← le.fmt} con otro conjunto."
  pushCom "Luego una demostración empezaría con: "
  pushTac `(tactic|Primero probemos que $(← elem.stx) ∈ $(← le.stx))

implement_endpoint (lang := es) helpMemUnionGoalSuggestion (elem le re : Expr) : SuggestionM Unit := do
  pushCom "El objetivo es demostrar que {← elem.fmt} pertenece a la unión de {← le.fmt} con {← re.fmt}."
  descrDirectProof
  pushTac `(tactic|Probemos que $(← elem.stx) ∈ $(← le.stx))
  flush
  pushCom "o por:"
  pushTac `(tactic|Probemos que $(← elem.stx) ∈ $(← re.stx))

implement_endpoint (lang := es) helpNoIdeaGoalSuggestion : SuggestionM Unit := do
  pushCom "Ni idea."

implement_endpoint (lang := es) helpSubsetGoalSuggestion (l r : Format) (xN : Name) (lT : Term) :
    SuggestionM Unit := do
  pushCom "El objetivo la inclusión {l} ⊆ {r}"
  descrDirectProof
  pushTac `(tactic| Sea $xN.ident:ident ∈ $lT)
  pushComment <| libre xN.ident

implement_endpoint (lang := es) helpFalseGoalSuggestion : SuggestionM Unit := do
  pushCom "El objetivo es demostrar que hay una contradicción."
  pushCom "Se puede aplicar una suposición que sea una negación"
  pushCom "es decir, una suposición de la forma P → falso."

implement_endpoint (lang := es) helpSinceFalseGoalSuggestion (goal : Term) : SuggestionM Unit := do
  pushCom "El objetivo es demostrar que hay una contradicción"
  pushCom "Se puede aplicar una suposición que sea una negación"
  pushCom "es decir, una suposición de la forma P → falso."
  pushCom "También puedes combinar dos hipótesis que claramente se contradigan usando: "
  pushTac `(tactic|Como ?_ yy ?_ concluimos que  $goal)
  pushCom "sustituyendo los signos de interrogación por esos dos hechos que se deducen directamente de las hipótesis."
  flush
  pushCom "También se puede invocar un hecho claramente falso (como «0 = 1») que se deduce directamente de una suposición."
  pushTac `(tactic|Como ?_ concluimos que  $goal)
  pushCom "reemplazando el signo de interrogación por cualquier hecho claramente falso."

implement_endpoint (lang := es) helpContraposeGoalSuggestion : SuggestionM Unit := do
  pushCom "El objetivo es una implicación."
  pushCom "Se puede empezar una demostración por contraposición usando"
  pushTac `(tactic| Contrapongamos)

implement_endpoint (lang := es) helpShowContrapositiveGoalSuggestion (stmt : Term) :
    SuggestionM Unit := do
  pushCom "El objetivo es una implicación."
  pushCom "Se puede empezar una demostración por contraposición usando"
  pushTac `(tactic| Probemos el contrapositivo: $stmt)

open Verbose.Named in
implement_endpoint (lang := es) helpByContradictionSuggestion (hyp : Ident) (assum : Term) : SuggestionM Unit := do
  pushCom "Se puede empezar una demostración por contradicción usando"
  pushTac `(tactic| Supongamos para una contradicción $hyp:ident : $assum)

open Verbose.NameLess in
implement_endpoint (lang := es) helpByContradictionNLSuggestion (assum : Term) : SuggestionM Unit := do
  pushCom "Se puede empezar una demostración por contradicción usando"
  pushTac `(tactic| Supongamos para una contradicción que $assum)

open Verbose.Named in
implement_endpoint (lang := es) helpNegationGoalSuggestion (hyp : Ident) (p : Format) (assum : Term) :
    SuggestionM Unit := do
  pushCom "El objetivo es la negación de {p}, es decir, {p} implica una contradicción"
  pushCom "Luego una prueba directa empieza con"
  pushTac `(tactic| Supongamos $hyp:ident : $assum)
  pushCom "Luego solo queda demostrar la contradicción."

open Verbose.NameLess in
implement_endpoint (lang := es) helpNegationNLGoalSuggestion (p : Format) (assum : Term) :
    SuggestionM Unit := do
  pushCom "El objetivo es la negación de {p}, es decir, {p} implica una contradicción"
  pushCom "Luego una prueba directa empieza con"
  pushTac `(tactic| Supongamos que $assum)
  pushCom "Luego solo queda demostrar la contradicción."

open Verbose.Named in
implement_endpoint (lang := es) helpNeGoalSuggestion (l r : Format) (lS rS : Term) (Hyp : Ident):
    SuggestionM Unit := do
  pushCom "El objetivo es la negación de {l} = {r}, es decir, {l} = {r} implica una contradicción"
  pushCom "Luego una prueba directa empieza con"
  pushTac `(tactic| Supongamos $Hyp:ident : $lS = $rS)
  pushCom "Luego solo queda demostrar la contradicción."

open Verbose.NameLess in
implement_endpoint (lang := es) helpNeGoalNLSuggestion (l r : Format) (lS rS : Term) :
    SuggestionM Unit := do
  pushCom "El objetivo es la negación  {l} = {r}, , es decir, {l} = {r} implica una contradicción"
  pushCom "Luego una prueba directa empieza con"
  pushTac `(tactic| Supongamos que $lS = $rS)
  pushCom "Luego solo quedaría demostrar la contradicción."

setLang es

set_option linter.unusedVariables false

configureAnonymousGoalSplittingLemmas Iff.intro Iff.intro' And.intro And.intro' abs_le_of_le_le abs_le_of_le_le'

configureHelpProviders DefaultHypHelp DefaultGoalHelp

set_option linter.unusedTactic false

/--
info: Ayuda
  • La hipótesis h starts with “∀ n > 0, ...”
    Se puede usar con:
    Por h aplicado a n₀ usando hn₀ tenemos (hyp : P n₀)
    where n₀ is a natural number yy hn₀ is a proof of the fact que n₀ > 0
    The name hyp can be chosen freely among available names.
-/
-- #guard_msgs in
example {P : ℕ → Prop} (h : ∀ n > 0, P n) : P 2 := by
  ayuda h
  apply h
  norm_num

/--
info: Ayuda
  • La hipótesis h tiene forma de “∃ n > 0, ...”
    Se puede usar con:
    Por h tenemos n tal que (n_pos : n > 0) yy (hn : P n)
    The names n, n_pos yy hn can be chosen freely among available names.
-/
-- #guard_msgs in
example {P : ℕ → Prop} (h : ∃ n > 0, P n) : True := by
  ayuda h
  trivial

/--
info: Ayuda
  • La hipótesis h tiene forma de “∃ ε > 0, ...”
    Se puede usar con:
    Por h tenemos ε tal que (ε_pos : ε > 0) yy (hε : P ε)
    The names ε, ε_pos yy hε can be chosen freely among available names.
-/
-- #guard_msgs in
example {P : ℝ → Prop} (h : ∃ ε > 0, P ε) : True := by
  ayuda h
  trivial

/--
info: Ayuda
  • La hipótesis h starts with “∀ n, ...”
    Se puede usar con:
    Por h aplicado a n₀ tenemos (hn₀ : P n₀ → Q n₀)
    where n₀ is a natural number
    The name hn₀ can be chosen freely among available names.
  • If this assumption won't be used again in its general shape, one can also specialize h with
    We apply h to n₀
-/
-- #guard_msgs in
example (P Q : ℕ → Prop) (h : ∀ n, P n → Q n) (h' : P 2) : Q 2 := by
  ayuda h
  exact h 2 h'

/--
info: Ayuda
  • La hipótesis h starts with “∀ n, ...”
    Se puede usar con:
    Por h aplicado a n₀ tenemos (hn₀ : P n₀)
    where n₀ is a natural number
    The name hn₀ can be chosen freely among available names.
  • If this assumption won't be used again in its general shape, one can also specialize h with
    We apply h to n₀
  • Como the goal is P 2, one can use:
    Concluimos por h aplicado a 2
-/
-- #guard_msgs in
example (P : ℕ → Prop) (h : ∀ n, P n) : P 2 := by
  ayuda h
  exact h 2

/--
info: Ayuda
  • La hipótesis h es una implicación
    La conclusión de esta implicación es el objetivo actual
    Hence one can use this assumption with:
    Por h basta probar que P 1
  • If one already has a proof H of P 1 then one can use:
    Concluimos por h aplicado a H
-/
-- #guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 → Q 2) (h' : P 1) : Q 2 := by
  ayuda h
  exact h h'

/--
info: Ayuda
  • La hipótesis h es una implicación
    The premise de esta implicación is P 1
    If you have a proof H of P 1
    Puedes usar esta hipótesis con:
    Por h aplicado a H tenemos H' : Q 2
    The name H' can be chosen freely among available names.
-/
-- #guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 → Q 2) : True := by
  ayuda h
  trivial

/--
info: Ayuda
  • La hipótesis h tiene forma de “... yy ...”
    Se puede usar con:
    Por h tenemos (h_1 : P 1) (h' : Q 2)
    The names h_1 yy h' can be chosen freely among available names.
-/
-- #guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 ∧ Q 2) : True := by
  ayuda h
  trivial

/--
info: Ayuda
  • La hipótesis h es una equivalencia
    One can use it to replace the left-hand-side (namely ∀ n ≥ 2, P n) by the right-hand side (namely ∀ (l : ℕ), Q l) in the goal with:
    Reescribimos usando h
  • One can use it to replace the right-hand-side in the goal with:
    Reescribimos usando ← h
  • One can also perform such replacements in an assumption hyp with
    Reescribimos usando h en hyp
  • o
    Reescribimos usando ← h en hyp
-/
-- #guard_msgs in
example (P Q : ℕ → Prop) (h : (∀ n ≥ 2, P n) ↔  ∀ l, Q l) : True := by
  ayuda h
  trivial

/--
info: Ayuda
  • El objetivo tiene forma de “... yy ...”
    Luego una prueba directa empieza yy
    Primero probemos que True
    After finish this first proof, it will remain to prove que 1 = 1
  • One can also start with
    Primero probemos que 1 = 1
    then, after finishing this first proof, il will remain to prove que True
-/
-- #guard_msgs in
example : True ∧ 1 = 1 := by
  ayuda
  exact ⟨trivial, rfl⟩

/--
info: Ayuda
  • La hipótesis h tiene forma de « ... o ... »
    Se puede usar con:
    Procedemos usando h
-/
-- #guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 ∨ Q 2) : True := by
  ayuda h
  trivial

/--
info: Ayuda
  • El objetivo tiene forma de “... o ...”
    Hence a direct proof starts with announcing which alternative will be proven:
    Probemos que True
  • o:
    Probemos que False
-/
-- #guard_msgs in
example : True ∨ False := by
  ayuda
  left
  trivial

/-- info: I have nothing to say about this assumption. -/
-- #guard_msgs in
example (P : Prop) (h : P) : True := by
  ayuda h
  trivial

-- TODO: Improve this ayuda message (low priority since it is very rare)
/--
info: Ayuda
  • ¡Esta hipótesis es una contradicción!
    One can deduce anything from it with:
    ( Let's prove it's contradictory
        Concluimos por h)
-/
-- #guard_msgs in
example (h : False) : 0 = 1 := by
  ayuda h
  trivial

/--
info: Ayuda
  • La hipótesis h es una implicación
    The premise de esta implicación is l - n = 0
    If you have a proof H of l - n = 0
    Puedes usar esta hipótesis con:
    Por h aplicado a H tenemos H' : P l k
    The name H' can be chosen freely among available names.
-/
-- #guard_msgs in
example (P : ℕ → ℕ → Prop) (k l n : ℕ) (h : l - n = 0 → P l k) : True := by
  ayuda h
  trivial

/--
info: Ayuda
  • La hipótesis h starts with “∀ k ≥ 2, ∃ n ≥ 3, ...”
    Se puede usar con:
    Por h aplicado a k₀ usando hk₀ tenemos
        n tal que (n_sup : n ≥ 3) yy (hn : ∀ (l : ℕ), l - n = 0 → P l k₀)
    where k₀ is a natural number yy hk₀ is a proof of the fact que k₀ ≥ 2.
    The names n, n_sup yy hn can be chosen freely among available names.
-/
-- #guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  ayuda h
  trivial

/--
info: Ayuda
  • La hipótesis h starts with “∀ k n, k ≥ n ⇒ ...
    Se puede usar con:
    Por h aplicado a k₀ yy n₀ usando H tenemos (h_1 : ∀ (l : ℕ), l - n₀ = 0 → P l k₀)
    where k₀ yy n₀ are some natural numbers yy H is a proof of k₀ ≥ n₀
    The name h_1 can be chosen freely among available names.
-/
-- #guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k, ∀ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  ayuda h
  trivial

/--
info: Ayuda
  • La hipótesis h starts with “∀ k ≥ 2, ∃ n_1 ≥ 3, ...”
    Se puede usar con:
    Por h aplicado a k₀ usando hk₀ tenemos
        n_1 tal que (n_1_sup : n_1 ≥ 3) yy (hn_1 : ∀ (l : ℕ), l - n = 0 → P l k₀)
    where k₀ is a natural number yy hk₀ is a proof of the fact que k₀ ≥ 2.
    The names n_1, n_1_sup yy hn_1 can be chosen freely among available names.
-/
-- #guard_msgs in
example (P : ℕ → ℕ → Prop) (n : ℕ) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  ayuda h
  trivial

/--
info: Ayuda
  • La hipótesis h tiene forma de “∃ n ≥ 5, ...”
    Se puede usar con:
    Por h tenemos n tal que (n_sup : n ≥ 5) yy (hn : P n)
    The names n, n_sup yy hn can be chosen freely among available names.
-/
-- #guard_msgs in
example (P : ℕ → Prop) (h : ∃ n ≥ 5, P n) : True := by
  ayuda h
  trivial

/--
info: Ayuda
  • La hipótesis h starts with “∀ k ≥ 2, ∃ n ≥ 3, ...”
    Se puede usar con:
    Por h aplicado a k₀ usando hk₀ tenemos n tal que (n_sup : n ≥ 3) yy (hn : P n k₀)
    where k₀ is a natural number yy hk₀ is a proof of the fact que k₀ ≥ 2.
    The names n, n_sup yy hn can be chosen freely among available names.
-/
-- #guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, P n k) : True := by
  ayuda h
  trivial

/--
info: Ayuda
  • La hipótesis h tiene forma de “∃ n, ...”
    Se puede usar con:
    Por h tenemos n tal que (hn : P n)
    The names n yy hn can be chosen freely among available names.
-/
-- #guard_msgs in
example (P : ℕ → Prop) (h : ∃ n : ℕ, P n) : True := by
  ayuda h
  trivial

/--
info: Ayuda
  • La hipótesis h starts with “∀ k, ∃ n, ...”
    Se puede usar con:
    Por h aplicado a k₀ tenemos n tal que (hn : P n k₀)
    where k₀ is a natural number
    The names n yy hn can be chosen freely among available names.
-/
-- #guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k, ∃ n : ℕ, P n k) : True := by
  ayuda h
  trivial

/--
info: Ayuda
  • La hipótesis h starts with “∀ k ≥ 2, ∃ n, ...”
    Se puede usar con:
    Por h aplicado a k₀ usando hk₀ tenemos n tal que (hn : P n k₀)
    where k₀ is a natural number yy hk₀ is a proof of the fact que k₀ ≥ 2
    The names n yy hn can be chosen freely among available names.
-/
-- #guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n : ℕ, P n k) : True := by
  ayuda h
  trivial

/--
info: Ayuda
  • El objetivo starts with “∃ n, ...”
    Luego una prueba directa empieza yy
    Probemos que n₀ works: P n₀ → True
    replacing n₀ by a natural number
-/
-- #guard_msgs in
example (P : ℕ → Prop): ∃ n : ℕ, P n → True := by
  ayuda
  use 0
  tauto

/--
info: Ayuda
  • El objetivo starts with “P ⇒ ...”
    Luego una prueba directa empieza yy
    Supongamos hyp : P
    The name hyp can be chosen freely among available names.
-/
-- #guard_msgs in
example (P Q : Prop) (h : Q) : P → Q := by
  ayuda
  exact fun _ ↦ h

/--
info: Ayuda
  • El objetivo starts with “∀ n ≥ 0”
    Luego una prueba directa empieza yy
    Sea n ≥ 0
-/
-- #guard_msgs in
example : ∀ n ≥ 0, True := by
  ayuda
  intros
  trivial

/--
info: Ayuda
  • El objetivo starts with “∀ n : ℕ,”
    Luego una prueba directa empieza yy
    Sea n : ℕ
-/
-- #guard_msgs in
example : ∀ n : ℕ, 0 ≤ n := by
  ayuda
  exact Nat.zero_le

/--
info: Ayuda
  • El objetivo starts with “∃ n, ...”
    Luego una prueba directa empieza yy
    Probemos que n₀ works: 0 ≤ n₀
    replacing n₀ by a natural number
-/
-- #guard_msgs in
example : ∃ n : ℕ, 0 ≤ n := by
  ayuda
  use 1
  exact Nat.zero_le 1

/--
info: Ayuda
  • El objetivo starts with “∃ n ≥ 1, ...”
    Luego una prueba directa empieza yy
    Probemos que n₀ works: n₀ ≥ 1 ∧ True
    replacing n₀ by a natural number
-/
-- #guard_msgs in
example : ∃ n ≥ 1, True := by
  ayuda
  use 1

/-- info: I have nothing to say about this assumption. -/
-- #guard_msgs in
example (h : Odd 3) : True := by
  ayuda h
  trivial

/--
info: Ayuda
  • El objetivo la inclusión s ⊆ t
    Luego una prueba directa empieza yy
    Sea x ∈ s
    The name x can be chosen freely among available names.
---
info: Ayuda
  • La hipótesis h demuestra la inclusión de s in t.
    Se puede usar con:
    Por h aplicado a x_1 usando hx tenemos hx' : x_1 ∈ t
    where x_1 is a natural number yy hx proves que x_1 ∈ s
    The name hx' can be chosen freely among available names.
-/
-- #guard_msgs in
example (s t : Set ℕ) (h : s ⊆ t) : s ⊆ t := by
  ayuda
  Sea x ∈ s
  ayuda h
  exact h x_mem

/--
info: Ayuda
  • La hipótesis h pertenece a una intersección
    Se puede usar con:
    Por h tenemos (h_1 : x ∈ s) (h' : x ∈ t)
    The names h_1 yy h' can be chosen freely among available names.
-/
-- #guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∩ t) : x ∈ s := by
  ayuda h
  Por h tenemos (h_1 : x ∈ s) (h' : x ∈ t)
  exact h_1

/--
info: Ayuda
  • La hipótesis h pertenece a una intersección
    Se puede usar con:
    Por h tenemos (h_1 : x ∈ s) (h' : x ∈ t)
    The names h_1 yy h' can be chosen freely among available names.
---
info: Ayuda
  • El objetivo is prove x pertenece a la intersección de t yy otro conjunto.
    Luego una demostración empezaría con:
    Primero probemos que x ∈ t
---
info: Ayuda
  • The next step is to announce:
    Probemos ahora que x ∈ s
-/
-- #guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∩ t) : x ∈ t ∩ s := by
  ayuda h
  Por h tenemos (h_1 : x ∈ s) (h' : x ∈ t)
  ayuda
  Primero probemos que x ∈ t
  exact h'
  ayuda
  Probemos ahora que x ∈ s
  exact h_1

open Verbose.Named in
/--
info: Ayuda
  • La hipótesis h pertenece a una unión
    Se puede usar con:
    Procedemos usando h
---
info: Ayuda
  • El objetivo es demostrar que x pertenece a la unión de t yy s.
    Luego una prueba directa empieza yy
    Probemos que x ∈ t
  • o by:
    Probemos que x ∈ s
-/
-- #guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∪ t) : x ∈ t ∪ s := by
  ayuda h
  Procedemos usando h
  Supongamos hyp : x ∈ s
  ayuda
  Probemos que x ∈ s
  exact hyp
  Supongamos hyp : x ∈ t
  Probemos que x ∈ t
  exact  hyp

/--
info: Ayuda
  • El objetivo starts with “False ⇒ ...”
    Luego una prueba directa empieza yy
    Supongamos hyp : False
    The name hyp can be chosen freely among available names.
-/
-- #guard_msgs in
example : False → True := by
  ayuda
  simp

/-- info: I have nothing to say about this goal. -/
-- #guard_msgs in
example : True := by
  ayuda
  trivial

configureHelpProviders DefaultHypHelp DefaultGoalHelp helpContraposeGoal

/--
info: Ayuda
  • El objetivo starts with “False ⇒ ...”
    Luego una prueba directa empieza yy
    Supongamos hyp : False
    The name hyp can be chosen freely among available names.
  • El objetivo es una implicación.
    Se puede empezar una demostración por contraposición usando
    Contrapongamos
-/
-- #guard_msgs in
example : False → True := by
  ayuda
  Contrapongamos
  simp

/-- info: I have nothing to say about this goal. -/
-- #guard_msgs in
example : True := by
  ayuda
  trivial

configureHelpProviders DefaultHypHelp DefaultGoalHelp helpByContradictionGoal

/--
info: Ayuda
  • Se puede empezar una demostración por contradicción usando
    Supongamos for contradiction hyp : False
-/
-- #guard_msgs in
example : True := by
  ayuda
  trivial

/--
info: Ayuda
  • La hipótesis h tiene forma de “∃ x, ...”
    Se puede usar con:
    Por h tenemos x_1 tal que (hx_1 : f x_1 = y)
    The names x_1 yy hx_1 can be chosen freely among available names.
-/
-- #guard_msgs in
example {X Y} (f : X → Y) (x : X) (y : Y) (h : ∃ x, f x = y) : True := by
  ayuda h
  trivial

/--
info: Ayuda
  • La hipótesis h tiene forma de “∃ x ∈ s, ...”
    Se puede usar con:
    Por h tenemos x_1 tal que (x_1_dans : x_1 ∈ s) yy (hx_1 : f x_1 = y)
    The names x_1, x_1_dans yy hx_1 can be chosen freely among available names.
-/
-- #guard_msgs in
example {X Y} (f : X → Y) (s : Set X) (x : X) (y : Y) (h : ∃ x ∈ s, f x = y) : True := by
  ayuda h
  trivial

/--
info: Ayuda
  • El objetivo es la negación P, , es decir, P implica una contradicción
    Luego una prueba directa empieza yy
    Supongamos hyp : P
    Luego solo queda demostrar la contradicción.
-/
-- #guard_msgs in
example (P : Prop) (h : ¬ P) : ¬ P := by
  ayuda
  exact h

/--
info: Ayuda
  • El objetivo es la negación  x = y, , es decir, x = y implica una contradicción
    Luego una prueba directa empieza yy
    Supongamos hyp : x = y
    Luego solo queda demostrar la contradicción.
-/
-- #guard_msgs in
example (x y : ℕ) (h : x ≠ y) : x ≠ y := by
  ayuda
  exact h

allowProvingNegationsByContradiction

/--
info: Ayuda
  • Se puede empezar una demostración por contradicción usando
    Supongamos for contradiction hyp : P
  • El objetivo es la negación P, , es decir, P implica una contradicción
    Luego una prueba directa empieza yy
    Supongamos hyp : P
    Luego solo queda demostrar la contradicción.
-/
-- #guard_msgs in
example (P : Prop) (h : ¬ P) : ¬ P := by
  ayuda
  exact h

/--
info: Ayuda
  • Se puede empezar una demostración por contradicción usando
    Supongamos for contradiction hyp : x = y
  • El objetivo es la negación  x = y, , es decir, x = y implica una contradicción
    Luego una prueba directa empieza yy
    Supongamos hyp : x = y
    Luego solo queda demostrar la contradicción.
-/
-- #guard_msgs in
example (x y : ℕ) (h : x ≠ y) : x ≠ y := by
  ayuda
  exact h

configureHelpProviders SinceHypHelp SinceGoalHelp helpShowContrapositiveGoal
/--
info: Ayuda
  • La hipótesis h starts with “∀ n > 0, ...”
    Se puede usar con:
    Como ∀ n > 0, P n yy n₀ > 0 tenemos que P n₀
    where n₀ is a natural number yy n₀ > 0 follows immediately from an assumption.
-/
-- #guard_msgs in
example {P : ℕ → Prop} (h : ∀ n > 0, P n) : P 2 := by
  ayuda h
  apply h
  norm_num

/--
info: Ayuda
  • La hipótesis h tiene forma de “∃ n > 0, ...”
    Se puede usar con:
    Como ∃ n > 0, P n tenemos n tal que (n_pos : n > 0) yy (hn : P n)
    The names n, n_pos yy hn can be chosen freely among available names.
-/
-- #guard_msgs in
example {P : ℕ → Prop} (h : ∃ n > 0, P n) : True := by
  ayuda h
  trivial

/--
info: Ayuda
  • La hipótesis h tiene forma de “∃ ε > 0, ...”
    Se puede usar con:
    Como ∃ ε > 0, P ε tenemos ε tal que (ε_pos : ε > 0) yy (hε : P ε)
    The names ε, ε_pos yy hε can be chosen freely among available names.
-/
-- #guard_msgs in
example {P : ℝ → Prop} (h : ∃ ε > 0, P ε) : True := by
  ayuda h
  trivial

/--
info: Ayuda
  • La hipótesis h starts with “∀ n, ...”
    Se puede usar con:
    Como ∀ (n : ℕ), P n → Q n tenemos que P n₀ → Q n₀
    where n₀ is a natural number
  • If this assumption won't be used again in its general shape, one can also specialize h with
    We apply h to n₀
-/
-- #guard_msgs in
example (P Q : ℕ → Prop) (h : ∀ n, P n → Q n) (h' : P 2) : Q 2 := by
  ayuda h
  exact h 2 h'

/--
info: Ayuda
  • La hipótesis h starts with “∀ n, ...”
    Se puede usar con:
    Como ∀ (n : ℕ), P n tenemos que P n₀
    where n₀ is a natural number
  • If this assumption won't be used again in its general shape, one can also specialize h with
    We apply h to n₀
-/
-- #guard_msgs in
example (P : ℕ → Prop) (h : ∀ n, P n) : P 2 := by
  ayuda h
  exact h 2

/--
info: Ayuda
  • Assumption h es una implicación
    La conclusión de esta implicación es el objetivo actual
    Hence one can use this assumption with:
    Como P 1 → Q 2 basta probar que P 1
  • If you already have a proof of P 1 then one can use:
    Como P 1 → Q 2 yy P 1 concluimos que  Q 2
-/
-- #guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 → Q 2) (h' : P 1) : Q 2 := by
  ayuda h
  exact h h'

/--
info: Ayuda
  • Assumption h es una implicación
    The premise de esta implicación is P 1
    Si tienes una prueba de P 1
    Puedes usar esta hipótesis con:
    Como P 1 → Q 2 yy P 1 tenemos que Q 2
-/
-- #guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 → Q 2) : True := by
  ayuda h
  trivial

/--
info: Ayuda
  • La hipótesis h tiene forma de “... yy ...”
    Se puede usar con:
    Como P 1 ∧ Q 2 tenemos que P 1 yy Q 2
-/
-- #guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 ∧ Q 2) : True := by
  ayuda h
  trivial

/--
info: Ayuda
  • La hipótesis h es una equivalencia
    One can use it to replace the left-hand-side (namely ∀ n ≥ 2, P n) by the right-hand side (namely ∀ (l : ℕ), Q l) o the other way around in the goal with:
    Como (∀ n ≥ 2, P n) ↔ ∀ (l : ℕ), Q l basta probar que ?_
    replacing the question mark by the new goal.
  • One can also perform such replacements in a statement following from one of the current assumptions with
    Como (∀ n ≥ 2, P n) ↔ ∀ (l : ℕ), Q l yy ?_ tenemos que ?_
    replacing the first question mark by the fact where you want to replace yy the second one by the new obtained fact.
-/
-- #guard_msgs in
example (P Q : ℕ → Prop) (h : (∀ n ≥ 2, P n) ↔  ∀ l, Q l) : True := by
  ayuda h
  trivial

/--
info: Ayuda
  • La hipótesis h starts with “∀ x, ...”
    Se puede usar con:
    Como ∀ (x y : ℝ), x ≤ y → f x ≤ f y tenemos que ∀ (y : ℝ), x₀ ≤ y → f x₀ ≤ f y
    where x₀ is a real number
  • If this assumption won't be used again in its general shape, one can also specialize h with
    We apply h to x₀
-/
-- #guard_msgs in
example (f : ℝ → ℝ) (h : ∀ x y, x ≤ y → f x ≤ f y) (a b : ℝ) (h' : a ≤ b) : True := by
  ayuda h
  trivial

/--
info: Ayuda
  • La hipótesis h starts with “∀ x > 0, ...”
    Se puede usar con:
    Como ∀ x > 0, x = 1 → f x ≤ 0 yy x₀ > 0 tenemos que x₀ = 1 → f x₀ ≤ 0
    where x₀ is a real number yy x₀ > 0 follows immediately from an assumption.
-/
-- #guard_msgs in
example (f : ℝ → ℝ) (h : ∀ x > 0, x = 1 → f x ≤ 0) (a b : ℝ) (h' : a ≤ b) : True := by
  ayuda h
  trivial

/--
info: Ayuda
  • Assumption h es una implicación
    The premise de esta implicación is l - n = 0
    Si tienes una prueba de l - n = 0
    Puedes usar esta hipótesis con:
    Como l - n = 0 → P l k yy l - n = 0 tenemos que P l k
-/
-- #guard_msgs in
example (P : ℕ → ℕ → Prop) (k l n : ℕ) (h : l - n = 0 → P l k) : True := by
  ayuda h
  trivial

/--
info: Ayuda
  • La hipótesis h starts with “∀ k ≥ 2, ∃ n ≥ 3, ...”
    Se puede usar con:
    Como ∀ k ≥ 2, ∃ n ≥ 3, ∀ (l : ℕ), l - n = 0 → P l k yy k₀ ≥ 2 tenemos
        n tal que n ≥ 3 yy ∀ (l : ℕ), l - n = 0 → P l k₀
    where k₀ is a natural number yy the relation k₀ ≥ 2 must follow immediately from an assumption.
    The name n can be chosen freely among available names.
-/
-- #guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  ayuda h
  trivial

-- FIXME: completely broken case
/--
info: Ayuda
  • La hipótesis h starts with “∀ k n, k ≥ n ⇒ ...”
    Se puede usar con:
    Como ∀ (k n : ℕ), n ≥ 3 → ∀ (l : ℕ), l - n = 0 → P l k yy n ≥ 3 tenemos que
        ∀ (l : ℕ), l - n₀ = 0 → P l k₀
    where k₀ yy n₀ are some natural numbers yy k₀ ≥ n₀ follows immediately from an assumption.
-/
-- #guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k, ∀ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  ayuda h
  trivial

-- FIXME: completely broken case
/--
info: Ayuda
  • La hipótesis h starts with “∀ k n, k ≤ n ⇒ ...”
    Se puede usar con:
    Como ∀ (k n : ℕ), n ≤ k → f n ≤ f k yy n ≤ k tenemos que f n₀ ≤ f k₀
    where k₀ yy n₀ are some natural numbers yy k₀ ≤ n₀ follows immediately from an assumption.
-/
-- #guard_msgs in
example (f : ℕ → ℕ) (h : ∀ k n, n ≤ k → f n ≤ f k) : True := by
  ayuda h
  trivial

-- FIXME: in hn_1, n is not replaced by n_1. This es una issue in
-- helpSinceForAllRelExistsRelSuggestion (o rather the function calling it)
/--
info: Ayuda
  • La hipótesis h starts with “∀ k ≥ 2, ∃ n_1 ≥ 3, ...”
    Se puede usar con:
    Como ∀ k ≥ 2, ∃ n ≥ 3, ∀ (l : ℕ), l - n = 0 → P l k yy k₀ ≥ 2 tenemos
        n_1 tal que n_1 ≥ 3 yy ∀ (l : ℕ), l - n = 0 → P l k₀
    where k₀ is a natural number yy the relation k₀ ≥ 2 must follow immediately from an assumption.
    The name n_1 can be chosen freely among available names.
-/
-- #guard_msgs in
example (P : ℕ → ℕ → Prop) (n : ℕ) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  ayuda h
  Por h aplicado a 2 usando le_rfl tenemos n' tal que (n_sup : n' ≥ 3) yy (hn : ∀ (l : ℕ), l - n' = 0 → P l 2)
  trivial

/--
info: Ayuda
  • La hipótesis h tiene forma de “∃ n ≥ 5, ...”
    Se puede usar con:
    Como ∃ n ≥ 5, P n tenemos n tal que (n_sup : n ≥ 5) yy (hn : P n)
    The names n, n_sup yy hn can be chosen freely among available names.
-/
-- #guard_msgs in
example (P : ℕ → Prop) (h : ∃ n ≥ 5, P n) : True := by
  ayuda h
  trivial

/--
info: Ayuda
  • La hipótesis h starts with “∀ k ≥ 2, ∃ n ≥ 3, ...”
    Se puede usar con:
    Como ∀ k ≥ 2, ∃ n ≥ 3, P n k yy k₀ ≥ 2 tenemos n tal que n ≥ 3 yy P n k₀
    where k₀ is a natural number yy the relation k₀ ≥ 2 must follow immediately from an assumption.
    The name n can be chosen freely among available names.
-/
-- #guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, P n k) : True := by
  ayuda h
  trivial

/--
info: Ayuda
  • La hipótesis h tiene forma de “∃ n, ...”
    Se puede usar con:
    Como ∃ n, P n tenemos n tal que P n
    The name n can be chosen freely among available names.
-/
-- #guard_msgs in
example (P : ℕ → Prop) (h : ∃ n : ℕ, P n) : True := by
  ayuda h
  trivial

/--
info: Ayuda
  • La hipótesis h starts with “∀ k, ∃ n, ...”
    Se puede usar con:
    Como ∀ (k : ℕ), ∃ n, P n k tenemos n tal que P n k₀
    where k₀ is a natural number
    The name n can be chosen freely among available names.
-/
-- #guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k, ∃ n : ℕ, P n k) : True := by
  ayuda h
  trivial

/--
info: Ayuda
  • La hipótesis h tiene forma de “... o ...”
    Se puede usar con:
    Decidimos en función de si P 1 o Q 2
-/
-- #guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 ∨ Q 2) : True := by
  ayuda h
  trivial

/--
info: Ayuda
  • La hipótesis h pertenece a una intersección
    Se puede usar con:
    Como x ∈ s ∩ t tenemos que x ∈ s yy x ∈ t
-/
-- #guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∩ t) : x ∈ s := by
  ayuda h
  Por h tenemos (h_1 : x ∈ s) (h' : x ∈ t)
  exact h_1

/--
info: Ayuda
  • La hipótesis h pertenece a una intersección
    Se puede usar con:
    Como x ∈ s ∩ t tenemos que x ∈ s yy x ∈ t
---
info: Ayuda
  • El objetivo is prove x pertenece a la intersección de t yy otro conjunto.
    Luego una demostración empezaría con:
    Primero probemos que x ∈ t
---
info: Ayuda
  • The next step is to announce:
    Probemos ahora que x ∈ s
-/
-- #guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∩ t) : x ∈ t ∩ s := by
  ayuda h
  Por h tenemos (h_1 : x ∈ s) (h' : x ∈ t)
  ayuda
  Primero probemos que x ∈ t
  exact h'
  ayuda
  Probemos ahora que x ∈ s
  exact h_1

open Verbose.Named in
/--
info: Ayuda
  • La hipótesis h pertenece a una unión
    Se puede usar con:
    Decidimos en función de si x ∈ s o x ∈ t
---
info: Ayuda
  • El objetivo es demostrar que x pertenece a la unión de t yy s.
    Luego una prueba directa empieza yy
    Probemos que x ∈ t
  • o by:
    Probemos que x ∈ s
-/
-- #guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∪ t) : x ∈ t ∪ s := by
  ayuda h
  Procedemos usando h
  Supongamos hyp : x ∈ s
  ayuda
  Probemos que x ∈ s
  exact hyp
  Supongamos hyp : x ∈ t
  Probemos que x ∈ t
  exact  hyp

/--
info: Ayuda
  • La hipótesis h es una desigualdad
    El objetivo actual se deriva inmediate de esta.
    Se puede usar con:
    Como ε > 0 concluimos que  ε / 2 > 0
-/
-- #guard_msgs in
example (ε : ℝ) (h : ε > 0) : ε/2 > 0 := by
  ayuda h
  linarith

/--
info: Ayuda
  • El objetivo es una desigualdad
    Puede calcularse usando
    Calc
        ε / 2 > 0 since?
    El último cálculo no es necesariamente una igualdad, sino una desigualdad.
    De la misma forma, la primera línea puede ser una igualdad. Al final los símbolos de relación
    deben componerse para obtener  > ⏎
  • Si esta desigualdad se sigue directamente de una hipótesis, se puede usar:
    Como ?_ concluimos que  ε / 2 > 0
    replacing the question mark by the statement of the assumption.
-/
-- #guard_msgs in
example (ε : ℝ) (h : ε > 0) : ε/2 > 0 := by
  ayuda
  Como ε > 0 concluimos que  ε / 2 > 0

/--
info: Ayuda
  • La hipótesis h es una equivalencia
    One can use it to replace the left-hand-side (namely P) by the right-hand side (namely Q) o the other way around in the goal with:
    Como P ↔ Q basta probar que ?_
    replacing the question mark by the new goal.
  • One can also perform such replacements in a statement following from one of the current assumptions with
    Como P ↔ Q yy ?_ tenemos que ?_
    replacing the first question mark by the fact where you want to replace yy the second one by the new obtained fact.
-/
-- #guard_msgs in
example (P Q : Prop) (h : P ↔ Q) (h' : P) : Q := by
  ayuda h
  Como P ↔ Q basta probar que P
  exact h'

/--
info: Ayuda
  • La hipótesis h demuestra la inclusión de A in B.
    Se puede usar con:
    Como A ⊆ B yy x ∈ A tenemos que x ∈ B
    where x is a natural number
-/
-- #guard_msgs in
example (A B : Set ℕ) (h : A ⊆ B) : True := by
  ayuda h
  trivial

/--
info: Ayuda
  • ¡Esta hipótesis es una contradicción!
    One can deduce the goal from it with:
    Como False concluimos que  0 = 1
-/
-- #guard_msgs in
example (h : False) : 0 = 1 := by
  ayuda h
  Como False concluimos que  0 = 1

/--
info: Ayuda
  • El objetivo es demostrar que hay una contradicción
    One can apply an assumption which is a negation
    namely, by definition, with shape P → false.
    También puedes combinar dos hipótesis que claramente se contradigan usando:
    Como ?_ yy ?_ concluimos que  False
    sustituyendo los signos de interrogación por esos dos hechos que se deducen directamente de las premisas.
  • También se puede invocar un hecho claramente falso (como «0 = 1») que se deduce directamente de una suposición.
    Como ?_ concluimos que  False
    reemplazando el signo de interrogación por cualquier hecho claramente falso.
-/
-- #guard_msgs in
example (h : 0 = 1) : False := by
  ayuda
  Como 0 = 1 concluimos que  False

/--
info: Ayuda
  • El objetivo es una desigualdad
    Puede calcularse usando
    Calc
        a ≤ c since?
    El último cálculo no es necesariamente una igualdad, sino una desigualdad.
    De la misma forma, la primera línea puede ser una igualdad. Al final los símbolos de relación
    deben componerse para obtener  ≤ ⏎
  • Si esta desigualdad se sigue directamente de una hipótesis, se puede usar:
    Como ?_ concluimos que  a ≤ c
    replacing the question mark by the statement of the assumption.
-/
-- #guard_msgs in
example (a b c : ℤ) (h : a ≤ b) (h' : b ≤ c) : a ≤ c := by
  ayuda
  exact le_trans h h'

/--
info: Ayuda
  • El objetivo starts with “False ⇒ ...”
    Luego una prueba directa empieza yy
    Supongamos que False
  • El objetivo es una implicación.
    Se puede empezar una demostración por contraposición usando
    Probemos la contraposición: ¬True → ¬False
-/
-- #guard_msgs in
example : False → True := by
  ayuda
  Probemos el contrapositivo: ¬True → ¬False
  simp
