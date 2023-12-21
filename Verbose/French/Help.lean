import Verbose.Tactics.Help
import Verbose.French.Tactics

open Lean Meta Elab Tactic Verbose

def describe {α :Type} [ToString α] (t : α) : String :=
match toString t with
| "ℝ" => "un nombre réel"
| "ℕ" => "un nombre entier naturel"
| "ℤ" => "un nombre entier relatif"
| t => "une expression de type " ++ t

def describe_pl {α :Type} [ToString α] (t : α) : String :=
match toString t with
| "ℝ" => "des nombres réels"
| "ℕ" => "des nombres entiers naturels"
| "ℤ" => "des nombres entiers relatifs"
| t => "des expressions de type " ++ t

def libre (s: String) : String := s!"Le nom {s} peut être choisi librement parmi les noms disponibles."

def libres (ls : List String) : String :=
"Les noms " ++ String.intercalate ", " ls ++ " peuvent être choisis librement parmi les noms disponibles."

def mkFixDecl (var : Name) (typ : Expr) : MetaM (TSyntax `fixDecl) := do
  let i := mkIdent var
  let typS ← Lean.PrettyPrinter.delab typ
  `(fixDecl|$i:ident : $typS)

def helpAtHyp (goal : MVarId) (hyp : Name) : SuggestionM Unit :=
  goal.withContext do
  let decl := ← getLocalDeclFromUserName hyp
  let hypId := mkIdent hyp
  if ← decl.type.closesGoal goal then
    pushCom "Cette hypothèse est exactement ce qu'il faut démontrer"
    pushCom "On peut l'utiliser avec :"
    pushTac `(tactic|On conclut par $hypId:ident)
    return
  let hypType ← instantiateMVars decl.type
  if let some expandedHypType ← hypType.expandHeadFun then
    let expandedHypTypeS ← PrettyPrinter.delab expandedHypType
    pushCom "Cette hypothèse commence par l'application d'une définition."
    pushCom "On peut l'expliciter avec :"
    pushTac `(tactic|On reformule $hypId:ident en $expandedHypTypeS)
    flush
  parse (← whnf hypType) fun m ↦ match m with
    | .forall_rel _ var_name typ rel rel_rhs propo => do
        let py ← ppExpr rel_rhs
        let t ← ppExpr typ
        let n := toString var_name
        let n₀ := n ++ "₀"
        let nn₀ ← goal.getUnusedUserName (Name.mkSimple n₀)
        let n₀T := mkIdent nn₀
        let hn₀N ← goal.getUnusedUserName ("h" ++ n₀ : String)
        let hn₀T := mkIdent hn₀N
        withRenamedFVar var_name nn₀ do
        match propo with
        | .exist_rel _e' var_name' _typ' rel' rel_rhs' propo' => do
          let var_name' := ← goal.getUnusedUserName var_name'
          let ineqIdent := mkIdent s!"{var_name'}{symb_to_hyp rel' rel_rhs'}"
          let ineqS ← mkRelStx var_name' rel' rel_rhs'
          let hn'S := mkIdent s!"h{var_name'}"
          let p'S ← propo'.delab
          pushCom "L'hypothèse {hyp} commence par « ∀ {n}{rel}{py}, ∃ {var_name'}{rel'}{← ppExpr rel_rhs'}, ... »"
          pushCom "On peut l'utiliser avec :"
          pushTac `(tactic|Par $hypId:term appliqué à [$n₀T, $hn₀T] on obtient $(mkIdent var_name'):ident tel que ($ineqIdent : $ineqS) ($hn'S : $p'S))
          pushCom "où {n₀} est {describe t} et {hn₀N} est une démonstration du fait que {nn₀}{rel}{py}."
          pushComment <| libres [s!"{var_name'}", s!"{var_name'}{symb_to_hyp rel' rel_rhs'}", s!"h{var_name'}"]
        | .exist_simple _e' var_name' _typ' propo' => do
          let n' := toString var_name'
          let var_name' := ← goal.getUnusedUserName var_name'
          let hn'S := mkIdent s!"h{var_name'}"
          let p'S ← propo'.delab
          pushCom "L'hypothèse {hyp} commence par « ∀ {n}{rel}{py}, ∃ {n'}, ... »"
          pushCom "On peut l'utiliser avec :"
          pushTac `(tactic|Par $hypId:term appliqué à [$n₀T, $hn₀T] on obtient $(mkIdent var_name'):ident tel que ($hn'S : $p'S))
          pushCom "où {n₀} est {describe t} et h{n₀} est une démonstration du fait que {n₀}{rel}{py}"
          pushComment <| libres [n', s!"h{n'}"]
        | _ => do
          let pS ← propo.delab
          pushCom "L'hypothèse {hyp} commence par « ∀ {var_name}{rel}{py}, »"
          pushCom "On peut l'utiliser avec :"
          pushTac `(tactic|Par $hypId:term appliqué à [$n₀T, $hn₀T] on obtient ($hn₀T : $pS))
          pushCom "où {n₀} est {describe t} et h{n₀} est une démonstration du fait que {n₀}{rel}{py}"
          pushComment <| libre "h"
    | .forall_simple _ var_name typ propo => do
        let t ← ppExpr typ
        let n := toString var_name
        let n₀ := n ++ "₀"
        let nn₀ ← goal.getUnusedUserName (Name.mkSimple n₀)
        let n₀T := mkIdent nn₀
        let hn₀N ← goal.getUnusedUserName ("h" ++ n₀ : String)
        let hn₀T := mkIdent hn₀N
        withRenamedFVar var_name nn₀ do
        match propo with
        | .exist_rel _e' var_name' _typ' rel' rel_rhs' propo' => do
          let var_name' := ← goal.getUnusedUserName var_name'
          let ineqIdent := mkIdent s!"{var_name'}{symb_to_hyp rel' rel_rhs'}"
          let ineqS ← mkRelStx var_name' rel' rel_rhs'
          let hn'S := mkIdent s!"h{var_name'}"
          let p'S ← propo'.delab
          pushCom "L'hypothèse {hyp} commence par « ∀ {n}, ∃ {var_name'}{rel'}{← ppExpr rel_rhs'}, ... »"
          pushCom "On peut l'utiliser avec :"
          pushTac `(tactic|Par $hypId:term appliqué à $n₀T on obtient $(mkIdent var_name'):ident tel que ($ineqIdent : $ineqS) ($hn'S : $p'S))
          pushCom "où {n₀} est {describe t}"
          pushComment <| libres [s!"{var_name'}", s!"{var_name'}{symb_to_hyp rel' rel_rhs'}", s!"h{var_name'}"]
        | .exist_simple _e' var_name' _typ' propo' => do
          let var_name' := ← goal.getUnusedUserName var_name'
          let hn'S := mkIdent s!"h{var_name'}"
          let p'S ← propo'.delab
          pushCom "L'hypothèse {hyp} commence par « ∀ {n}, ∃ {var_name'}, ... »"
          pushCom "On peut l'utiliser avec :"
          pushTac `(tactic|Par $hypId:term appliqué à $n₀T on obtient $(mkIdent var_name'):ident tel que ($hn'S : $p'S))
          pushCom "où {n₀} est {describe t}"
          pushComment <| libres [toString var_name', s!"h{var_name'}"]
        | .forall_rel _e' var_name' _typ' rel' _rel_rhs' propo' => do
          let n' := toString var_name'
          let var_name'₀ := ← goal.getUnusedUserName (Name.mkSimple ((toString var_name') ++ "₀"))
          withRenamedFVar var_name' var_name'₀ do
          let n'₀T := mkIdent var_name'₀
          let H := ← goal.getUnusedUserName `H
          let HT := mkIdent H
          let h := ← goal.getUnusedUserName `h
          let hT := mkIdent h
          let rel := n ++ rel' ++ n'
          let rel₀ := s!"{nn₀}{rel'}{var_name'₀}"
          let p'S ← propo'.delab
          pushCom "L'hypothèse {hyp} commence par « ∀ {n} {n'}, {rel} → ... "
          pushCom "On peut l'utiliser avec :"
          pushTac `(tactic|Par $hypId:term appliqué à [$n₀T, $n'₀T, $HT] on obtient ($hT : $p'S))
          pushCom "où {nn₀} et {var_name'₀} sont {describe_pl t} et {H} est une démonstration de {rel₀}"
          pushComment <| libre (toString h)
        | _ => do
          let pS ← propo.delab
          pushCom "L'hypothèse {hyp} commence par « ∀ {n}, »"
          pushCom "On peut l'utiliser avec :"
          pushTac `(tactic|Par $hypId:term appliqué à $n₀T on obtient ($hn₀T : $pS))
          pushCom "où {n₀} est {describe t}"
          pushComment <| libre "h" ++ ""
          flush
          pushCom "Si cette hypothèse ne servira plus dans sa forme générale, on peut aussi spécialiser {hyp} par"
          pushTac `(tactic|On applique $hypId:ident à $n₀T)
          -- **TODO** cleanup this mess
          let msgM : MetaM (Option <| TSyntax `tactic) := withoutModifyingState do
              (do
              let _ ← goal.apply decl.toExpr
              let prf ← instantiateMVars (mkMVar goal)
              let prfS ← prf.toMaybeAppliedFR
              if !prf.hasMVar then
                some (← `(tactic|On conclut par $prfS))
              else
                none)
            <|>
              pure none
          let msg ← msgM
          if let some msg := msg then
            let but ← ppExpr (← goal.getType)
            flush
            pushCom "\nComme le but est {but}, on peut utiliser :"
            pushTac (do return msg)
    | .exist_rel _ var_name _typ rel rel_rhs propo => do
      let y ← ppExpr rel_rhs
      let pS ← propo.delab
      let name ← goal.getUnusedUserName var_name
      let nameS := mkIdent name
      let hS := mkIdent s!"h{name}"
      let ineqName := Name.mkSimple s!"{name}{symb_to_hyp rel rel_rhs}"
      let ineqIdent := mkIdent ineqName
      let ineqS ← mkRelStx name rel rel_rhs
      pushCom "L'hypothèse {hyp} est de la forme « ∃ {var_name}{rel}{y}, ... »"
      pushCom "On peut l'utiliser avec :"
      pushTac `(tactic|Par $hypId:term on obtient $nameS:ident tel que ($ineqIdent : $ineqS) ($hS : $pS))
      pushComment <| libres [toString name, s!"{name}{symb_to_hyp rel rel_rhs}", s!"h{name}"]
    | .exist_simple _ var_name _typ propo => do
      let pS ← propo.delab
      let name ← goal.getUnusedUserName var_name
      let nameS := mkIdent name
      let hS := mkIdent s!"h{name}"
      pushCom "L'hypothèse {hyp} est de la forme « ∃ {var_name}, ... »"
      pushCom "On peut l'utiliser avec :"
      pushTac `(tactic|Par $hypId:term on obtient $nameS:ident tel que ($hS : $pS))
      pushComment <| libres [toString name, s!"h{name}"]
    | .conjunction _ propo propo' => do
      let h₁N ← goal.getUnusedUserName `h
      let h₁I := mkIdent h₁N
      let h₂N ← goal.getUnusedUserName `h
      let h₂I := mkIdent h₂N
      let p₁S ← propo.delab
      let p₂S ← propo'.delab
      pushCom "L'hypothèse {hyp} est de la forme « ... et ... »"
      pushCom "On peut l'utiliser avec :"
      pushTac `(tactic|Par $hypId:term on obtient ($h₁I : $p₁S) ($h₂I : $p₂S))
      pushComment <| libres [s!"h₁N", s!"h₂N"]
    | .disjunction _ _propo _propo' => do
      pushCom "L'hypothèse {hyp} est de la forme « ... ou ... »"
      pushCom "On peut l'utiliser avec :"
      pushTac `(tactic|On discute en utilisant $hypId:term)
    | .impl _ _le re lhs rhs => do
      let HN ← goal.getUnusedUserName `H
      let HI := mkIdent HN
      let H'N ← goal.getUnusedUserName `H'
      let H'I := mkIdent H'N
      let l ← lhs.delab
      let lStr ← PrettyPrinter.ppTerm l
      let r ← rhs.delab
      pushCom "L'hypothèse {hyp} est une implication"
      if ← re.closesGoal goal then do
        pushCom "La conclusion de cette implication est le but courant"
        pushCom "On peut donc utiliser cette hypothèse avec :"
        pushTac `(tactic| Par $hypId:term il suffit de montrer $l)
        flush
        pushCom "Si vous disposez déjà d'une preuve {HN} de {lStr} alors on peut utiliser :"
        pushTac `(tactic|On conclut par $hypId:term appliqué à $HI)
      else do
        pushCom "La prémisse de cette implication est {lStr}"
        pushCom "Si vous avez une démonstration {HN} de {lStr}"
        pushCom "vous pouvez donc utiliser cette hypothèse avec :"
        pushTac `(tactic|Par $hypId:term appliqué à $HI:term on obtient $H'I:ident : $r:term)
        pushComment <| libre s!"{H'N}"
    | .iff _ _le _re lhs rhs => do
      let l ← lhs.delab
      let lStr ← PrettyPrinter.ppTerm l
      let r ← rhs.delab
      let rStr ← PrettyPrinter.ppTerm r
      let hyp'N ← goal.getUnusedUserName `hyp
      let hyp'I := mkIdent hyp'N
      pushCom "L'hypothèse {hyp} est une équivalence"
      pushCom "On peut s'en servir pour remplacer le membre de gauche (c'est à dire {lStr}) par le membre de droite  (c'est à dire {rStr}) dans le but par :"
      pushTac `(tactic|On réécrit via $hypId:term)
      flush
      pushCom "On peut s'en servir pour remplacer le membre de droite dans par le membre de gauche dans le but par :"
      pushTac `(tactic|On réécrit via ← $hypId)
      flush
      pushCom "On peut aussi effectuer de tels remplacements dans une hypothèse {hyp'N} par"
      pushTac `(tactic|On réécrit via $hypId:term dans $hyp'I:ident)
      flush
      pushCom "ou"
      pushTac `(tactic|On réécrit via ← $hypId:term dans $hyp'I:ident)
    | .equal _ le re => do
      let l ← ppExpr le
      let r ← ppExpr re
      let hyp'N ← goal.getUnusedUserName `hyp
      let hyp'I := mkIdent hyp'N
      pushCom "L'hypothèse {hyp} est une égalité"
      if ← decl.toExpr.linarithClosesGoal goal then
        pushComment <| s!"Le but courant en découle immédiatement"
        pushComment   "On peut l'utiliser avec :"
        pushTac `(tactic|On conclut par $hypId:ident)
      else do
        pushCom "On peut s'en servir pour remplacer le membre de gauche (c'est à dire {l}) par le membre de droite  (c'est à dire {r}) dans le but par :"
        pushTac `(tactic|On réécrit via $hypId:ident)
        flush
        pushCom "On peut s'en servir pour remplacer le membre de droite dans par le membre de gauche dans le but par :"
        pushTac `(tactic|On réécrit via ← $hypId:ident)
        flush
        pushCom "On peut aussi effectuer de tels remplacements dans une hypothèse {hyp'N} par"
        pushTac `(tactic|On réécrit via $hypId:ident dans $hyp'I:ident)
        flush
        pushCom "ou"
        pushTac `(tactic|On réécrit via ← $hypId:ident dans $hyp'I:ident)
        flush
        pushCom "On peut aussi s'en servir comme étape dans un calcul, ou bien combinée linéairement à d'autres par :"
        pushTac `(tactic| On combine [$hypId:term, ?_])
        pushCom "en remplaçant le point d'interrogation par un ou plusieurs termes prouvant des égalités."
    | .ineq _ _le _rel _re => do
      pushCom "L'hypothèse {hyp} est une inégalité"
      if ← decl.toExpr.linarithClosesGoal goal then
          flush
          pushCom "Le but courant en découle immédiatement"
          pushCom "On peut l'utiliser avec :"
          pushTac `(tactic|On conclut par $hypId:ident)
      else do
          flush
          pushCom "On peut s'en servir comme étape dans un calcul, ou bien combinée linéairement à d'autres par :"
          pushTac `(tactic| On combine [$hypId:term, ?_])
          pushCom "en remplaçant le point d'interrogation par un ou plusieurs termes prouvant des égalités ou inégalités."
    | .mem _ _elem _set => do
      pushCom "L'hypothèse {hyp} est une appartenance"
    | .prop (.const `False _) => do
        pushComment <| "Cette hypothèse est une contradiction."
        pushCom "On peut en déduire tout ce qu'on veut par :"
        pushTac `(tactic|(Montrons une contradiction
                          On conclut par $hypId:ident))
    | .prop _ => do
        pushCom "Je n'ai rien à déclarer à propos de cette hypothèse."
    | .data e => do
        let t ← toString <$> ppExpr e
        pushComment <| s!"L'objet {hyp}" ++ match t with
          | "ℝ" => " est un nombre réel fixé."
          | "ℕ" => " est un nombre entier naturel fixé."
          | "ℤ" => " est un nombre entier relatif fixé."
          | s => " : " ++ s ++ " est fixé."

def helpAtGoal (goal : MVarId) : SuggestionM Unit :=
  goal.withContext do
  let goalType ← instantiateMVars (← goal.getType)
  if let some expandedGoalType ← goalType.expandHeadFun then
    let expandedGoalTypeS ← PrettyPrinter.delab expandedGoalType
    pushCom "Le but commence par l'application d'une définition."
    pushCom "On peut l'expliciter avec :"
    pushTac `(tactic|Montrons que $expandedGoalTypeS)
    flush
  parse (← whnf goalType) fun g ↦ match g with
    | .forall_rel _e var_name _typ rel rel_rhs _propo => do
        let py ← ppExpr rel_rhs
        let n ← goal.getUnusedUserName var_name
        let ineqS ← mkFixDeclIneq n rel rel_rhs
        let commun := s!"{var_name}{rel}{py}"
        pushCom "Le but commence par « ∀ {commun} »"
        pushCom "Une démonstration directe commence donc par :"
        pushTac `(tactic|Soit $ineqS)
    | .forall_simple _e var_name typ _propo => do
        let t ← ppExpr typ
        let n ← goal.getUnusedUserName var_name
        let declS ← mkFixDecl n typ
        pushCom "Le but commence par « ∀ {var_name} : {t}, »"
        pushCom "Une démonstration directe commence donc par :"
        pushTac `(tactic|Soit $declS)
    | .exist_rel _e var_name typ rel rel_rhs propo => do
        let n := toString var_name
        let n₀ := n ++ "₀"
        let nn₀ ← goal.getUnusedUserName (Name.mkSimple n₀)
        let n₀S := mkIdent nn₀
        withRenamedFVar var_name nn₀ do
        let ineqS ← mkRelStx nn₀ rel rel_rhs
        let tgtS ← propo.delab
        let fullTgtS ← `($ineqS ∧ $tgtS)
        let t ← ppExpr typ
        pushCom "Le but est de la forme « ∃ {n}{rel}{← ppExpr rel_rhs}, ... »"
        pushCom "Une démonstration directe commence donc par :"
        pushTac `(tactic|Montrons que $n₀S convient : $fullTgtS)
        pushCom "en remplaçant {n₀} par {describe t}"
    | .exist_simple _e var_name typ propo => do
        let n := toString var_name
        let n₀ := n ++ "₀"
        let nn₀ ← goal.getUnusedUserName (Name.mkSimple n₀)
        let n₀S := mkIdent nn₀
        withRenamedFVar var_name nn₀ do
        let tgt ← propo.delab
        let t ← ppExpr typ
        pushCom "Le but est de la forme « ∃ {n}, ... »"
        pushCom "Une démonstration directe commence donc par :"
        pushTac `(tactic|Montrons que $n₀S convient : $tgt)
        pushCom "en remplaçant {n₀} par {describe t}"
    | .conjunction _e propo propo' => do
        let pS ← propo.delab
        let p ← PrettyPrinter.ppTerm pS
        let p'S ← propo'.delab
        let p' ← PrettyPrinter.ppTerm p'S
        pushCom "Le but est de la forme « ... et ... »"
        pushCom "Une démonstration directe commence donc par :"
        pushTac `(tactic|Montrons d'abord que $pS)
        pushCom "Une fois cette première démonstration achevée, il restera à montrer que {p'}"
        flush
        pushCom "On peut aussi commencer par"
        pushTac `(tactic|Montrons d'abord que $p'S)
        pushCom "puis, une fois cette première démonstration achevée, il restera à montrer que {p}"
    | .disjunction _e propo propo' => do
        let pS ← propo.delab
        let p'S ← propo'.delab
        pushCom "Le but est de la forme « ... ou ... »"
        pushCom "Une démonstration directe commence donc par annoncer quelle alternative va être démontrée :"
        pushTac `(tactic|Montrons que $pS)
        flush
        pushCom "ou bien :"
        pushTac `(tactic|Montrons que $p'S)
    | .impl _e le _re lhs _rhs => do
        let l ← ppExpr le
        let leStx ← lhs.delab
        let Hyp := mkIdent (← goal.getUnusedUserName `hyp)
        pushCom "Le but est une implication « {l} → ... »"
        pushCom "Une démonstration directe commence donc par :"
        pushTac `(tactic| Supposons $Hyp:ident : $leStx)
        pushCom "où hyp est un nom disponible au choix."
    | .iff _e le re lhs rhs => do
        let l ← ppExpr le
        let lS ← lhs.delab
        let r ← ppExpr re
        let rS ← rhs.delab
        pushCom "Le but est une équivalence. On peut annoncer la démonstration de l'implication de la gauche vers la droite par :"
        pushTac `(tactic|Montrons que $lS → $rS)
        pushCom "Une fois cette première démonstration achevée, il restera à montrer que {r} → {l}"
        flush
        pushCom "On peut aussi commencer par"
        pushTac `(tactic|Montrons que $rS → $lS)
        pushCom "puis, une fois cette première démonstration achevée, il restera à montrer que {l} → {r}"
    | .equal _e le re => do
        let l ← ppExpr le
        let r ← ppExpr re
        -- **FIXME** this discussion isn't easy to do using tactics.
        pushCom "Le but est une égalité"
        pushCom "On peut la démontrer par réécriture avec la commande `On réécrit via`"
        pushCom "ou bien commencer un calcul par"
        pushCom "  calc {l} = sorry := by sorry"
        pushCom "  ... = {r} := by sorry"
        pushCom "On peut bien sûr utiliser plus de lignes intermédiaires."
        pushCom "On peut aussi tenter des combinaisons linéaires d'hypothèses hyp₁ hyp₂... avec"
        pushCom "  On combine [hyp₁, hyp₂]"
    | .ineq _e le rel re => do
        let l ← ppExpr le
        let r ← ppExpr re
        -- **FIXME** this discussion isn't easy to do using tactics.
        pushCom "Le but est une inégalité"
        pushCom "On peut commencer un calcul par"
        pushCom "  calc {l}{rel}sorry := by sorry "
        pushCom "  ... = {r} := by sorry "
        pushCom "On peut bien sûr utiliser plus de lignes intermédiaires."
        pushCom "La dernière ligne du calcul n'est pas forcément une égalité, cela peut être une inégalité."
        pushCom "De même la première ligne peut être une égalité. Au total les symboles de relations"
        pushCom "doivent s'enchaîner pour donner {rel}"
        pushCom "On peut aussi tenter des combinaisons linéaires d'hypothèses hyp₁ hyp₂... avec"
        pushCom "  On combine [hyp₁, hyp₂]"
    | .prop (.const `False _) => do
        pushCom "Le but est de montrer une contradiction."
        pushCom "On peut par exemple appliquer une hypothèse qui est une négation"
        pushCom "c'est à dire, par définition, de la forme P → false."
    | .prop _ | .mem _ _ _ | .data _ => pushCom "Pas d'idée"

open Lean.Parser.Tactic in
elab "aide" h:(colGt ident)? : tactic => do
match h with
| some h => do
        let (s, msg) ← gatherSuggestions (helpAtHyp (← getMainGoal) h.getId)
        if s.isEmpty then
          logInfo (msg.getD "Pas de suggestion")
        else
          Std.Tactic.TryThis.addSuggestions (← getRef) s (header := "Aide")
| none => do
   dbg_trace ← (← getMainGoal).getType
   let (s, msg) ← gatherSuggestions (helpAtGoal (← getMainGoal))
   if s.isEmpty then
          logInfo (msg.getD "Pas de suggestion")
    else
      Std.Tactic.TryThis.addSuggestions (← getRef) s (header := "Aide")

set_option linter.unusedVariables false

example {P : ℕ → Prop} (h : ∀ n > 0, P n) : P 2 := by
  aide h
  apply h
  norm_num

example {P : ℕ → Prop} (h : ∃ n > 0, P n) : True := by
  aide h
  trivial

example {P : ℝ → Prop} (h : ∃ ε > 0, P ε) : True := by
  aide h
  trivial

example (P Q : ℕ → Prop) (h : ∀ n, P n → Q n) (h' : P 2) : Q 2 := by
  aide h
  exact h 2 h'

example (P : ℕ → Prop) (h : ∀ n, P n) : P 2 := by
  aide h
  exact h 2

example (P Q : ℕ → Prop) (h : P 1 → Q 2) (h' : P 1) : Q 2 := by
  aide h
  exact h h'

example (P Q : ℕ → Prop) (h : P 1 → Q 2) : True := by
  aide h
  trivial

example (P Q : ℕ → Prop) (h : P 1 ∧ Q 2) : True := by
  aide h
  trivial

example (P Q : ℕ → Prop) (h : (∀ n ≥ 2, P n) ↔  ∀ l, Q l) : True := by
  aide h
  trivial

example : True ∧ 1 = 1 := by
  aide
  exact ⟨trivial, rfl⟩

example (P Q : ℕ → Prop) (h : P 1 ∨ Q 2) : True := by
  aide h
  trivial

example : True ∨ False := by
  aide
  left
  trivial

example (P : Prop) (h : P) : True := by
  aide h
  trivial

example (h : False) : 0 = 1 := by
  aide h
  trivial


example (P : ℕ → ℕ → Prop) (k l n : ℕ) (h : l - n = 0 → P l k) : True := by
  aide h
  trivial

example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  aide h
  Par h appliqué à [2, le_rfl] on obtient n tel que (n_sup : n ≥ 3) (hn : ∀ (l : ℕ), l - n = 0 → P l 2)
  trivial

example (P : ℕ → ℕ → Prop) (h : ∀ k, ∀ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  aide h
  trivial


example (P : ℕ → ℕ → Prop) (n : ℕ) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  aide h
  Par h appliqué à [2, le_rfl] on obtient n' tel que (n_sup : n' ≥ 3) (hn : ∀ (l : ℕ), l - n' = 0 → P l 2)
  trivial

example (P : ℕ → Prop) (h : ∃ n ≥ 5, P n) : True := by
  aide h
  trivial


example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, P n k) : True := by
  aide h
  trivial


example (P : ℕ → Prop) (h : ∃ n : ℕ, P n) : True := by
  aide h
  trivial

example (P : ℕ → ℕ → Prop) (h : ∀ k, ∃ n : ℕ, P n k) : True := by
  aide h
  trivial

example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n : ℕ, P n k) : True := by
  aide h
  trivial


example (P : ℕ → Prop): ∃ n : ℕ, P n → True := by
  aide
  use 0
  tauto

example (P Q : Prop) (h : Q) : P → Q := by
  aide
  exact fun _ ↦ h

example : ∀ n ≥ 0, True := by
  aide
  intros
  trivial

example : ∀ n : ℕ, 0 ≤ n := by
  aide
  exact Nat.zero_le

example : ∃ n : ℕ, 0 ≤ n := by
  aide
  use 1
  exact Nat.zero_le 1

example : ∃ n ≥ 1, True := by
  aide
  use 1

example (h : Odd 3) : True := by
  aide h
  trivial
