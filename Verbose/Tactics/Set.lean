import Lean
import Verbose.Tactics.Common
import Verbose.Tactics.MaybeTypedIdent

open Lean Meta Elab Tactic Mathlib.Tactic

/-
The code below is a simplified version of the code in `Mathlib.Tactic.Set`.
-/

def setTac (n : Ident) (ty : Option Term) (val : Term) : TacticM Unit :=
  withMainContext do
    let (ty, vale) ← match ty with
    | some ty =>
      let ty ← Term.elabType ty
      pure (ty, ← elabTermEnsuringType val ty)
    | none =>
      let val ← elabTerm val none
      pure (← inferType val, val)
    let fvar ← liftMetaTacticAux fun goal ↦ do
      let (fvar, goal) ← (← goal.define n.getId ty vale).intro1P
      pure (fvar, [goal])
    Term.addTermInfo' (isBinder := true) n (mkFVar fvar)
    evalTactic (← `(tactic| try rewrite [show $(← Term.exprToSyntax vale) = $n from rfl] at *))
    let h : Ident := mkIdent (toString n ++ "_def")
    evalTactic (← `(tactic| have
        $h : $n = ($(← Term.exprToSyntax vale) : $(← Term.exprToSyntax ty)) := rfl))
