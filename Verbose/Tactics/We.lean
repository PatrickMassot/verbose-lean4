import Lean
import Verbose.Tactics.Common

open Lean Parser Elab Tactic

/- Restore rewrite using a single term without brackets. -/
declare_syntax_cat myRwRuleSeq
syntax rwRule : myRwRuleSeq
syntax "[" rwRule,*,? "]" : myRwRuleSeq

def rewrite_macro (rw : Syntax) (s : TSyntax `myRwRuleSeq)
    (l : Option (TSyntax `Lean.Parser.Tactic.location)) : MacroM (TSyntax `tactic) :=
  match s with
  | `(myRwRuleSeq| [%$lbrak $rs:rwRule,* ]%$rbrak) =>
    -- We show the `rfl` state on `]`
    `(tactic| (rewrite%$rw [%$lbrak $rs,*] $(l)?; try (with_reducible rfl%$rbrak)))
  | `(myRwRuleSeq| $rs:rwRule) =>
    `(tactic| (rewrite%$rw  [$rs] $(l)?; try (with_reducible rfl)))
  | _ => Macro.throwUnsupported

def discussOr (input : Term) : TacticM Unit := do
  evalApplyLikeTactic MVarId.apply <| ← `(Or.elim $input)

def discussEm (input : Term) : TacticM Unit := do
  evalApplyLikeTactic MVarId.apply <| ← `(Or.elim <| Classical.em $input)
