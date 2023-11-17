import Lean

open Lean Meta Elab Command

def explBinder := leading_parser Lean.Parser.Term.explicitBinder

open TSyntax.Compat in
def mkExampleArgs (objs hyps : TSyntaxArray `explBinder)  :
    TSyntaxArray `Lean.Parser.Term.bracketedBinder :=
  objs ++ hyps


elab "Exercise" str "Given:" objs:explBinder* "Assume:" hyps:explBinder* "Conclusion:" concl:term "Proof:" prf:tacticSeq : command => do
  elabCommand (← `(command|example $(mkExampleArgs objs hyps):bracketedBinder* : $concl := by $prf))

/- set_option pp.rawOnError true

Exercise "Test"
  Given: (n : Nat)
  Assume: (hn : n = 0)
  Conclusion: True

  Proof:
  trivial

example (n : Nat) (hn : n = 0) : True := by trivial -/
