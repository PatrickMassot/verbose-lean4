import Mathlib.Tactic
import Verbose.Tactics.Multilingual

open Verbose Lean

-- whatsnew in
endpoint foo (a : Nat) : MetaM Nat := pure a

run_cmd
  let n := mkIdent <| .str (.num `foo._hyg 26) "_cstage1"
  Elab.Command.elabCommand <|← `(#print $n:ident)

#check foo

#check foo._default

#eval foo 2

endpoint (lang := en) foo (_ : Nat) : MetaM Nat := pure 0
endpoint (lang := fr) foo (_ : Nat) : MetaM Nat := pure 1

set_option verbose.lang "fr"

#check foo

#eval foo 2
