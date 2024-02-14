import Verbose.Tactics.Multilingual

open Verbose Lean

endpoint foo (a : Nat) : MetaM Nat := pure a
endpoint (lang := en) foo (_ : Nat) : MetaM Nat := pure 0
endpoint (lang := fr) foo (_ : Nat) : MetaM Nat := pure 1

#eval foo 2
