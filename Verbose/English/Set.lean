import Verbose.Tactics.Set
import Verbose.English.Common

elab "Set " n:maybeTypedIdent " := " val:term : tactic => do
  let (n, ty) := match n with
  | `(maybeTypedIdent| $N:ident) => (N, none)
  | `(maybeTypedIdent|($N : $TY)) => (N, some TY)
  | _ => (default, none)
  setTac n ty val


setLang en

example (a b : ℕ) : ℕ := by
  Set n := max a b
  success_if_fail_with_msg "The name n is already used"
    Set n := 1
  exact n

example (a b : ℕ) : ℕ := by
  Set (n : ℕ) := max a b
  exact n

example : ℤ := by
  Set (n : ℤ) := max 0 1
  exact n
