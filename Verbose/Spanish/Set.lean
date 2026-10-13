import Verbose.Tactics.Set
import Verbose.Spanish.Common

elab "Tomemos " n:maybeTypedIdent " := " val:term : tactic => do
  let (n, ty) := match n with
  | `(maybeTypedIdent| $N:ident) => (N, none)
  | `(maybeTypedIdent|($N : $TY)) => (N, some TY)
  | _ => (default, none)
  setTac n ty val


setLang es

example (a b : ℕ) : ℕ := by
  Tomemos n := max a b
  success_if_fail_with_msg "El nombre n ya está en uso"
    Tomemos n := 1
  exact n

example (a b : ℕ) : ℕ := by
  Tomemos (n : ℕ) := max a b
  exact n

example : ℤ := by
  Tomemos (n : ℤ) := max 0 1
  exact n
