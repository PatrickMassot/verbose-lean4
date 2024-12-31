import Verbose.Tactics.Set
import Verbose.French.Common

elab "Posons " n:maybeTypedIdent " := " val:term : tactic => do
  let (n, ty) := match n with
  | `(maybeTypedIdent| $N:ident) => (N, none)
  | `(maybeTypedIdent|($N : $TY)) => (N, some TY)
  | _ => (default, none)
  setTac n ty val


setLang fr

example (a b : ℕ) : ℕ := by
  Posons n := max a b
  success_if_fail_with_msg "Le nom n est déjà utilisé."
    Posons n := 1
  exact n

example (a b : ℕ) : ℕ := by
  Posons (n : ℕ) := max a b
  exact n

example : ℤ := by
  Posons (n : ℤ) := max 0 1
  exact n
