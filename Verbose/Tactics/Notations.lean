import Mathlib.Util.Delaborators
import Mathlib.Mathport.Notation
import Mathlib.Tactic.SuppressCompilation

/-! # Notations

This sets up the mathematical notation for implication with the corresponding delaborator
(which is complicated because the core logical foundation sees functions everywhere...).
-/

notation:25 (priority := high) a:26 " ⇒ " b:25 => a → b

open Lean PrettyPrinter Delaborator SubExpr

@[delab forallE]
def delabDoubleArrow : Delab := do
  let e ← getExpr
  unless e.isArrow do failure
  unless ← (Meta.isProp e.bindingDomain! <&&> Meta.isProp e.bindingBody!) do failure
  let p ← withBindingDomain delab
  let q ← withBindingBody `a delab
  `($p ⇒ $q)

@[delab forallE]
def delabPi : Delab := whenPPOption Lean.getPPNotation do
  let stx ← delabDoubleArrow <|> delabForall
  match stx with
  | `(∀ ($i:ident : $_), $j:ident ∈ $s ⇒ $body) =>
    if i == j then `(∀ $i:ident ∈ $s, $body) else pure stx
  | `(∀ ($x:ident : $_), $y:ident > $z ⇒ $body) =>
    if x == y then `(∀ $x:ident > $z, $body) else pure stx
  | `(∀ ($x:ident : $_), $y:ident < $z ⇒ $body) =>
    if x == y then `(∀ $x:ident < $z, $body) else pure stx
  | `(∀ ($x:ident : $_), $y:ident ≥ $z ⇒ $body) =>
    if x == y then `(∀ $x:ident ≥ $z, $body) else pure stx
  | `(∀ ($x:ident : $_), $y:ident ≤ $z ⇒ $body) =>
    if x == y then `(∀ $x:ident ≤ $z, $body) else pure stx
  | `(Π ($i:ident : $_), $j:ident ∈ $s ⇒ $body) =>
    if i == j then `(Π $i:ident ∈ $s, $body) else pure stx
  | `(∀ ($i:ident : $_), $j:ident ∉ $s ⇒ $body) =>
    if i == j then `(∀ $i:ident ∉ $s, $body) else pure stx
  | `(∀ ($i:ident : $_), $j:ident ⊆ $s ⇒ $body) =>
    if i == j then `(∀ $i:ident ⊆ $s, $body) else pure stx
  | `(∀ ($i:ident : $_), $j:ident ⊂ $s ⇒ $body) =>
    if i == j then `(∀ $i:ident ⊂ $s, $body) else pure stx
  | `(∀ ($i:ident : $_), $j:ident ⊇ $s ⇒ $body) =>
    if i == j then `(∀ $i:ident ⊇ $s, $body) else pure stx
  | `(∀ ($i:ident : $_), $j:ident ⊃ $s ⇒ $body) =>
    if i == j then `(∀ $i:ident ⊃ $s, $body) else pure stx
  | _ => pure stx
