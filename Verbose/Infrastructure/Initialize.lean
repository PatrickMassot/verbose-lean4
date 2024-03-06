import Lean

/-! # Options initialization

This file define options for the tactic framework.
-/

register_option verbose.suggestion_widget : Bool := {
  defValue := false
  descr := "Show the suggestion widget in proofs." }

register_option verbose.suggestion_debug : Bool := {
  defValue := false
  descr := "Report debug info in the suggestion widget." }
