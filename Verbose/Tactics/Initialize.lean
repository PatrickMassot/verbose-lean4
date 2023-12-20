import Lean

register_option verbose.suggestion_widget : Bool := {
  defValue := false
  descr := "Show the suggestion widget in proofs." }

register_option verbose.suggestion_debug : Bool := {
  defValue := false
  descr := "Report debug info in the suggestion widget." }
