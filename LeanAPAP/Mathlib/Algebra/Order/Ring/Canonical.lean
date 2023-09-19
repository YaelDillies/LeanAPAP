import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Tactic.Ring

variable {α : Type*} [LinearOrderedCommSemiring α] [ExistsAddOfLE α] {a b : α}

lemma add_sq_le : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  calc
    (a + b) ^ 2 = a ^ 2 + b ^ 2 + (a * b + b * a) := by ring
    _ ≤ a ^ 2 + b ^ 2 + (a * a + b * b) := add_le_add_left ?_ _
    _ = _ := by ring
  cases le_total a b
  · exact mul_add_mul_le_mul_add_mul ‹_› ‹_›
  · exact mul_add_mul_le_mul_add_mul' ‹_› ‹_›
