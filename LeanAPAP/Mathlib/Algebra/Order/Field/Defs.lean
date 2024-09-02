import Mathlib.Algebra.Order.Field.Defs

variable {α : Type*} [LinearOrderedSemifield α] {a : α}

lemma mul_inv_le_one : a * a⁻¹ ≤ 1 := by obtain rfl | ha := eq_or_ne a 0 <;> simp [*]
lemma inv_mul_le_one : a⁻¹ * a ≤ 1 := by obtain rfl | ha := eq_or_ne a 0 <;> simp [*]
