import data.nat.cast.field

variables {α : Type*} [linear_ordered_semifield α]

lemma nat.cast_inv_le_one : ∀ (n : ℕ), (n⁻¹ : α) ≤ 1
| 0 := by simp
| (n + 1) := inv_le_one $ by simp [nat.cast_nonneg]
