import Mathlib.Data.Nat.Cast.Field

variable {α : Type*} [LinearOrderedSemifield α]

lemma Nat.cast_inv_le_one : ∀ n : ℕ, (n⁻¹ : α) ≤ 1
  | 0 => by simp
  | n + 1 => inv_le_one $ by simp [Nat.cast_nonneg]
