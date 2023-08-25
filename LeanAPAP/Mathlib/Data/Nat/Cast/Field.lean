import Mathbin.Data.Nat.Cast.Field

#align_import mathlib.data.nat.cast.field

variable {α : Type _} [LinearOrderedSemifield α]

theorem Nat.cast_inv_le_one : ∀ n : ℕ, (n⁻¹ : α) ≤ 1
  | 0 => by simp
  | n + 1 => inv_le_one <| by simp [Nat.cast_nonneg]

