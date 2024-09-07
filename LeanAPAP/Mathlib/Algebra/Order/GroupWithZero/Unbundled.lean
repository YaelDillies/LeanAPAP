import Mathlib.Algebra.Order.GroupWithZero.Unbundled

/-!
# TODO

Rename `one_le_mul_of_one_le_of_one_le` to `one_le_mul₀`
-/

variable {G₀ : Type*} [GroupWithZero G₀] [PartialOrder G₀] [ZeroLEOneClass G₀] [PosMulReflectLT G₀]
  {a b : G₀} [PosMulMono G₀]

-- TODO: Unify with `le_inv`
lemma le_inv_comm₀ (ha : 0 < a) (hb : 0 < b) : a ≤ b⁻¹ ↔ b ≤ a⁻¹ := sorry
