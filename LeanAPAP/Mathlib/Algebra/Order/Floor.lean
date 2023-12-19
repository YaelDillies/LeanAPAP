import Mathlib.Algebra.Order.Floor

section
variable {α : Type*} [LinearOrderedRing α] [FloorRing α] {a : α}

@[simp] lemma natCast_floor_eq_intCast_floor (ha : 0 ≤ a) : (⌊a⌋₊ : α) = ⌊a⌋ := by
  simp [← Nat.cast_floor_eq_int_floor ha]

@[simp] lemma natCast_ceil_eq_intCast_ceil (ha : 0 ≤ a) : (⌈a⌉₊ : α) = ⌈a⌉ := by
  simp [← Nat.cast_ceil_eq_int_ceil ha]

end
