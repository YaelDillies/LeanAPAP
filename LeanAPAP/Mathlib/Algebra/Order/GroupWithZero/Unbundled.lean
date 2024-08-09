import Mathlib.Algebra.Order.GroupWithZero.Unbundled

section LinearOrderedSemiring
variable {G₀ : Type*} [Zero G₀] [MulOneClass G₀] [Preorder G₀] {a b : G₀}

lemma one_lt_of_lt_mul_left₀ [PosMulReflectLT G₀] (ha : 0 ≤ a) (h : a < a * b) : 1 < b :=
  lt_of_mul_lt_mul_left (by simpa) ha

lemma one_lt_of_lt_mul_right₀ [MulPosReflectLT G₀] (hb : 0 ≤ b) (h : b < a * b) : 1 < a :=
  lt_of_mul_lt_mul_right (by simpa) hb

lemma one_le_of_le_mul_left₀ [PosMulReflectLE G₀] (ha : 0 < a) (h : a ≤ a * b) : 1 ≤ b :=
  le_of_mul_le_mul_left (by simpa) ha

lemma one_le_of_le_mul_right₀ [MulPosReflectLE G₀] (hb : 0 < b) (h : b ≤ a * b) : 1 ≤ a :=
  le_of_mul_le_mul_right (by simpa) hb

end LinearOrderedSemiring
