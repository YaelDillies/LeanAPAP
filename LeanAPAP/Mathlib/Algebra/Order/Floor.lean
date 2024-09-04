import Mathlib.Algebra.Order.Floor

namespace Nat
variable {α : Type*} [LinearOrderedField α] [FloorSemiring α] {a b : α}

lemma ceil_lt_mul (ha : 0 ≤ a) (hb : 1 < b) (h : (b - 1)⁻¹ ≤ a) : ⌈a⌉₊ < b * a := by
  rw [← sub_pos] at hb
  calc
    ⌈a⌉₊ < a + 1 := ceil_lt_add_one ha
    _ = a + (b - 1) * (b - 1)⁻¹ := by rw [mul_inv_cancel₀]; positivity
    _ ≤ a + (b - 1) * a := by gcongr; positivity
    _ = b * a := by rw [sub_one_mul, add_sub_cancel]

lemma ceil_lt_two_mul (ha : 1 ≤ a) : ⌈a⌉₊ < 2 * a :=
  ceil_lt_mul (by positivity) one_lt_two (by norm_num; exact ha)

end Nat

namespace Int
variable {α : Type*} [LinearOrderedField α] [FloorRing α] {a b : α}

lemma ceil_lt_mul (hb : 1 < b) (ha : (b - 1)⁻¹ ≤ a) : ⌈a⌉ < b * a := by
  rw [← sub_pos] at hb
  calc
    ⌈a⌉ < a + 1 := ceil_lt_add_one _
    _ = a + (b - 1) * (b - 1)⁻¹ := by rw [mul_inv_cancel₀]; positivity
    _ ≤ a + (b - 1) * a := by gcongr; positivity
    _ = b * a := by rw [sub_one_mul, add_sub_cancel]

lemma ceil_lt_two_mul (ha : 1 ≤ a) : ⌈a⌉ < 2 * a := ceil_lt_mul one_lt_two (by norm_num; exact ha)

end Int
