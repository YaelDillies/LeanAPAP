import Mathlib.Algebra.Order.Ring.Lemmas

variable {α : Type*}

alias mul_lt_mul_iff_of_pos_left := mul_lt_mul_left
alias mul_lt_mul_iff_of_pos_right := mul_lt_mul_right

section MulZeroClass
variable [MulZeroClass α] [Preorder α] {a b : α}

-- mul_pos
-- mul_neg_of_pos_of_neg

@[simp]
lemma mul_pos_iff_of_pos_left [PosMulStrictMono α] [PosMulReflectLT α] (ha : 0 < a) :
    0 < a * b ↔ 0 < b := by
  simpa only [mul_zero] using mul_lt_mul_iff_of_pos_left ha (b := 0) (c := b)

-- mul_nonneg
-- mul_nonpos_of_nonneg_of_nonpos
-- pos_of_mul_pos_right

-- mul_neg_of_neg_of_pos

@[simp]
lemma mul_pos_iff_of_pos_right [MulPosStrictMono α] [MulPosReflectLT α] (hb : 0 < b) :
    0 < a * b ↔ 0 < a := by
  simpa only [zero_mul] using mul_lt_mul_iff_of_pos_right hb (b := 0) (c := a)

-- mul_nonpos_of_nonpos_of_nonneg
-- pos_of_mul_pos_left
-- pos_iff_pos_of_mul_pos

end MulZeroClass
