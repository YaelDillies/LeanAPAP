import Mathlib.Algebra.Order.Field.Basic
import LeanAPAP.Mathlib.Algebra.Order.Ring.Lemmas

/-!
### TODO

Replace in mathlib
-/

alias div_le_div_of_pos_left := div_le_div_of_le_left
alias div_le_div_of_nonneg_right := div_le_div_of_le_of_nonneg

variable {α : Type*}

section LinearOrderedSemifield
variable [LinearOrderedSemifield α] {a b : α}

-- div_pos
-- div_neg_of_pos_of_neg

@[simp]
lemma div_pos_iff_of_pos_left [PosMulStrictMono α] [PosMulReflectLT α] (ha : 0 < a) :
    0 < a / b ↔ 0 < b := by
  simp only [div_eq_mul_inv, mul_pos_iff_of_pos_left ha, inv_pos]

-- div_nonneg
-- div_nonpos_of_nonneg_of_nonpos
-- pos_of_div_pos_right

-- div_neg_of_neg_of_pos

@[simp]
lemma div_pos_iff_of_pos_right [MulPosStrictMono α] [MulPosReflectLT α] (hb : 0 < b) :
    0 < a / b ↔ 0 < a := by
  simp only [div_eq_mul_inv, mul_pos_iff_of_pos_right (inv_pos.2 hb)]

-- div_nonpos_of_nonpos_of_nonneg
-- pos_of_div_pos_left
-- pos_iff_pos_of_div_pos

end LinearOrderedSemifield
