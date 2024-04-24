import Mathlib.Algebra.Order.Module.Defs
import LeanAPAP.Mathlib.Algebra.Order.Field.Basic

variable {α : Type*}

section LinearOrderedAddCommGroup
variable [LinearOrderedAddCommGroup α] [DistribMulAction ℚ≥0 α] [PosSMulMono ℚ≥0 α]

@[simp] lemma abs_nnqsmul (q : ℚ≥0) (a : α) : |q • a| = q • |a| := by
  obtain ha | ha := le_total a 0 <;>
    simp [abs_of_nonneg, abs_of_nonpos, smul_neg, *, smul_nonpos_of_nonneg_of_nonpos, smul_nonneg]

end LinearOrderedAddCommGroup

section LinearOrderedSemifield
variable [LinearOrderedSemifield α]

instance LinearOrderedSemifield.toPosSMulStrictMono_rat : PosSMulStrictMono ℚ≥0 α where
  elim q hq a b hab := by
    rw [NNRat.smul_def, NNRat.smul_def]; exact mul_lt_mul_of_pos_left hab $ NNRat.cast_pos.2 hq

end LinearOrderedSemifield
