import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Data.Rat.Cast.Order

variable {α : Type*}

instance [Preorder α] [MulAction ℚ α] [PosSMulMono ℚ α] : PosSMulMono ℚ≥0 α where
  elim a _ _b₁ _b₂ hb := (smul_le_smul_of_nonneg_left hb a.2 :)

instance LinearOrderedSemifield.toPosSMulStrictMono [LinearOrderedSemifield α] :
    PosSMulStrictMono ℚ≥0 α where
  elim a ha b₁ b₂ hb := by
    simp_rw [NNRat.smul_def]; exact mul_lt_mul_of_pos_left hb (NNRat.cast_pos.2 ha)
