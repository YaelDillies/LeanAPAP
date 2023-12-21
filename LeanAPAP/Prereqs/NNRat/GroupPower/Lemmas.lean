import Mathlib.Algebra.GroupPower.Lemmas
import Mathlib.Algebra.Order.Module.Defs
import LeanAPAP.Prereqs.NNRat.Cast.Defs

open scoped NNRat

variable {α : Type*} [LinearOrderedAddCommGroup α] [DistribMulAction ℚ≥0 α] [PosSMulMono ℚ≥0 α]

@[simp] lemma abs_nnqsmul (q : ℚ≥0) (a : α) : |q • a| = q • |a| := by
  obtain ha | ha := le_total a 0 <;>
    simp [abs_of_nonneg, abs_of_nonpos, smul_neg, *, smul_nonpos_of_nonneg_of_nonpos, smul_nonneg]
