import Mathlib.Data.Real.ConjExponents

/-!
# TODO

Unprime `NNReal.HolderTriple.inv_add_inv'`, `ENNReal.HolderTriple.inv_add_inv'`
Add `HolderTriple.le`, `HolderConjugate.one_le`, `HolderConjugate.one_lt` for discoverability
-/

namespace NNReal
variable {p q r : ℝ≥0}

lemma HolderTriple.holderConjugate_div_div (hpq : HolderTriple p q r) (hr : r ≠ 0) :
    (p / r).HolderConjugate (q / r) where
  inv_add_inv' := by simp [inv_div, div_eq_mul_inv, ← mul_add, hpq.inv_add_inv', hr]
  left_pos := by have := hpq.left_pos; have := hpq.pos';  positivity
  right_pos := by have := hpq.right_pos; have := hpq.pos';  positivity

end NNReal

namespace ENNReal
variable {p q r : ℝ≥0∞}

lemma HolderTriple.holderConjugate_div_div [hpqr : HolderTriple p q r] (hr₀ : r ≠ 0) (hr : r ≠ ∞) :
    HolderConjugate (p / r) (q / r) where
  inv_add_inv' := by
    rw [ENNReal.inv_div (.inl hr) (.inl hr₀), ENNReal.inv_div (.inl hr) (.inl hr₀), div_eq_mul_inv,
      div_eq_mul_inv, ← mul_add, hpqr.inv_add_inv', ENNReal.mul_inv_cancel hr₀ hr, inv_one]

end ENNReal
