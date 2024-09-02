import LeanAPAP.Mathlib.Algebra.Order.Field.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Real
variable {x : ℝ}

lemma rpow_inv_log_le_exp_one : x ^ (log x)⁻¹ ≤ exp 1 := by
  refine (le_abs_self _).trans ?_
  refine (Real.abs_rpow_le_abs_rpow _ _).trans ?_
  rw [← log_abs]
  obtain hx | hx := (abs_nonneg x).eq_or_gt
  · simp [hx]
  · rw [rpow_def_of_pos hx]
    gcongr
    exact mul_inv_le_one

end Real
