import Mathlib.Data.Real.ENNReal

open scoped ENNReal

namespace ENNReal
variable {x : ℝ≥0∞}

@[simp] protected lemma inv_eq_one : x⁻¹ = 1 ↔ x = 1 := by rw [←inv_inj, inv_inv, inv_one]

end ENNReal
