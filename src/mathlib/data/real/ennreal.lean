import data.real.ennreal

open_locale ennreal

namespace ennreal
variables {x : ℝ≥0∞}

@[simp] protected lemma inv_eq_one : x⁻¹ = 1 ↔ x = 1 := by rw [←inv_inj, inv_inv, inv_one]

end ennreal
