import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Real
variable {x : ℝ}

lemma log_le_self (hx : 0 ≤ x) : log x ≤ x := by
  obtain rfl | hx := hx.eq_or_lt
  · simp
  · exact (log_le_sub_one_of_pos hx).trans (by linarith)

end Real
