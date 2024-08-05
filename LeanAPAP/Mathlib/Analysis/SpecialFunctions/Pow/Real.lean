import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Real
variable {x y : ℝ}

lemma lt_pow_iff_log_lt {n : ℕ} (hx : 0 < x) (hy : 0 < y) :
    x < y ^ n ↔ Real.log x < n * Real.log y := by rw [← lt_rpow_iff_log_lt hx hy, rpow_natCast]

lemma lt_zpow_iff_log_lt {n : ℤ} (hx : 0 < x) (hy : 0 < y) :
    x < y ^ n ↔ Real.log x < n * Real.log y := by rw [← lt_rpow_iff_log_lt hx hy, rpow_intCast]

end Real
