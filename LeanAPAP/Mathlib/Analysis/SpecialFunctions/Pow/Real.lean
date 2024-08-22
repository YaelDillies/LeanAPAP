import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Real
variable {x y z : ℝ}

lemma rpow_le_iff_le_log (hx : 0 < x) (hy : 0 < y) : x ^ z ≤ y ↔ z * log x ≤ log y := by
  rw [← log_le_log_iff (rpow_pos_of_pos hx _) hy, log_rpow hx]

lemma rpow_lt_iff_lt_log (hx : 0 < x) (hy : 0 < y) : x ^ z < y ↔ z * log x < log y := by
  rw [← log_lt_log_iff (rpow_pos_of_pos hx _) hy, log_rpow hx]

lemma pow_le_iff_le_log {n : ℕ} (hx : 0 < x) (hy : 0 < y) :
    x ^ n ≤ y ↔ n * log x ≤ log y := by rw [← rpow_le_iff_le_log hx hy, rpow_natCast]

lemma zpow_le_iff_le_log {n : ℤ} (hx : 0 < x) (hy : 0 < y) :
    x ^ n ≤ y ↔ n * log x ≤ log y := by rw [← rpow_le_iff_le_log hx hy, rpow_intCast]

lemma pow_lt_iff_lt_log {n : ℕ} (hx : 0 < x) (hy : 0 < y) :
    x ^ n < y ↔ n * log x < log y := by rw [← rpow_lt_iff_lt_log hx hy, rpow_natCast]

lemma zpow_lt_iff_lt_log {n : ℤ} (hx : 0 < x) (hy : 0 < y) :
    x ^ n < y ↔ n * log x < log y := by rw [← rpow_lt_iff_lt_log hx hy, rpow_intCast]

lemma le_pow_iff_log_le {n : ℕ} (hx : 0 < x) (hy : 0 < y) : x ≤ y ^ n ↔ log x ≤ n * log y := by
  rw [← le_rpow_iff_log_le hx hy, rpow_natCast]

lemma le_zpow_iff_log_le {n : ℤ} (hx : 0 < x) (hy : 0 < y) : x ≤ y ^ n ↔ log x ≤ n * log y := by
  rw [← le_rpow_iff_log_le hx hy, rpow_intCast]

lemma lt_pow_iff_log_lt {n : ℕ} (hx : 0 < x) (hy : 0 < y) : x < y ^ n ↔ log x < n * log y := by
  rw [← lt_rpow_iff_log_lt hx hy, rpow_natCast]

lemma lt_zpow_iff_log_lt {n : ℤ} (hx : 0 < x) (hy : 0 < y) : x < y ^ n ↔ log x < n * log y := by
  rw [← lt_rpow_iff_log_lt hx hy, rpow_intCast]

-- TODO: Replace in mathlib
alias rpow_add_intCast := rpow_add_int
alias rpow_add_natCast := rpow_add_nat
alias rpow_sub_intCast := rpow_sub_int
alias rpow_sub_natCast := rpow_sub_nat
alias rpow_add_intCast' := rpow_add_int'
alias rpow_add_natCast' := rpow_add_nat'
alias rpow_sub_intCast' := rpow_sub_int'
alias rpow_sub_natCast' := rpow_sub_nat'

end Real
