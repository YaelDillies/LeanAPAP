import Mathbin.Analysis.SpecialFunctions.Log.Basic

#align_import mathlib.analysis.special_functions.log.basic

namespace Real

variable {x y : ℝ}

theorem log_le_log_of_le (hx : 0 < x) (hxy : x ≤ y) : log x ≤ log y :=
  (log_le_log hx (hx.trans_le hxy)).2 hxy

end Real

