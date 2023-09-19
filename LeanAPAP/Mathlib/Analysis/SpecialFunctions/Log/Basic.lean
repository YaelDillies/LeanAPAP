import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Real
variable {x y : ℝ}

lemma log_le_log_of_le (hx : 0 < x) (hxy : x ≤ y) : log x ≤ log y :=
  (log_le_log hx (hx.trans_le hxy)).2 hxy

end Real
