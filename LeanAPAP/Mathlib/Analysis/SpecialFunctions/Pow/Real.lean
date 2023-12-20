import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Real
variable {x y z : ℝ}

--TODO: Replace `rpow_nonneg_of_nonneg`
lemma rpow_nonneg (hx : 0 ≤ x) : 0 ≤ x ^ y := rpow_nonneg_of_nonneg hx _

end Real
