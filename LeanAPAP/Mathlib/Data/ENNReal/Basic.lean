import Mathlib.Data.ENNReal.Basic

open scoped NNReal

namespace ENNReal

-- TODO: Replace in mathlib
lemma toNNReal_coe' (r : ℝ≥0) : ENNReal.toNNReal r = r := toNNReal_coe

end ENNReal
