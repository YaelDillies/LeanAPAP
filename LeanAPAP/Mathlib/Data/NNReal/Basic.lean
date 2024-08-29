import Mathlib.Data.NNReal.Basic

namespace NNReal

@[simp, norm_cast] lemma coe_nnqsmul (q : ℚ≥0) (x : ℝ≥0) : ↑(q • x) = (q • x : ℝ) := rfl

end NNReal
