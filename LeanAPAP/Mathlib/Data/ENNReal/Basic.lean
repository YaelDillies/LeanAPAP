import Mathlib.Data.ENNReal.Basic

/-!
### TODO

Unprotect `coe_injective` and a few more
Make `coe_nsmul` defeq (needs `WithTop.addMonoid` to change)
-/

open scoped NNReal

namespace ENNReal
variable {p q : ℝ≥0}

lemma coe_ne_coe : (p : ℝ≥0∞) ≠ q ↔ p ≠ q := ENNReal.coe_injective.ne_iff

@[norm_cast] lemma coe_nsmul (n : ℕ) (p : ℝ≥0) : (↑(n • p) : ℝ≥0∞) = n • p := WithTop.coe_nsmul _ _

end ENNReal
