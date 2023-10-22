import Mathlib.Data.Complex.Basic

/-!
### TODO

`Complex.ext` lemma is a bad `ext` lemma to have globally.
-/

namespace Complex

attribute [simp] I_ne_zero

@[norm_cast] lemma ofReal'_nsmul (n : ℕ) (r : ℝ) : ofReal' (n • r) = n • ofReal' r := by simp

end Complex
