import Mathlib.Data.Complex.Abs

namespace Complex

lemma abs_add_mul_I (x y : ℝ) : abs (x + y * I) = (x ^ 2 + y ^ 2).sqrt := by
  rw [← normSq_add_mul_I]; rfl

end Complex
