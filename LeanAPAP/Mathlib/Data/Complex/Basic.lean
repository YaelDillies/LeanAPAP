import Mathlib.Data.Complex.Basic

namespace Complex

attribute [simp] I_ne_zero

@[norm_cast] lemma ofReal_nsmul (n : ℕ) (r : ℝ) : ↑(n • r) = n • (r : ℂ) := by simp
@[norm_cast] lemma ofReal_zsmul (n : ℤ) (r : ℝ) : ↑(n • r) = n • (r : ℂ) := by simp

lemma re_mul_ofReal (z : ℂ) (r : ℝ) : (z * r).re = z.re *  r := by simp [ofReal']
lemma im_mul_ofReal (z : ℂ) (r : ℝ) : (z * r).im = z.im *  r := by simp [ofReal']

end Complex
