import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import LeanAPAP.Mathlib.Data.Nat.Factorial.Basic

open NormedSpace
open scoped Nat

namespace Complex

/-- The power series expansion of `Complex.cosh`. -/
lemma hasSum_cosh (z : ℂ) : HasSum (fun n ↦ z ^ (2 * n) / ↑(2 * n)!) (cosh z) := by
  simpa [mul_assoc, cos_mul_I] using hasSum_cos' (z * I)

/-- The power series expansion of `Complex.sinh`. -/
lemma hasSum_sinh (z : ℂ) : HasSum (fun n ↦ z ^ (2 * n + 1) / ↑(2 * n + 1)!) (sinh z) := by
  simpa [mul_assoc, sin_mul_I, neg_pow z, pow_add, pow_mul, neg_mul, neg_div]
    using (hasSum_sin' (z * I)).mul_right (-I)

lemma cosh_eq_tsum (z : ℂ) : cosh z = ∑' n, z ^ (2 * n) / ↑(2 * n)! := z.hasSum_cosh.tsum_eq.symm

lemma sinh_eq_tsum (z : ℂ) : sinh z = ∑' n, z ^ (2 * n + 1) / ↑(2 * n + 1)! :=
  z.hasSum_sinh.tsum_eq.symm

end Complex

namespace Real

/-- The power series expansion of `Real.cosh`. -/
lemma hasSum_cosh (r : ℝ) : HasSum (fun n  ↦ r ^ (2 * n) / ↑(2 * n)!) (cosh r) :=
  mod_cast Complex.hasSum_cosh r

/-- The power series expansion of `Real.sinh`. -/
lemma hasSum_sinh (r : ℝ) : HasSum (fun n ↦ r ^ (2 * n + 1) / ↑(2 * n + 1)!) (sinh r) :=
  mod_cast Complex.hasSum_sinh r

lemma cosh_eq_tsum (r : ℝ) : cosh r = ∑' n, r ^ (2 * n) / ↑(2 * n)! := r.hasSum_cosh.tsum_eq.symm

lemma sinh_eq_tsum (r : ℝ) : sinh r = ∑' n, r ^ (2 * n + 1) / ↑(2 * n + 1)! :=
  r.hasSum_sinh.tsum_eq.symm

lemma cosh_le_exp_half_sq (x : ℝ) : cosh x ≤ exp (x ^ 2 / 2) := by
  rw [cosh_eq_tsum, exp_eq_exp_ℝ, exp_eq_tsum]
  refine tsum_le_tsum (fun i ↦ ?_) x.hasSum_cosh.summable $ expSeries_summable' (x ^ 2 / 2)
  simp only [div_pow, pow_mul, smul_eq_mul, inv_mul_eq_div, div_div]
  gcongr
  norm_cast
  exact Nat.two_pow_mul_factorial_le_factorial_two_mul

end Real
