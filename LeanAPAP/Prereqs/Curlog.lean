import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Miscellaneous definitions
-/

open Set
open scoped ComplexConjugate NNReal

namespace Real
variable {x : ℝ}

-- Maybe define as `2 - log x`
noncomputable def curlog (x : ℝ) : ℝ := log (exp 2 / x)

@[simp] lemma curlog_zero : curlog 0 = 0 := by simp [curlog]

lemma two_le_curlog (hx₀ : 0 < x) (hx : x ≤ 1) : 2 ≤ x.curlog :=
  (le_log_iff_exp_le (by positivity)).2 (le_div_self (exp_pos _).le hx₀ hx)

lemma curlog_pos (hx₀ : 0 < x) (hx : x ≤ 1) : 0 < x.curlog :=
  zero_lt_two.trans_le $ two_le_curlog hx₀ hx

lemma curlog_nonneg (hx₀ : 0 ≤ x) (hx : x ≤ 1) : 0 ≤ x.curlog := by
  obtain rfl | hx₀ := hx₀.eq_or_lt
  · simp
  · exact (curlog_pos hx₀ hx).le

lemma inv_le_exp_curlog : x⁻¹ ≤ exp (curlog x) := by
  obtain hx | hx := le_or_lt x 0
  · exact (inv_nonpos.2 hx).trans (exp_pos _).le
  rw [curlog, exp_log, ←one_div, div_le_div_right hx]
  · norm_num
  · positivity

lemma log_one_div_le_curlog (hx : 0 ≤ x) : log (1 / x) ≤ curlog x := by
  obtain rfl | hx := hx.eq_or_lt
  · simp
  · unfold curlog
    gcongr
    norm_num

lemma log_inv_le_curlog (hx : 0 ≤ x) : log x⁻¹ ≤ curlog x := by
  rw [←one_div]; exact log_one_div_le_curlog hx

lemma rpow_neg_inv_curlog_le (hx : 0 ≤ x) (hx' : x ≤ 1) : x ^ (-(curlog x)⁻¹) ≤ exp 1 := by
  obtain rfl | hx := hx.eq_or_lt
  · simp
  obtain rfl | hx' := hx'.eq_or_lt
  · simp
  have : -1 / log (1 / x) ≤ -1 / curlog x := by
    rw [neg_div, neg_div, neg_le_neg_iff]
    refine one_div_le_one_div_of_le ?_ (log_one_div_le_curlog hx.le)
    refine log_pos ?_
    rwa [lt_div_iff hx, one_mul]
  rw [←one_div, ←neg_div]
  refine (rpow_le_rpow_of_exponent_ge hx hx'.le this).trans ?_
  rw [one_div, log_inv, rpow_def_of_pos hx, neg_div_neg_eq, mul_one_div, div_self]
  exact log_ne_zero_of_pos_of_ne_one hx hx'.ne

end Real
