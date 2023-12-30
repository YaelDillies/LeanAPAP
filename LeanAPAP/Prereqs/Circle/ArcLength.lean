import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import LeanAPAP.Mathlib.Analysis.SpecialFunctions.Complex.Arg
import LeanAPAP.Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

open Set
open scoped Real

namespace Complex
variable {a x y : ℂ}

/-- Chord-length is always less than arc-length. -/
lemma norm_sub_le_arcLength (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : ‖x - y‖ ≤ arcLength x y := by
  clear a
  wlog h : y = 1
  · have := @this (x / y) 1 (by simp only [norm_div, hx, hy, div_one]) norm_one rfl
    rwa [arcLength_div_left_eq_arcLength_mul_right, div_sub_one, norm_div, hy, div_one, one_mul]
      at this
    rintro rfl
    simp at hy
  subst y
  rw [norm_eq_abs, abs_eq_one_iff'] at hx
  obtain ⟨θ, hθ, rfl⟩ := hx
  rw [arcLength_exp_one, exp_mul_I, add_sub_right_comm, (toIocMod_eq_self _).2]
  norm_cast
  rw [norm_eq_abs, abs_add_mul_I, Real.sqrt_le_left (by positivity), ← _root_.abs_pow, abs_sq]
  calc
    _ = 2 * (1 - θ.cos) := by linear_combination θ.cos_sq_add_sin_sq
    _ ≤ 2 * (1 - (1 - θ ^ 2 / 2)) := by gcongr; exact Real.cos_quadratic_lower_bound
    _ = _ := by ring
  · convert hθ
    ring

/-- Chord-length is always greater than a multiple of arc-length. -/
lemma mul_arcLength_le_norm (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : 2 / π * arcLength x y ≤ ‖x - y‖ := by
  clear a
  wlog h : y = 1
  · have := @this (x / y) 1 (by simp only [norm_div, hx, hy, div_one]) norm_one rfl
    rwa [arcLength_div_left_eq_arcLength_mul_right, div_sub_one, norm_div, hy, div_one, one_mul]
      at this
    rintro rfl
    simp at hy
  subst y
  rw [norm_eq_abs, abs_eq_one_iff'] at hx
  obtain ⟨θ, hθ, rfl⟩ := hx
  rw [arcLength_exp_one, exp_mul_I, add_sub_right_comm, (toIocMod_eq_self _).2]
  norm_cast
  rw [norm_eq_abs, abs_add_mul_I]
  refine Real.le_sqrt_of_sq_le ?_
  rw [mul_pow, ← _root_.abs_pow, abs_sq]
  calc
    _ = 2 * (1 - (1 - 2 / π ^ 2 * θ ^ 2)) := by ring
    _ ≤ 2 * (1 - θ.cos) := by
        gcongr; exact Real.cos_quadratic_upper_bound $ abs_le.2 $ Ioc_subset_Icc_self hθ
    _  = _ := by linear_combination -θ.cos_sq_add_sin_sq
  · convert hθ
    ring

/-- Arc-length is always less than a multiple of chord-length. -/
lemma arcLength_le_mul_norm (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : arcLength x y ≤ π / 2 * ‖x - y‖ := by
  rw [← div_le_iff' $ by positivity, div_eq_inv_mul, inv_div]; exact mul_arcLength_le_norm hx hy
