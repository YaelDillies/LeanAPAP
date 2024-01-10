import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Data.Complex.Abs

open scoped Real

namespace Complex
variable {a x : ℂ}

@[simp] lemma abs_arg_inv (x : ℂ) : |x⁻¹.arg| = |x.arg| := by rw [arg_inv]; split_ifs <;> simp [*]

lemma abs_eq_one_iff' : abs x = 1 ↔ ∃ θ ∈ Set.Ioc (-π) π, exp (θ * I) = x := by
  rw [abs_eq_one_iff]
  constructor
  · rintro ⟨θ, rfl⟩
    refine ⟨toIocMod (mul_pos two_pos Real.pi_pos) (-π) θ, ?_, ?_⟩
    · convert toIocMod_mem_Ioc _ _ _
      ring
    · rw [eq_sub_of_add_eq $ toIocMod_add_toIocDiv_zsmul _ _ θ, ofReal_sub,
      ofReal_zsmul, ofReal_mul, ofReal_ofNat, exp_mul_I_periodic.sub_zsmul_eq]
  · rintro ⟨θ, _, rfl⟩
    exact ⟨θ, rfl⟩

/-- The arclength between two complex numbers is the absolute value of their argument. -/
noncomputable def arcLength (x y : ℂ) : ℝ := |(x / y).arg|

lemma arcLength_comm (x y : ℂ) : arcLength x y = arcLength y x := by
  rw [arcLength, ← abs_arg_inv, inv_div, arcLength]

@[simp] lemma arcLength_zero_left (y : ℂ) : arcLength 0 y = 0 := by simp [arcLength]
@[simp] lemma arcLength_zero_right (x : ℂ) : arcLength x 0 = 0 := by simp [arcLength]
lemma arcLength_one_left (y : ℂ) : arcLength 1 y = |y.arg| := by simp [arcLength]
lemma arcLength_one_right (x : ℂ) : arcLength x 1 = |x.arg| := by simp [arcLength]
@[simp] lemma arcLength_mul_left (ha : a ≠ 0) (x y : ℂ) :
    arcLength (a * x) (a * y) = arcLength x y := by simp [arcLength, mul_div_mul_left _ _ ha]
@[simp] lemma arcLength_mul_right (ha : a ≠ 0) (x y : ℂ) :
    arcLength (x * a) (y * a) = arcLength x y := by simp [arcLength, mul_div_mul_right _ _ ha]

lemma arcLength_div_left_eq_arcLength_mul_right (a x y : ℂ) :
    arcLength (x / a) y = arcLength x (y * a) := by simp [arcLength, div_div, mul_comm]

lemma arcLength_div_right_eq_arcLength_mul_left (a x y : ℂ) :
    arcLength x (y / a) = arcLength (x * a) y := by
  rw [arcLength_comm, arcLength_div_left_eq_arcLength_mul_right, arcLength_comm]

lemma arg_exp_mul_I (θ : ℝ) :
    arg (exp (θ * I)) = toIocMod (mul_pos two_pos Real.pi_pos) (-π) θ := by
  convert arg_cos_add_sin_mul_I (θ := toIocMod (mul_pos two_pos Real.pi_pos) (-π) θ) _ using 2
  · rw [← exp_mul_I, eq_sub_of_add_eq $ toIocMod_add_toIocDiv_zsmul _ _ θ, ofReal_sub,
      ofReal_zsmul, ofReal_mul, ofReal_ofNat, exp_mul_I_periodic.sub_zsmul_eq]
  · convert toIocMod_mem_Ioc _ _ _
    ring

lemma arcLength_exp_exp (x y : ℝ) :
    arcLength (exp (x * I)) (exp (y * I)) =
      |toIocMod (mul_pos two_pos Real.pi_pos) (-π) (x - y)| := by
  simp_rw [arcLength, ← exp_sub, ← sub_mul, ← ofReal_sub, arg_exp_mul_I]

lemma arcLength_exp_one (x : ℝ) :
    arcLength (exp (x * I)) 1 = |toIocMod (mul_pos two_pos Real.pi_pos) (-π) x| := by
  simpa using arcLength_exp_exp x 0

end Complex
