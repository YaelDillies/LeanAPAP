import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

open Set

namespace Real
variable {x : ℝ}

lemma sin_le (hx : 0 ≤ x) : sin x ≤ x := by
  suffices MonotoneOn (fun x ↦ x - sin x) (Ici 0) by simpa using this left_mem_Ici hx hx
  exact monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _) (Continuous.continuousOn $ by
    continuity) (fun x _ ↦ ((hasDerivAt_id _).sub $ hasDerivAt_sin _).hasDerivWithinAt) $ by
    simp [cos_le_one]

lemma cos_quadratic_lower_bound : 1 - x ^ 2 / 2 ≤ cos x := by
  wlog hx₀ : 0 ≤ x
  · simpa using this $ neg_nonneg.2 $ le_of_not_le hx₀
  suffices MonotoneOn (fun x ↦ cos x + x ^ 2 / 2) (Ici 0) by simpa using this left_mem_Ici hx₀ hx₀
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _) (Continuous.continuousOn $ by
    continuity) (fun x _ ↦
    ((hasDerivAt_cos ..).add $ (hasDerivAt_pow ..).div_const _).hasDerivWithinAt) fun x hx ↦ ?_
  simp [mul_div_cancel_left]
  exact sin_le $ interior_subset hx

/-- **Jordan's inequality**. -/
lemma two_div_pi_mul_le (hx₀ : 0 ≤ x) (hx : x ≤ π / 2) : 2 / π * x ≤ sin x := by
  rw [← sub_nonneg]
  suffices ConcaveOn ℝ (Icc 0 (π / 2)) (fun x ↦ sin x - 2 / π * x) by
    refine (le_min ?_ ?_).trans $ this.min_le_of_mem_Icc ⟨hx₀, hx⟩ <;> field_simp
  refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc ..)
    (Continuous.continuousOn $ by continuity)
    (fun x _ ↦ ((hasDerivAt_sin ..).sub $ (hasDerivAt_id ..).const_mul (2 / π)).hasDerivWithinAt)
    (fun x _ ↦ (hasDerivAt_cos ..).hasDerivWithinAt.sub_const _)
    fun x hx ↦ neg_nonpos.2 $ sin_nonneg_of_mem_Icc $ Icc_subset_Icc_right (by linarith) $
    interior_subset hx

lemma cos_quadratic_upper_bound (hx : |x| ≤ π) : cos x ≤ 1 - 2 / π ^ 2 * x ^ 2 := by
  wlog hx₀ : 0 ≤ x
  · simpa using this (by rwa [abs_neg]) $ neg_nonneg.2 $ le_of_not_le hx₀
  rw [abs_of_nonneg hx₀] at hx
  -- TODO: `compute_deriv` tactic?
  have hderiv (x) : HasDerivAt (fun x ↦ 1 - 2 / π ^ 2 * x ^ 2 - cos x) _ x :=
    (((hasDerivAt_pow ..).const_mul _).const_sub _).sub $ hasDerivAt_cos _
  simp only [Nat.cast_ofNat, Nat.succ_sub_succ_eq_sub, tsub_zero, pow_one, ← neg_sub', neg_sub,
    ← mul_assoc] at hderiv
  have hmono : MonotoneOn (fun x ↦ 1 - 2 / π ^ 2 * x ^ 2 - cos x) (Icc 0 (π / 2)) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc ..) (Continuous.continuousOn $
      by continuity) (fun x _ ↦ (hderiv _).hasDerivWithinAt) fun x hx ↦ sub_nonneg.2 ?_
    have ⟨hx₀, hx⟩ := interior_subset hx
    calc
      _ = 2 / π * (2 / π * x) := by ring
      _ ≤ 1 * sin x := by
          gcongr; exacts [div_le_one_of_le two_le_pi (by positivity), two_div_pi_mul_le hx₀ hx]
      _ = sin x := one_mul _
  have hconc : ConcaveOn ℝ (Icc (π / 2) π) (fun x ↦ 1 - 2 / π ^ 2 * x ^ 2 - cos x) := by
    refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc ..)
      (Continuous.continuousOn $ by continuity) (fun x _ ↦ (hderiv _).hasDerivWithinAt)
      (fun x _ ↦ ((hasDerivAt_sin ..).sub $ (hasDerivAt_id ..).const_mul _).hasDerivWithinAt)
      fun x hx ↦ ?_
    have ⟨hx, hx'⟩ := interior_subset hx
    calc
      _ ≤ (0 : ℝ) - 0 := by
          gcongr
          · exact cos_nonpos_of_pi_div_two_le_of_le hx $ hx'.trans $ by linarith
          · positivity
      _ = 0 := sub_zero _
  rw [← sub_nonneg]
  obtain hx' | hx' := le_total x (π / 2)
  · simpa using hmono (left_mem_Icc.2 $ by positivity) ⟨hx₀, hx'⟩ hx₀
  · refine (le_min ?_ ?_).trans $ hconc.min_le_of_mem_Icc ⟨hx', hx⟩ <;> field_simp <;> norm_num
