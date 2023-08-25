import Mathlib.Data.IsROrC.Basic

#align_import mathlib.data.is_R_or_C.basic

open scoped ComplexConjugate

namespace IsROrC
variable {K : Type*} [IsROrC K] {x : K}

lemma inv_eq_conj (hx : ‖x‖ = 1) : x⁻¹ = conj x :=
  inv_eq_of_mul_eq_one_left <| by rw [conj_mul, norm_sq_eq_def', hx, one_pow, algebraMap.coe_one]

--TODO: Do we rather want the map as an explicit definition?
lemma exists_norm_eq_mul_self (x : K) : ∃ c, ‖c‖ = 1 ∧ ↑‖x‖ = c * x := by
  obtain rfl | hx := eq_or_ne x 0
  · exact ⟨1, by simp⟩
  · exact ⟨‖x‖ / x, by simp [norm_ne_zero_iff.2, hx]⟩

lemma mul_conj' (x : K) : x * conj x = ‖x‖ ^ 2 := by rw [mul_conj, norm_sq_eq_def'] <;> norm_cast

lemma conj_mul' (x : K) : conj x * x = ‖x‖ ^ 2 := by rw [conj_mul, norm_sq_eq_def'] <;> norm_cast

@[simp]
lemma conj_div (x y : K) : conj (x / y) = conj x / conj y :=
  map_div' conj conj_inv _ _

end IsROrC
