import Mathlib.Data.IsROrC.Basic

open scoped ComplexConjugate

namespace IsROrC
variable {K : Type*} [IsROrC K] {x : K}

lemma mul_conj' (x : K) : x * conj x = (‖x‖ : K) ^ 2 := by rw [mul_conj, normSq_eq_def']; norm_cast
lemma conj_mul' (x : K) : conj x * x = (‖x‖ : K) ^ 2 := by rw [conj_mul, normSq_eq_def']; norm_cast

lemma inv_eq_conj (hx : ‖x‖ = 1) : x⁻¹ = conj x :=
  inv_eq_of_mul_eq_one_left $ by simp_rw [conj_mul', hx, algebraMap.coe_one, one_pow]

@[simp] lemma conj_div (x y : K) : conj (x / y) = conj x / conj y := map_div' conj conj_inv _ _

--TODO: Do we rather want the map as an explicit definition?
lemma exists_norm_eq_mul_self (x : K) : ∃ c, ‖c‖ = 1 ∧ ↑‖x‖ = c * x := by
  obtain rfl | hx := eq_or_ne x 0
  · exact ⟨1, by simp⟩
  · exact ⟨‖x‖ / x, by simp [norm_ne_zero_iff.2, hx]⟩

lemma exists_norm_mul_eq_self (x : K) : ∃ c, ‖c‖ = 1 ∧ c * ‖x‖ = x := by
  obtain rfl | hx := eq_or_ne x 0
  · exact ⟨1, by simp⟩
  · exact ⟨x / ‖x‖, by simp [norm_ne_zero_iff.2, hx]⟩

end IsROrC
