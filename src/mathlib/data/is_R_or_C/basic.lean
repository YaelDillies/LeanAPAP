import data.is_R_or_C.basic

open_locale complex_conjugate

namespace is_R_or_C
variables {K : Type*} [is_R_or_C K] {x : K}

lemma inv_eq_conj (hx : ‖x‖ = 1) : x⁻¹ = conj x :=
inv_eq_of_mul_eq_one_left $ by rw [conj_mul, norm_sq_eq_def', hx, one_pow, algebra_map.coe_one]

--TODO: Do we rather want the map as an explicit definition?
lemma exists_norm_eq_mul_self (x : K) : ∃ c, ‖c‖ = 1 ∧ ↑‖x‖ = c * x :=
begin
  obtain rfl | hx := eq_or_ne x 0,
  { exact ⟨1, by simp⟩ },
  { exact ⟨‖x‖ / x, by simp [norm_ne_zero_iff.2, hx]⟩ }
end

end is_R_or_C
