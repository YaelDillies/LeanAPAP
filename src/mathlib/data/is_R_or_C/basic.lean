import data.is_R_or_C.basic

open_locale complex_conjugate

namespace is_R_or_C
variables {K : Type*} [is_R_or_C K] {x : K}

lemma inv_eq_conj (hx : ‖x‖ = 1) : x⁻¹ = conj x :=
inv_eq_of_mul_eq_one_left $ by rw [conj_mul, norm_sq_eq_def', hx, one_pow, algebra_map.coe_one]

end is_R_or_C
