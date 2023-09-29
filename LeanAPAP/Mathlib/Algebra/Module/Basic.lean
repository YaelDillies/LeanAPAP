import Mathlib.Algebra.Module.Basic

--TODO: Subsume `smul_eq_zero_iff_eq'`, `smul_eq_zero_iff_ne'`

section SMulWithZero
variable {R M : Type*} [Zero R] [Zero M] [SMulWithZero R M] [NoZeroSMulDivisors R M] {c : R} {x : M}

lemma smul_eq_zero_iff_left (hx : x ≠ 0) : c • x = 0 ↔ c = 0 := by simp [hx]
lemma smul_eq_zero_iff_right (hc : c ≠ 0) : c • x = 0 ↔ x = 0 := by simp [hc]
lemma smul_ne_zero_iff_left (hx : x ≠ 0) : c • x ≠ 0 ↔ c ≠ 0 := by simp [hx]
lemma smul_ne_zero_iff_right (hc : c ≠ 0) : c • x ≠ 0 ↔ x ≠ 0 := by simp [hc]

end SMulWithZero
