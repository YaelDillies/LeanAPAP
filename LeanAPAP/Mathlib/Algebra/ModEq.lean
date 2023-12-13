import Mathlib.Algebra.ModEq

namespace AddCommGroup
variable {α : Type*}

section AddCommGroupWithOne
variable [AddCommGroupWithOne α] [CharZero α] {a b : ℤ} {n : ℕ}

@[simp, norm_cast] lemma intCast_modEq_intCast' : a ≡ b [PMOD (n : α)] ↔ a ≡ b [PMOD (n : ℤ)] := by
  simpa using int_cast_modEq_int_cast (α := α) (z := n)

end AddCommGroupWithOne

variable [DivisionRing α] {a b c p : α}

@[simp] lemma div_modEq_div (hc : c ≠ 0) : a / c ≡ b / c [PMOD p] ↔ a ≡ b [PMOD (p * c)] := by
  simp [ModEq, ←sub_div, div_eq_iff hc, mul_assoc]

end AddCommGroup
