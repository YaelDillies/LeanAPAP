import Mathlib.Algebra.Group.Basic
import Aesop

section CancelCommMonoid
variable {α : Type*} [CancelCommMonoid α] {a b c d : α}

@[to_additive] lemma eq_iff_eq_of_mul_eq_mul (h : a * b = c * d) : a = c ↔ b = d := by aesop
@[to_additive] lemma ne_iff_ne_of_mul_eq_mul (h : a * b = c * d) : a ≠ c ↔ b ≠ d := by aesop

end CancelCommMonoid
