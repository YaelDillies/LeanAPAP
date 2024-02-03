import Mathlib.Data.Int.CharZero
import LeanAPAP.Mathlib.Data.Rat.Order
import LeanAPAP.Mathlib.Data.Rat.NNRat
import LeanAPAP.Prereqs.NNRat.Cast.Defs

/-!
# Casts of nonnegative rational numbers into characteristic zero semifields
-/

open Function
open scoped NNRat

variable {F ι α β : Type*}

namespace NNRat
section DivisionSemiring
variable [DivisionSemiring α] [CharZero α] {p q : ℚ≥0}

lemma cast_injective : Injective ((↑) : ℚ≥0 → α) := by
  rintro p q (hpq : _ / _ = _ / _)
  rw [Commute.div_eq_div_iff] at hpq
  rw [← p.num_div_den, ← q.num_div_den, div_eq_div_iff]
  norm_cast at hpq ⊢
  any_goals norm_cast
  any_goals positivity
  exact Nat.cast_commute _ _

@[simp, norm_cast] lemma cast_inj : (p : α) = q ↔ p = q := cast_injective.eq_iff

@[simp, norm_cast]
lemma cast_eq_zero {q : ℚ≥0} : (q : α) = 0 ↔ q = 0 := by rw [← cast_zero, cast_inj]

lemma cast_ne_zero {q : ℚ≥0} : (q : α) ≠ 0 ↔ q ≠ 0 := cast_eq_zero.not

@[simp, norm_cast]
lemma cast_add (p q) : (p + q : ℚ≥0) = (p + q : α) :=
  cast_add_of_ne_zero (Nat.cast_ne_zero.2 p.den_pos.ne') (Nat.cast_ne_zero.2 q.den_pos.ne')

@[simp, norm_cast]
lemma cast_mul (p q) : (p * q : ℚ≥0) = (p * q : α) :=
  cast_mul_of_ne_zero (Nat.cast_ne_zero.2 p.den_pos.ne') (Nat.cast_ne_zero.2 q.den_pos.ne')

@[simp, norm_cast]
lemma cast_inv (p) : (p⁻¹ : ℚ≥0) = (p : α)⁻¹ :=
  cast_inv_of_ne_zero (Nat.cast_ne_zero.2 p.den_pos.ne')

@[simp, norm_cast]
lemma cast_div (p q) : (p / q : ℚ≥0) = (p / q : α) :=
  cast_div_of_ne_zero (Nat.cast_ne_zero.2 p.den_pos.ne') (Nat.cast_ne_zero.2 q.den_pos.ne')

section

set_option linter.deprecated false

@[simp, norm_cast] lemma cast_bit0 (q : ℚ≥0) : ↑(bit0 q) = (bit0 q : α) := cast_add _ _

@[simp, norm_cast] lemma cast_bit1 (q : ℚ≥0) : ↑(bit1 q) = (bit1 q : α) := by
  rw [bit1, cast_add, cast_one, cast_bit0]; rfl

end

variable (α) in
/-- Coercion `ℚ≥0 → α` as a `RingHom`. -/
def castHom : ℚ≥0 →+* α where
  toFun := (↑)
  map_one' := cast_one
  map_mul' := cast_mul
  map_zero' := cast_zero
  map_add' := cast_add

@[simp, norm_cast] lemma coe_cast_hom : ⇑(castHom α) = (↑) := rfl

@[simp, norm_cast]
lemma cast_zpow (q : ℚ≥0) (n : ℤ) : ↑(q ^ n) = ((q : α) ^ n : α) := map_zpow₀ (castHom α) _ _

-- @[norm_cast]
-- lemma cast_mk (a b : ℤ) : (a /. b : α) = a / b := by
--   simp only [divInt_eq_div, cast_div, cast_coe_int]

@[simp, norm_cast]
lemma cast_pow (q : ℚ≥0) (n : ℕ) : ↑(q ^ n) = (q : α) ^ n := (castHom α).map_pow _ _

end DivisionSemiring
end NNRat
