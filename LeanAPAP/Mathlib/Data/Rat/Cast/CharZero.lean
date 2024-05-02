import Mathlib.Data.NNRat.Lemmas
import Mathlib.Data.Rat.Cast.Defs
import LeanAPAP.Mathlib.Data.NNRat.Defs

open Function

variable {F ι α β : Type*}

namespace NNRat
section DivisionSemiring
variable [DivisionSemiring α] [CharZero α] {p q : ℚ≥0}

lemma cast_injective : Injective ((↑) : ℚ≥0 → α) := by
  rintro p q hpq
  rw [NNRat.cast_def, NNRat.cast_def, Commute.div_eq_div_iff] at hpq
  rw [← p.num_div_den, ← q.num_div_den, div_eq_div_iff]
  norm_cast at hpq ⊢
  any_goals norm_cast
  any_goals positivity
  exact Nat.cast_commute _ _

@[simp, norm_cast] lemma cast_inj : (p : α) = q ↔ p = q := cast_injective.eq_iff

@[simp, norm_cast] lemma cast_eq_zero : (q : α) = 0 ↔ q = 0 := by rw [← cast_zero, cast_inj]
lemma cast_ne_zero : (q : α) ≠ 0 ↔ q ≠ 0 := cast_eq_zero.not

@[simp, norm_cast]
lemma cast_add (p q) : (p + q : ℚ≥0) = (p + q : α) :=
  cast_add_of_ne_zero (Nat.cast_ne_zero.2 p.den_pos.ne') (Nat.cast_ne_zero.2 q.den_pos.ne')

@[simp, norm_cast]
lemma cast_mul (p q) : (p * q : ℚ≥0) = (p * q : α) :=
  cast_mul_of_ne_zero (Nat.cast_ne_zero.2 p.den_pos.ne') (Nat.cast_ne_zero.2 q.den_pos.ne')

variable (α) in
/-- Coercion `ℚ≥0 → α` as a `RingHom`. -/
def castHom : ℚ≥0 →+* α where
  toFun := (↑)
  map_one' := cast_one
  map_mul' := cast_mul
  map_zero' := cast_zero
  map_add' := cast_add

@[simp, norm_cast] lemma coe_castHom : ⇑(castHom α) = (↑) := rfl

@[simp, norm_cast]
lemma cast_pow (q : ℚ≥0) (n : ℕ) : ↑(q ^ n) = (q : α) ^ n := (castHom α).map_pow _ _

@[simp, norm_cast]
lemma cast_zpow (q : ℚ≥0) (n : ℤ) : ↑(q ^ n) = ((q : α) ^ n : α) := map_zpow₀ (castHom α) _ _

@[simp, norm_cast] lemma cast_inv (p) : (p⁻¹ : ℚ≥0) = (p : α)⁻¹ := map_inv₀ (castHom α) _
@[simp, norm_cast] lemma cast_div (p q) : (p / q : ℚ≥0) = (p / q : α) := map_div₀ (castHom α) _ _

@[simp, norm_cast]
lemma cast_divNat (a b : ℕ) : (divNat a b : α) = a / b := sorry

end DivisionSemiring
end NNRat
