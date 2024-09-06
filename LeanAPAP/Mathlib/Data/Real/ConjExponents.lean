import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Real.ConjExponents
import LeanAPAP.Mathlib.Data.ENNReal.Operations

open scoped NNReal

namespace ENNReal

/-- Two nonnegative real exponents `p, q` are conjugate if they are `> 1` and satisfy the equality
`1/p + 1/q = 1`. This condition shows up in many theorems in analysis, notably related to `L^p`
norms. -/
@[mk_iff]
structure IsConjExponent (p q : ℝ≥0∞) : Prop where
  inv_add_inv_conj : p⁻¹ + q⁻¹ = 1

/-- The conjugate exponent of `p` is `q = p/(p - 1)`, so that `1/p + 1/q = 1`. -/
noncomputable def conjExponent (p : ℝ≥0∞) : ℝ≥0∞ := 1 + (p - 1)⁻¹

variable {a b p q : ℝ≥0∞} (h : p.IsConjExponent q)

@[simp, norm_cast] lemma isConjExponent_coe {p q : ℝ≥0} :
    IsConjExponent p q ↔ p.IsConjExponent q := by
  simp [NNReal.isConjExponent_iff, isConjExponent_iff]; sorry

alias ⟨_, _root_.NNReal.IsConjExponent.coe_ennreal⟩ := isConjExponent_coe

namespace IsConjExponent

/- Register several non-vanishing results following from the fact that `p` has a conjugate exponent
`q`: many computations using these exponents require clearing out denominators, which can be done
with `field_simp` given a proof that these denominators are non-zero, so we record the most usual
ones. -/

section
include h

lemma one_le : 1 ≤ p := ENNReal.inv_le_one.1 $ by
  rw [← add_zero p⁻¹, ← h.inv_add_inv_conj]; gcongr; positivity

lemma pos : 0 < p := zero_lt_one.trans_le h.one_le
lemma ne_zero : p ≠ 0 := h.pos.ne'

lemma one_sub_inv : 1 - p⁻¹ = q⁻¹ :=
  ENNReal.sub_eq_of_eq_add_rev' one_ne_top h.inv_add_inv_conj.symm

lemma conj_eq : q = 1 + (p - 1)⁻¹ := sorry

lemma conjExponent_eq : conjExponent p = q := h.conj_eq.symm

lemma mul_eq_add : p * q = p + q := sorry

@[symm]
protected lemma symm : q.IsConjExponent p where
  inv_add_inv_conj := by simpa [add_comm] using h.inv_add_inv_conj

lemma div_conj_eq_sub_one : p / q = p - 1 := sorry

end

protected lemma inv_inv (hab : a + b = 1) : a⁻¹.IsConjExponent b⁻¹ where
  inv_add_inv_conj := by simpa only [inv_inv] using hab

lemma inv_one_sub_inv (ha : a ≤ 1) : a⁻¹.IsConjExponent (1 - a)⁻¹ :=
  .inv_inv <| add_tsub_cancel_of_le ha

lemma one_sub_inv_inv (ha : a ≤ 1) : (1 - a)⁻¹.IsConjExponent a⁻¹ := (inv_one_sub_inv ha).symm

lemma top_one : IsConjExponent ∞ 1 := sorry
lemma one_top : IsConjExponent 1 ∞ := sorry

end IsConjExponent

lemma isConjExponent_iff_eq_conjExponent (h : 1 < p) : p.IsConjExponent q ↔ q = 1 + (p - 1)⁻¹ :=
  sorry

protected lemma IsConjExponent.conjExponent (h : 1 < p) : p.IsConjExponent (conjExponent p) :=
  (isConjExponent_iff_eq_conjExponent h).2 rfl

end ENNReal
