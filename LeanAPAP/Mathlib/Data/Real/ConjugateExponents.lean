import Mathlib.Data.Real.ConjugateExponents

/-!
## TODO

Change everything to using `x⁻¹` instead of `1 / x`.
-/

open scoped ENNReal

namespace Real.IsConjugateExponent
variable {p q : ℝ} (h : p.IsConjugateExponent q)

attribute [mk_iff] IsConjugateExponent

lemma inv_add_inv_conj' : p⁻¹ + q⁻¹ = 1 := by simpa only [one_div] using h.inv_add_inv_conj

lemma one_sub_inv : 1 - p⁻¹ = q⁻¹ := sub_eq_of_eq_add' h.inv_add_inv_conj'.symm
lemma inv_sub_one : p⁻¹ - 1 = -q⁻¹ := by rw [← h.inv_add_inv_conj', sub_add_cancel']

lemma inv_add_inv_conj_nnreal' : p.toNNReal⁻¹ + q.toNNReal⁻¹ = 1 := by
  simpa only [one_div] using h.inv_add_inv_conj_nnreal

lemma inv_add_inv_conj_ennreal' : (ENNReal.ofReal p)⁻¹ + (ENNReal.ofReal q)⁻¹ = 1 := by
  simpa only [one_div] using h.inv_add_inv_conj_ennreal

end Real.IsConjugateExponent

namespace NNReal

/-- Two nonnegative real exponents `p, q` are conjugate if they are `> 1` and satisfy the equality
`1/p + 1/q = 1`. This condition shows up in many theorems in analysis, notably related to `L^p`
norms. -/
@[mk_iff, pp_dot]
structure IsConjExponent (p q : ℝ≥0) : Prop where
  one_lt : 1 < p
  inv_add_inv_conj : p⁻¹ + q⁻¹ = 1

/-- The conjugate exponent of `p` is `q = p/(p-1)`, so that `1/p + 1/q = 1`. -/
noncomputable def conjExponent (p : ℝ≥0) : ℝ≥0 := p / (p - 1)

variable {a b p q : ℝ≥0} (h : p.IsConjExponent q)

@[simp, norm_cast]
lemma isConjugateExponent_coe : (p : ℝ).IsConjugateExponent q ↔ p.IsConjExponent q := by
  simp [Real.IsConjugateExponent_iff, IsConjExponent_iff]; norm_cast

alias ⟨_, IsConjExponent.coe⟩ := isConjugateExponent_coe

lemma isConjExponent_iff (h : 1 < p) : p.IsConjExponent q ↔ q = p / (p - 1) := by
  rw [← isConjugateExponent_coe, Real.isConjugateExponent_iff (mod_cast h), ← NNReal.coe_eq,
    NNReal.coe_div, NNReal.coe_sub h.le, NNReal.coe_one]

namespace IsConjExponent

/- Register several non-vanishing results following from the fact that `p` has a conjugate exponent
`q`: many computations using these exponents require clearing out denominators, which can be done
with `field_simp` given a proof that these denominators are non-zero, so we record the most usual
ones. -/
lemma one_le : 1 ≤ p := h.one_lt.le
lemma pos : 0 < p := zero_lt_one.trans h.one_lt
lemma ne_zero : p ≠ 0 := h.pos.ne'

lemma sub_one_pos : 0 < p - 1 := tsub_pos_of_lt h.one_lt
lemma sub_one_ne_zero : p - 1 ≠ 0 := h.sub_one_pos.ne'

lemma inv_pos : 0 < p⁻¹ := _root_.inv_pos.2 h.pos
lemma inv_ne_zero : p⁻¹ ≠ 0 := h.inv_pos.ne'

lemma one_sub_inv : 1 - p⁻¹ = q⁻¹ := tsub_eq_of_eq_add_rev h.inv_add_inv_conj.symm

protected lemma conjExponent (h : 1 < p) : p.IsConjExponent (conjExponent p) :=
  (isConjExponent_iff h).2 rfl

lemma conj_eq : q = p / (p - 1) := by
  simpa only [← NNReal.coe_one, ← NNReal.coe_sub h.one_le, ← NNReal.coe_div, NNReal.coe_eq]
    using h.coe.conj_eq

-- TODO: Rename `Real` version
lemma conjExponent_eq : conjExponent p = q := h.conj_eq.symm

lemma sub_one_mul_conj : (p - 1) * q = p :=
  mul_comm q (p - 1) ▸ (eq_div_iff h.sub_one_ne_zero).1 h.conj_eq

lemma mul_eq_add : p * q = p + q := by
  simpa only [← NNReal.coe_mul, ← NNReal.coe_add, NNReal.coe_eq] using h.coe.mul_eq_add

@[symm]
protected lemma symm : q.IsConjExponent p where
  one_lt := by
      rw [h.conj_eq]
      exact (one_lt_div h.sub_one_pos).mpr (tsub_lt_self h.pos zero_lt_one)
  inv_add_inv_conj := by simpa [add_comm] using h.inv_add_inv_conj

lemma div_conj_eq_sub_one : p / q = p - 1 := by field_simp [h.symm.ne_zero]; rw [h.sub_one_mul_conj]

lemma inv_add_inv_conj_ennreal : (p⁻¹ + q⁻¹ : ℝ≥0∞) = 1 := by norm_cast; exact h.inv_add_inv_conj

protected lemma inv_inv (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b = 1) :
    a⁻¹.IsConjExponent b⁻¹ :=
  ⟨one_lt_inv ha.bot_lt $ by rw [← hab]; exact lt_add_of_pos_right _ hb.bot_lt, by
    simpa only [inv_inv] using hab⟩

lemma inv_one_sub_inv (ha₀ : a ≠ 0) (ha₁ : a < 1) : a⁻¹.IsConjExponent (1 - a)⁻¹ :=
  .inv_inv ha₀ (tsub_pos_of_lt ha₁).ne' $ add_tsub_cancel_of_le ha₁.le

lemma one_sub_inv_inv (ha₀ : a ≠ 0) (ha₁ : a < 1) : (1 - a)⁻¹.IsConjExponent a⁻¹ :=
  (inv_one_sub_inv ha₀ ha₁).symm

end IsConjExponent
end NNReal
