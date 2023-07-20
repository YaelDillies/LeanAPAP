import mathlib.algebra.group_power.order
import mathlib.analysis.normed.field.basic
import mathlib.group_theory.order_of_element
import mathlib.linear_algebra.finite_dimensional
import number_theory.legendre_symbol.add_character
import prereqs.lp_norm
/-!
### TODO

Rename `exists_pow_eq_one` to `is_of_fin_order_of_finite`
-/

open finset
open_locale big_operators complex_conjugate

variables {G R : Type*}

namespace add_char
section add_monoid
variables [add_monoid G] [comm_monoid R] {ψ : add_char G R}

lemma eq_one_iff : ψ = 1 ↔ ∀ x, ψ x = 1 := fun_like.ext_iff
lemma ne_one_iff : ψ ≠ 1 ↔ ∃ x, ψ x ≠ 1 := fun_like.ne_iff

noncomputable instance : decidable_eq (add_char G R) := classical.dec_eq _

end add_monoid

section add_group
variables [add_group G]

section normed_field
variables [finite G] [normed_field R]

@[simp] lemma norm_apply (ψ : add_char G R) (x : G) : ‖ψ x‖ = 1 :=
(ψ.is_of_fin_order $ exists_pow_eq_one _).norm_eq_one

@[simp] lemma coe_ne_zero (ψ : add_char G R) : (ψ : G → R) ≠ 0 :=
function.ne_iff.2 ⟨0, λ h, by simpa [h] using ψ.norm_apply 0⟩

end normed_field

section is_R_or_C
variables [is_R_or_C R]

lemma inv_apply_eq_conj [finite G] (ψ : add_char G R) (x : G) : (ψ x)⁻¹ = conj (ψ x) :=
inv_eq_of_mul_eq_one_right $ by simp [is_R_or_C.mul_conj, is_R_or_C.norm_sq_eq_def']

@[simp] lemma L2inner_self [fintype G] (ψ : add_char G R) : ⟪(ψ : G → R), ψ⟫_[R] = fintype.card G :=
L2inner_self_of_norm_eq_one ψ.norm_apply

end is_R_or_C

variables [fintype G] [comm_semiring R] [is_domain R] [char_zero R] {ψ : add_char G R}

lemma sum_eq_zero_iff_ne_one : ∑ x, ψ x = 0 ↔ ψ ≠ 1 :=
begin
  refine ⟨_, λ h, _⟩,
  { rintro h rfl,
    simpa [card_univ, fintype.card_ne_zero] using h },
  obtain ⟨x, hx⟩ := ne_one_iff.1 h,
  refine eq_zero_of_mul_eq_self_left hx _,
  rw finset.mul_sum,
  exact fintype.sum_equiv (equiv.add_left x) _ _ (λ y, (map_add_mul _ _ _).symm),
end

lemma sum_ne_zero_iff_eq_one : ∑ x, ψ x ≠ 0 ↔ ψ = 1 := sum_eq_zero_iff_ne_one.not_left

end add_group

section add_comm_group
variables [add_comm_group G]

section division_comm_monoid
variables [division_comm_monoid R]

lemma map_neg_eq_inv (ψ : add_char G R) (x : G) : ψ (-x) = (ψ x)⁻¹ :=
eq_inv_of_mul_eq_one_left $ by simp [←map_add_mul]

lemma inv_apply' (ψ : add_char G R) (x : G) : ψ⁻¹ x = (ψ x)⁻¹ := map_neg_eq_inv _ _

end division_comm_monoid

section is_R_or_C
variables [is_R_or_C R] {ψ₁ ψ₂ : add_char G R}

lemma L2inner_eq [fintype G] (ψ₁ ψ₂ : add_char G R) :
  ⟪(ψ₁ : G → R), ψ₂⟫_[R] = if ψ₁ = ψ₂ then fintype.card G else 0 :=
begin
  split_ifs,
  { rw [h, L2inner_self] },
  have : ψ₁⁻¹ * ψ₂ ≠ 1, { rwa [ne.def, inv_mul_eq_one] },
  simp_rw [L2inner_eq_sum, ←inv_apply_eq_conj],
  simpa [inv_apply'] using sum_eq_zero_iff_ne_one.2 this,
end

lemma L2inner_eq_zero_iff_ne [fintype G] : ⟪(ψ₁ : G → R), ψ₂⟫_[R] = 0 ↔ ψ₁ ≠ ψ₂ :=
by rw [L2inner_eq, ne.ite_eq_right_iff (nat.cast_ne_zero.2 fintype.card_ne_zero)]; apply_instance

lemma L2inner_eq_card_iff_eq [fintype G] : ⟪(ψ₁ : G → R), ψ₂⟫_[R] = fintype.card G ↔ ψ₁ = ψ₂ :=
by rw [L2inner_eq, ne.ite_eq_left_iff (nat.cast_ne_zero.2 fintype.card_ne_zero)]; apply_instance

protected lemma linear_independent [finite G] :
  linear_independent R (coe_fn : add_char G R → G → R) :=
begin
  casesI nonempty_fintype G,
  exact linear_independent_of_ne_zero_of_L2inner_eq_zero add_char.coe_ne_zero
    (λ ψ₁ ψ₂, L2inner_eq_zero_iff_ne.2),
end

noncomputable instance fintype_add_char [finite G] : fintype (add_char G ℂ) :=
@fintype.of_finite _
  (add_char.linear_independent : linear_independent ℂ (coe_fn : add_char G ℂ → G → ℂ)).finite'

end is_R_or_C
end add_comm_group
end add_char
