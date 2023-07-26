import mathlib.number_theory.legendre_symbol.add_char.duality
import prereqs.convolution.basic

/-!
# Discrete Fourier transform

This file defines the discrete Fourier transform and shows the Parseval-Plancherel identity and
Fourier inversion formula for it.
-/

open add_char finset fintype (card) function.
open_locale big_operators complex_conjugate

variables {α : Type*} [add_comm_group α] [fintype α] {f : α → ℂ} {ψ : add_char α ℂ} {n : ℕ}

/-- The discrete Fourier transform. -/
def dft (f : α → ℂ) : add_char α ℂ → ℂ := λ ψ, ⟪ψ, f⟫_[ℂ]

lemma dft_apply (f : α → ℂ) (ψ : add_char α ℂ) : dft f ψ = ⟪ψ, f⟫_[ℂ] := rfl

@[simp] lemma dft_zero : dft (0 : α → ℂ) = 0 := by ext; simp [dft_apply]

@[simp] lemma dft_add (f g : α → ℂ) : dft (f + g) = dft f + dft g :=
by ext : 1; simp [L2inner_add_right, dft_apply]

@[simp] lemma dft_sub (f g : α → ℂ) : dft (f - g) = dft f - dft g :=
by ext : 1; simp [L2inner_sub_right, dft_apply]

/-- **Parseval-Plancherel identity** for the discrete Fourier transform. -/
@[simp] lemma L2inner_dft (f g : α → ℂ) : ⟪dft f, dft g⟫_[ℂ] = card α * ⟪f, g⟫_[ℂ] :=
begin
  classical,
  simp_rw [dft, L2inner_eq_sum, map_sum, map_mul, star_ring_end_self_apply, sum_mul,
    mul_sum, @sum_comm _ _ (add_char _ _), mul_mul_mul_comm _ (conj $ f _), ←sum_mul,
    ←add_char.inv_apply_eq_conj, ←map_neg_eq_inv, ←map_add_mul, add_char.sum_apply, add_neg_eq_zero,
    ite_mul, zero_mul, fintype.sum_ite_eq],
end

/-- **Parseval-Plancherel identity** for the discrete Fourier transform. -/
lemma L2norm_dft_sq (f : α → ℂ) : ‖dft f‖_[2] ^ 2 = card α * ‖f‖_[2] ^ 2 :=
complex.of_real_injective $ by push_cast; simpa only [L2inner_self] using L2inner_dft f f

/-- **Parseval-Plancherel identity** for the discrete Fourier transform. -/
@[simp] lemma L2norm_dft (f : α → ℂ) : ‖dft f‖_[2] = real.sqrt (card α) * ‖f‖_[2] :=
by simpa using congr_arg real.sqrt (L2norm_dft_sq f)

/-- **Fourier inversion** for the discrete Fourier transform. -/
lemma dft_inversion (f : α → ℂ) (a : α) : ∑ ψ : add_char α ℂ, dft f ψ * ψ a = card α * f a :=
begin
  classical,
  simp_rw [dft, L2inner_eq_sum, sum_mul, @sum_comm _ α, mul_right_comm _ (f _), ←sum_mul,
    ←add_char.inv_apply_eq_conj, inv_mul_eq_div, ←map_sub_eq_div, add_char.sum_apply, sub_eq_zero,
    ite_mul, zero_mul, fintype.sum_ite_eq],
end

lemma dft_inv (ψ : add_char α ℂ) (hf : is_self_adjoint f) : dft f ψ⁻¹ = conj (dft f ψ) :=
by simp_rw [dft_apply, L2inner_eq_sum, map_sum, add_char.inv_apply', map_mul,
  add_char.inv_apply_eq_conj, complex.conj_conj, (hf.apply _).conj_eq]

@[simp] lemma dft_balance (f : α → ℂ) (hψ : ψ ≠ 1) : dft (balance f) ψ = dft f ψ :=
begin
  simp only [dft_apply, L2inner_eq_sum, balance, mul_sub, sum_sub_distrib],
  rw [←sum_mul, ←map_sum, sum_eq_zero_iff_ne_one.2 hψ, map_zero, zero_mul, sub_zero],
end

lemma dft_dilate (f : α → ℂ) (ψ : add_char α ℂ) (hn : n.coprime (card α)) :
  dft (dilate f n) ψ = dft f (ψ ^ n) :=
begin
  simp_rw [dft_apply, L2inner_eq_sum, dilate],
  refine sum_nbij' ((•) (n⁻¹ : zmod (card α)).val) _ (λ x hx, _) ((•) n) _ _ _,
  { simp only [mem_univ, forall_const] },
  { rw [pow_apply, ←map_nsmul_pow, nsmul_zmod_val_inv_nsmul hn] },
  all_goals { simp only [hn, mem_univ, nsmul_zmod_val_inv_nsmul, zmod_val_inv_nsmul_nsmul,
    eq_self_iff_true, forall_const] },
end

variables [decidable_eq α]

@[simp] lemma dft_indicate_one (A : finset α) : dft (𝟭 A) 1 = A.card :=
begin
  rw [dft_apply, L2inner_eq_sum, ←sum_indicate],
  simp only [monoid_hom.one_apply, coe_one_unit_sphere, map_one, one_mul],
end

lemma dft_conv_apply (f g : α → ℂ) (ψ : add_char α ℂ) : dft (f ∗ g) ψ = dft f ψ * dft g ψ :=
begin
  simp_rw [dft, L2inner_eq_sum, conv_eq_sum_sub', mul_sum, sum_mul, ←sum_product',
    univ_product_univ],
  refine sum_nbij' (λ x, (x.1 - x.2, x.2)) (by simp) (λ x _, _) (λ x, (x.1 + x.2, x.2))
    (by simp) (by simp) (by simp),
  rw [mul_mul_mul_comm, ←map_mul, ←map_add_mul, add_sub_cancel'_right],
end

@[simp] lemma dft_conv (f g : α → ℂ) : dft (f ∗ g) = dft f * dft g := funext $ dft_conv_apply _ _
