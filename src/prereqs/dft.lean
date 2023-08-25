import mathlib.algebra.big_operators.ring
import mathlib.logic.basic
import mathlib.number_theory.legendre_symbol.add_char.duality
import prereqs.convolution.basic

/-!
# Discrete Fourier transform

This file defines the discrete Fourier transform and shows the Parseval-Plancherel identity and
Fourier inversion formula for it.
-/

open add_char finset fintype (card) function.
open_locale big_operators complex_conjugate complex_order

variables {α γ : Type*} [add_comm_group α] [fintype α] {f : α → ℂ} {ψ : add_char α ℂ} {n : ℕ}

/-- The discrete Fourier transform. -/
def dft (f : α → ℂ) : add_char α ℂ → ℂ := λ ψ, ⟪ψ, f⟫_[ℂ]

lemma dft_apply (f : α → ℂ) (ψ : add_char α ℂ) : dft f ψ = ⟪ψ, f⟫_[ℂ] := rfl

@[simp] lemma dft_zero : dft (0 : α → ℂ) = 0 := by ext; simp [dft_apply]

@[simp] lemma dft_add (f g : α → ℂ) : dft (f + g) = dft f + dft g :=
by ext : 1; simp [L2inner_add_right, dft_apply]

@[simp] lemma dft_sub (f g : α → ℂ) : dft (f - g) = dft f - dft g :=
by ext : 1; simp [L2inner_sub_right, dft_apply]

@[simp] lemma dft_const (a : ℂ) (hψ : ψ ≠ 0) : dft (const α a) ψ = 0 :=
by simp only [dft_apply, L2inner_eq_sum, const_apply, ←sum_mul, ←map_sum,
  sum_eq_zero_iff_ne_zero.2 hψ, map_zero, zero_mul]

@[simp] lemma dft_smul [distrib_smul γ ℂ] [has_star γ] [star_module γ ℂ] [smul_comm_class γ ℂ ℂ]
  (c : γ) (f : α → ℂ) : dft (c • f) = c • dft f :=
by ext : 1; simp [L2inner_smul_right, dft_apply]

/-- **Parseval-Plancherel identity** for the discrete Fourier transform. -/
@[simp] lemma L2inner_dft (f g : α → ℂ) : ⟪dft f, dft g⟫_[ℂ] = card α * ⟪f, g⟫_[ℂ] :=
begin
  classical,
  simp_rw [dft, L2inner_eq_sum, map_sum, map_mul, star_ring_end_self_apply, sum_mul,
    mul_sum, @sum_comm _ _ (add_char _ _), mul_mul_mul_comm _ (conj $ f _), ←sum_mul,
    ←add_char.inv_apply_eq_conj, ←map_neg_eq_inv, ←map_add_mul, add_char.sum_apply_eq_ite,
    add_neg_eq_zero, ite_mul, zero_mul, fintype.sum_ite_eq],
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
    ←add_char.inv_apply_eq_conj, inv_mul_eq_div, ←map_sub_eq_div, add_char.sum_apply_eq_ite,
    sub_eq_zero, ite_mul, zero_mul, fintype.sum_ite_eq],
end

lemma dft_dft_double_dual_emb (f : α → ℂ) (a : α) :
  dft (dft f) (double_dual_emb a) = card α * f (-a) :=
by simp only [←dft_inversion, mul_comm (conj _), dft_apply, L2inner_eq_sum,
  map_neg_eq_inv, add_char.inv_apply_eq_conj, double_dual_emb_apply]

lemma dft_dft (f : α → ℂ) : dft (dft f) = card α * (f ∘ double_dual_equiv.symm ∘ has_neg.neg) :=
funext $ λ a, by simp_rw [pi.mul_apply, function.comp_app, map_neg, pi.nat_apply,
  ←dft_dft_double_dual_emb, double_dual_emb_double_dual_equiv_symm_apply]

lemma dft_injective : injective (dft : (α → ℂ) → add_char α ℂ → ℂ) :=
λ f g h, funext $ λ a, mul_right_injective₀ (nat.cast_ne_zero.2 fintype.card_ne_zero) $
    (dft_inversion _ _).symm.trans $ by rw [h, dft_inversion]

lemma dft_inv (ψ : add_char α ℂ) (hf : is_self_adjoint f) : dft f ψ⁻¹ = conj (dft f ψ) :=
by simp_rw [dft_apply, L2inner_eq_sum, map_sum, add_char.inv_apply', map_mul,
  add_char.inv_apply_eq_conj, complex.conj_conj, (hf.apply _).conj_eq]

@[simp] lemma dft_conj (f : α → ℂ) (ψ : add_char α ℂ) : dft (conj f) ψ = conj (dft f ψ⁻¹) :=
by simp only [dft_apply, L2inner_eq_sum, map_sum, map_mul, ←inv_apply', ←inv_apply_eq_conj, inv_inv,
  pi.conj_apply]

lemma dft_conjneg_apply (f : α → ℂ) (ψ : add_char α ℂ) : dft (conjneg f) ψ = conj (dft f ψ) :=
begin
  simp only [dft_apply, L2inner_eq_sum, conjneg_apply, map_sum, map_mul, is_R_or_C.conj_conj],
  refine equiv.sum_comp' (equiv.neg _) _ _ (λ i, _),
  simp only [equiv.neg_apply, ←inv_apply_eq_conj, ←inv_apply', inv_apply],
end

@[simp] lemma dft_conjneg (f : α → ℂ) : dft (conjneg f) = conj (dft f) :=
funext $ dft_conjneg_apply _

@[simp] lemma dft_balance (f : α → ℂ) (hψ : ψ ≠ 0) : dft (balance f) ψ = dft f ψ :=
by simp only [balance, pi.sub_apply, dft_sub, dft_const _ hψ, sub_zero]

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

@[simp] lemma dft_triv_char [decidable_eq α] : dft (triv_char : α → ℂ) = 1 :=
by ext ψ : 1; simp [triv_char_apply, dft_apply, L2inner_eq_sum, ←map_sum]

@[simp] lemma dft_one : dft (1 : α → ℂ) = card α • triv_char :=
dft_injective $ by classical; rw [dft_smul, dft_triv_char, dft_dft, pi.one_comp, nsmul_eq_mul]

variables [decidable_eq α]

@[simp] lemma dft_indicate_zero (A : finset α) : dft (𝟭 A) 0 = A.card :=
by simp only [dft_apply, L2inner_eq_sum, sum_indicate, add_char.zero_apply, map_one, one_mul]

lemma dft_conv_apply (f g : α → ℂ) (ψ : add_char α ℂ) : dft (f ∗ g) ψ = dft f ψ * dft g ψ :=
begin
  simp_rw [dft, L2inner_eq_sum, conv_eq_sum_sub', mul_sum, sum_mul, ←sum_product',
    univ_product_univ],
  refine sum_nbij' (λ x, (x.1 - x.2, x.2)) (by simp) (λ x _, _) (λ x, (x.1 + x.2, x.2))
    (by simp) (by simp) (by simp),
  rw [mul_mul_mul_comm, ←map_mul, ←map_add_mul, add_sub_cancel'_right],
end

lemma dft_dconv_apply (f g : α → ℂ) (ψ : add_char α ℂ) : dft (f ○ g) ψ = dft f ψ * conj (dft g ψ) :=
by rw [←conv_conjneg, dft_conv_apply, dft_conjneg_apply]

@[simp] lemma dft_conv (f g : α → ℂ) : dft (f ∗ g) = dft f * dft g := funext $ dft_conv_apply _ _
@[simp] lemma dft_dconv (f g : α → ℂ) : dft (f ○ g) = dft f * conj (dft g) :=
funext $ dft_dconv_apply _ _

@[simp] lemma dft_iter_conv (f : α → ℂ) : ∀ n, dft (f ∗^ n) = dft f ^ n
| 0 := dft_triv_char
| (n + 1) := by simp [iter_conv_succ, pow_succ, dft_iter_conv]

lemma Lpnorm_conv_le_Lpnorm_dconv (hn₀ : n ≠ 0) (hn : even n) (f : α → ℂ) :
  ‖f ∗ f‖_[n] ≤ ‖f ○ f‖_[n] :=
begin
  refine le_of_pow_le_pow _ _ hn₀.bot_lt (le_of_mul_le_mul_left _ (_ : (0 : ℝ) < card α ^ n)),
  any_goals { positivity },
  obtain ⟨n, rfl⟩ := hn.two_dvd,
  simp_rw [Lpnorm_pow_eq_sum hn₀, mul_sum, ←mul_pow, ←nsmul_eq_mul, ←norm_nsmul, nsmul_eq_mul,
    ←dft_inversion, dft_conv, dft_dconv, pi.mul_apply],
  rw [←real.norm_of_nonneg (sum_nonneg $ λ i _, _), ←complex.norm_real, is_R_or_C.of_real_sum],
  any_goals { positivity },
  simp_rw [pow_mul', ←norm_pow _ n, complex.of_real_pow, ←is_R_or_C.conj_mul', map_pow, map_sum,
    map_mul, fintype.sum_pow, fintype.sum_mul_sum],
  simp only [@sum_comm _ _ α, ←mul_sum, prod_mul_prod_comm],
  refine (norm_sum_le _ _).trans_eq (complex.of_real_injective _),
  simp only [norm_mul, norm_prod, is_R_or_C.norm_conj, ←pow_mul],
  push_cast,
  have : ∀ f g : fin n → add_char α ℂ, 0 ≤ ∑ a, ∏ i, conj (f i a) * g i a,
  { rintro f g,
    suffices : ∑ a, ∏ i, conj (f i a) * g i a = if ∑ i, (g i - f i) = 0 then card α else 0,
    { rw this,
      split_ifs; positivity },
    simp_rw [←add_char.sum_eq_ite, add_char.sum_apply, add_char.sub_apply, add_char.map_neg_eq_inv,
      add_char.inv_apply_eq_conj, mul_comm] },
  simp only [is_R_or_C.of_real_pow, pow_mul, ←is_R_or_C.conj_mul', map_sum, map_mul,
    is_R_or_C.conj_conj, pi.conj_apply, mul_pow, fintype.sum_pow, ←sq, fintype.sum_mul_sum],
  conv_lhs { congr, skip, funext, rw ←complex.eq_coe_norm_of_nonneg (this _ _) },
  letI : fintype (fin n → add_char α ℂ) := @pi.fintype _ _ _ _ (λ i, add_char.fintype _ _),
  simp only [@sum_comm _ _ α, mul_sum, map_prod, map_mul, is_R_or_C.conj_conj, ←prod_mul_distrib],
  refine sum_congr rfl (λ x _, sum_congr rfl $ λ a _, prod_congr rfl $ λ i _, _),
  ring,
end

@[simp] lemma is_R_or_C.Lpnorm_coe_comp {𝕜 : Type*} [is_R_or_C 𝕜] (p) (f : α → ℝ) :
  ‖(coe : ℝ → 𝕜) ∘ f‖_[p] = ‖f‖_[p] :=
by simp only [←Lpnorm_norm _ ((coe : ℝ → 𝕜) ∘ f), ←Lpnorm_norm _ f, function.comp_app,
  is_R_or_C.norm_of_real, real.norm_eq_abs]

--TODO: Can we unify with `Lpnorm_conv_le_Lpnorm_dconv`?
lemma Lpnorm_conv_le_Lpnorm_dconv' (hn₀ : n ≠ 0) (hn : even n) (f : α → ℝ) :
  ‖f ∗ f‖_[n] ≤ ‖f ○ f‖_[n] :=
by simpa only [←is_R_or_C.coe_comp_conv, ←is_R_or_C.coe_comp_dconv, is_R_or_C.Lpnorm_coe_comp]
  using Lpnorm_conv_le_Lpnorm_dconv hn₀ hn (coe ∘ f)
