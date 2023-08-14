import combinatorics.additive.salem_spencer
import mathlib.data.nat.parity
import mathlib.group_theory.order_of_element
import prereqs.convolution.norm

open finset fintype function
open_locale big_operators pointwise

variables {G : Type*} [add_comm_group G] [decidable_eq G] [fintype G] {s : finset G}

lemma add_salem_spencer.L2inner_mu_conv_mu_mu_two_smul_mu (hG : odd (card G))
  (hs : add_salem_spencer (s : set G)) : ⟪μ s ∗ μ s, μ (s.image $ (•) 2)⟫_[ℝ] = (s.card ^ 2)⁻¹ :=
begin
  obtain rfl | hs' := s.eq_empty_or_nonempty,
  { simp },
  simp only [L2inner_eq_sum, sum_conv_mul, ←sum_product', is_R_or_C.conj_to_real],
  rw [←diag_union_off_diag univ, sum_union (disjoint_diag_off_diag _), sum_diag,
    ←sum_add_sum_compl s, @sum_eq_card_nsmul _ _ _ _ _ (s.card ^ 3 : ℝ)⁻¹, nsmul_eq_mul,
    finset.sum_eq_zero, finset.sum_eq_zero, add_zero, add_zero, pow_succ, mul_inv,
    mul_inv_cancel_left₀],
  any_goals { apply_instance },
  { exact nat.cast_ne_zero.2 hs'.card_pos.ne' },
  { refine λ i hi, not_ne_iff.1 (λ h, (mem_off_diag.1 hi).2.2 _),
    simp_rw [mul_ne_zero_iff, ←mem_support, support_mu, mem_coe, mem_image, two_smul] at h,
    obtain ⟨b, hb, hab⟩ := h.2,
    exact hs h.1.1 h.1.2 hb hab.symm },
  { simpa using λ _, or.inl },
  { rintro a ha,
    simp only [mu_apply, ha, if_true, mul_one, mem_image, exists_prop, mul_ite, mul_zero],
    rw [if_pos, card_image_of_injective, pow_three', mul_inv, mul_inv],
    exacts [hG.coprime_two_left.nsmul_bijective.injective, ⟨_, ha, two_smul _ _⟩] }
end
