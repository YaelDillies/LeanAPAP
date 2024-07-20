import Mathlib.Combinatorics.Additive.AP.Three.Defs
import LeanAPAP.Prereqs.Convolution.Norm

/-!
# The convolution characterisation of 3AP-free sets
-/

open Finset Fintype Function
open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G] {s : Finset G}

lemma ThreeAPFree.l2Inner_mu_conv_mu_mu_two_smul_mu (hG : Odd (card G))
    (hs : ThreeAPFree (s : Set G)) :
    ⟪μ s ∗ μ s, μ (s.image (2 • ·))⟫_[ℝ] = (s.card ^ 2 : ℝ)⁻¹ := by
  obtain rfl | hs' := s.eq_empty_or_nonempty
  · simp
  simp only [l2Inner_eq_sum, sum_conv_mul, ←sum_product', RCLike.conj_to_real]
  rw [←diag_union_offDiag univ, sum_union (disjoint_diag_offDiag _), sum_diag, ←
    sum_add_sum_compl s, @sum_eq_card_nsmul _ _ _ _ _ (s.card ^ 3 : ℝ)⁻¹, nsmul_eq_mul,
    Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero, add_zero, pow_succ', mul_inv,
    mul_inv_cancel_left₀]
  · exact Nat.cast_ne_zero.2 hs'.card_pos.ne'
  · refine fun i hi ↦ not_ne_iff.1 fun h ↦ (mem_offDiag.1 hi).2.2 ?_
    simp_rw [mul_ne_zero_iff, ←mem_support, support_mu, mem_coe, mem_image, two_smul] at h
    obtain ⟨b, hb, hab⟩ := h.2
    obtain rfl := hs h.1.1 hb h.1.2 hab.symm
    simpa using hab
  · simpa using fun _ ↦ Or.inl
  · rintro a ha
    simp only [mu_apply, ha, if_true, mul_one, mem_image, exists_prop, mul_ite,
      mul_zero]
    rw [if_pos, card_image_of_injective, pow_three', mul_inv, mul_inv]
    rw [← Nat.card_eq_fintype_card] at hG
    exacts [hG.coprime_two_right.nsmul_right_bijective.injective, ⟨_, ha, two_smul _ _⟩]
