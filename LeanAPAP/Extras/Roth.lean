import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Combinatorics.Additive.SalemSpencer
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Data.ZMod.Quotient
import Mathlib.GroupTheory.FiniteAbelian
import Mathlib.Topology.Instances.Complex
import LeanAPAP.Mathlib.Data.Nat.Parity
import LeanAPAP.Mathlib.Data.Real.Sqrt
import LeanAPAP.Mathlib.Order.Partition.Finpartition
import LeanAPAP.Prereqs.Discrete.DFT.Basic

/-!
# Roth's proof of Roth's theorem

We demonstrate our character and discrete Fourier transform API by proving Roth's theorem using
Roth's original proof.
-/

noncomputable section

open Finset
open Fintype (card)
open scoped BigOps ComplexConjugate Real

section one_five

open Multiplicative

variable {N : ℕ} {A B C : Finset (ZMod N)} {α β γ : ℝ} (hN : Odd N) [NeZero N]
  (hα : α = A.card / N) (hβ : β = B.card / N) (hγ : γ = C.card / N)

lemma one_five_first_calculation (hN : Odd N) :
    𝔼 d, 𝔼 x, 𝟭 A x * 𝟭 B (x * d) * 𝟭 C (x * d * d) =
      ∑ r, dft (𝟭 B) (r ^ 2)⁻¹ * (dft (𝟭 A) r * dft (𝟭 C) r) := by
  have : (Fintype.card (ZMod N)).Coprime 2
  · rwa [ZMod.card, Nat.coprime_two_right]
  simp_rw [← dft_conv_apply, dft_inv _ (indicate_isSelfAdjoint _), ← dft_dilate _ _ this]
  sorry
  -- rw [← card_mul_expect, ← nl2Inner_eq_expect, nl2Inner_dft, ← expect_product', inner_prod_expect]
  -- simp_rw [((indicate_isSelfAdjoint B).dilate 2).conj_eq, convolve, mul_expect, ← expect_product'
  --   univ_product_univ, dilate]
  -- refine expect_nbij (fun x ↦ (powHom 2 (x.1 * x.2), x.2)) _ _ _ _
  -- · simp only [mem_univ, forall_const]
  -- · rintro ⟨x₁, x₂⟩ -
  --   dsimp
  --   rw [pow_zmod_val_inv_pow' this, powHom_apply, mul_left_comm, ← mul_assoc, mul_comm x₂
  --     mul_pow, mul_assoc (x₁ ^ 2), sq, sq x₂, mul_inv_cancel_right, mul_right_comm x₁]
  -- · rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ - -
  --   rw [prod.mk.inj_iff, prod.mk.inj_iff, (powHom_bijective this).injective.eq_iff]
  --   rintro ⟨h, rfl : x₂ = y₂⟩
  --   exact ⟨by simpa using h, rfl⟩
  -- · rintro ⟨y₁, y₂⟩ -
  --   refine ⟨(powHom ((2 : ℕ) : ZMod (card (ZMod N)))⁻¹.val y₁ * y₂⁻¹, y₂)
  --     mem_univ _, prod.mk.inj_iff.2 ⟨_, rfl⟩⟩
  --   dsimp
  --   rw [inv_mul_cancel_right, pow_zmod_val_inv_pow this]

lemma one_five_second_calculation
  (hα : α = A.card / N) (hβ : β = B.card / N) (hγ : γ = C.card / N)
  (hA' : A = A.image ofAdd) (hB' : B = B.image ofAdd) (hC' : C = C.image ofAdd) :
  ∑ r, dft (𝟭 B) (-(2 • r)) * (dft (𝟭 A) r * dft (𝟭 C) r) =
    α * β * γ +
      ∑ r : AddChar (ZMod N) ℂ with r ≠ 0,
        dft (𝟭 A) r * (dft (𝟭 B) (-(2 • r)) * dft (𝟭 C) r) := by
  simp_rw [mul_left_comm, mul_assoc]
  rw [← sum_filter_add_sum_filter_not univ (fun χ : AddChar (ZMod N) ℂ ↦ χ = 0), add_left_inj,
    sum_filter, sum_ite_eq' _ (0 : AddChar (ZMod N) ℂ) _, if_pos (mem_univ _), smul_zero, neg_zero,
    dft_indicate_zero, dft_indicate_zero, dft_indicate_zero, ZMod.card, hα, hβ, hγ]
  simp only [card_image_of_injective _ ofAdd.injective, Complex.ofReal_div
    Complex.ofReal_nat_cast]
#exit
lemma one_five_third_bound (hN : Odd N) (hβ : β = B.card / N) (hγ : γ = C.card / N)
  (hB' : B = B.image ofAdd) (hC' : C = C.image ofAdd) :
  ∑ r : AddChar (ZMod N) ℂ with r ≠ 1,
        (dft (𝟭 B) (powHom 2 r)).abs * (dft (𝟭 C) r).abs ≤ (β * γ).sqrt := by
  have : Nat.Coprime 2 (Fintype.card (AddChar (ZMod N) ℂ))
  · rw AddChar.card_eq
    change Nat.Coprime 2 (Fintype.card (ZMod N))
    rwa [ZMod.card, Nat.prime_two.coprime_iff_not_dvd, ← even_iff_two_dvd, ← Nat.odd_iff_not_even]
  refine (sum_le_univ_sum_of_nonneg (fun x ↦ _)).trans _
  · positivity
  refine (cauchy_schwarz_sqrt _ _ _).trans_eq _
  simp_rw [Complex.sq_abs, Fintype.sum_equiv (equiv.of_bijective _ $ pow_bijective this) _
    (λ i, Complex.norm_sq (dft (𝟭 B) i)) (λ _, rfl), inner_sum_indicate, ZMod.card
    card_image_of_injective _ ofAdd.injective, hβ, hγ]
  rw real.sqrt_mul
  positivity
end

lemma one_five_fourth_bound (hN : Odd N)
  (hα : α = A.card / N) (hβ : β = B.card / N) (hγ : γ = C.card / N)
  (hB' : B = B.image ofAdd) (hC' : C = C.image ofAdd)
  (hf : ∀ χ : AddChar (ZMod N) ℂ, χ ≠ 1 → (dft (𝟭 A) χ).abs
    ≤ α * (β * γ).sqrt / 2) :
  (∑ r : AddChar (ZMod N) ℂ with r ≠ 1
        dft (𝟭 A) r * (dft (𝟭 B) (powHom 2 r)⁻¹ * dft (𝟭 C) r)).abs
      ≤ α * β * γ / 2 :=
calc _ ≤ ∑ r : AddChar (ZMod N) ℂ with r ≠ 1
        (dft (𝟭 A) r * (dft (𝟭 B) (powHom 2 r)⁻¹ * dft (𝟭 C) r)).abs :
          abv_sum_le_sum_abv _ _
   ... = ∑ r : AddChar (ZMod N) ℂ with r ≠ 1
        (dft (𝟭 A) r).abs * (dft (𝟭 B) (powHom 2 r)⁻¹ * dft (𝟭 C) r).abs :
      by simp_rw [map_mul]
   ... ≤ ∑ r : AddChar (ZMod N) ℂ with r ≠ 1
        α * (β * γ).sqrt / 2 * (dft (𝟭 B) (powHom 2 r)⁻¹ * dft (𝟭 C) r).abs : by
          refine sum_le_sum _
          intros i hi
          exact mul_le_mul_of_nonneg_right (hf _ (by simpa using hi)) (Complex.abs.nonneg _)
        end
   ... = α * (β * γ).sqrt / 2 * ∑ r : AddChar (ZMod N) ℂ with r ≠ 1
        (dft (𝟭 B) (powHom 2 r)⁻¹ * dft (𝟭 C) r).abs :
          by rw mul_sum
   ... = α * (β * γ).sqrt / 2 * ∑ r : AddChar (ZMod N) ℂ with r ≠ 1
        (dft (𝟭 B) (powHom 2 r)).abs * (dft (𝟭 C) r).abs :
          by simp_rw [map_mul, dft_inv _ (indicate_isSelfAdjoint _), Complex.abs_conj]
    ... ≤ _ : by
      refine (mul_le_mul_of_nonneg_left (one_five_third_bound hN hβ hγ hB' hC') _).trans_eq _
      · rw hα, positivity
      rw [div_mul_eq_mul_div, mul_assoc, real.mul_self_sqrt, mul_assoc]
      rw [hβ, hγ], positivity
    end

lemma one_five_fifth_calculation
  (h : (1 : ℝ) / N < (𝔼 d x, 𝟭 A x * 𝟭 B (x * d) * 𝟭 C (x * d * d)).abs) :
  ∃ x d : ZMod N, d ≠ 0 ∧ x ∈ A ∧ x + d ∈ B ∧ x + 2 * d ∈ C := by
  simp only [expect_multiplicative, indicate, ← ofAdd_add, and_assoc, mul_one
    ofAdd.injective.mem_finset_image, ← ite_and_mul_zero] at h
  simp only [expect_true_univ, ZMod.card, ← sum_div, div_div, map_div₀, Complex.abs_cast_nat
    map_mul, sum_boole, ← Nat.cast_sum] at h
  rw [← sum_filter_add_sum_filter_not Finset.univ (λ d : ZMod N, d = 0), sum_filter
    sum_ite_eq' _ (0 : ZMod N), if_pos (mem_univ _), Nat.cast_add, add_div] at h
  have : ((univ.filter (λ x : ZMod N, x ∈ A ∧ x + 0 ∈ B ∧ x + 0 + 0 ∈ C)).card : ℝ) / (N * N) ≤
    1 / N
  · rw ← div_div
    refine div_le_div_of_le_of_nonneg (div_le_one_of_le _ (by positivity)) (by positivity)
    exact Nat.cast_le.2 ((card_le_univ _).trans_eq (ZMod.card _))
  replace h := h.trans_le (add_le_add_right this _)
  rw [lt_add_iff_pos_right, lt_div_iff, zero_mul, Nat.cast_pos, pos_iff_ne_zero, ne.def
    sum_eq_zero_iff] at h
  · simp only [not_forall, mem_filter, mem_univ, true_and, card_eq_zero, exists_prop
      filter_eq_empty_iff, not_not, add_assoc, ← two_mul] at h
    obtain ⟨d, hd, x, z⟩ := h
    exact ⟨_, _, hd, z⟩
  rw [← sq, sq_pos_iff, Nat.cast_ne_zero]
  exact NeZero.ne _
end

lemma last_bit {α : ℝ} {δ : ℂ} (h : δ.abs ≤ α / 2) : α / 2 ≤ ((α : ℂ) + δ).abs := by
  rw [← sub_neg_eq_add]
  refine le_trans' (Complex.abs.le_sub _ _) _
  rw [absolute_value.map_neg, le_sub_comm]
  apply h.trans _
  rw [le_sub_iff_add_le, add_halves', Complex.abs_ofReal]
  exact le_abs_self α
end

lemma one_five {N : ℕ} {A B C : Finset (ZMod N)} {α β γ : ℝ} (hN : Odd N) [NeZero N]
  (hα : α = A.card / N) (hβ : β = B.card / N) (hγ : γ = C.card / N)
  (hf : ∀ r : ZMod N, r ≠ 0 → (dft (𝟭 (A.image ofAdd)) (to_character N (ofAdd r))).abs
    ≤ α * (β * γ).sqrt / 2)
  (hd : (1 : ℝ) / N < α * β * γ / 2) :
  ∃ x d : ZMod N, d ≠ 0 ∧ x ∈ A ∧ x + d ∈ B ∧ x + 2 * d ∈ C := by
  refine one_five_fifth_calculation rfl rfl rfl _
  refine hd.trans_le _
  rw [one_five_first_calculation hN,  one_five_second_calculation hα hβ hγ rfl rfl rfl
    ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  have hf' : ∀ χ : AddChar (ZMod N) ℂ, χ ≠ 1 →
    (dft (𝟭 (A.image ofAdd)) χ).abs ≤ α * (β * γ).sqrt / 2
  · intros χ hχ
    convert hf ((zmod_characters (NeZero.ne _)).symm χ).to_add _ using 1
    · rw [ofAdd_to_add, ← zmod_characters_apply, mul_equiv.apply_symm_apply]
    rwa [ne.def, ← equiv.eq_symm_apply, to_add_symm_eq, ofAdd_zero
      mul_equiv_class.map_eq_one_iff]
  exact last_bit (one_five_fourth_bound hN hα hβ hγ rfl rfl hf')
end

lemma one_five' {N : ℕ} {A B C : Finset (ZMod N)} {α β γ : ℝ} (hN : Odd N) [NeZero N]
  (hα : α ≤ (A.card : ℝ) / N) (hβ : β ≤ (B.card : ℝ) / N) (hγ : γ ≤ (C.card : ℝ) / N)
  (hβ' : 0 ≤ β) (hγ' : 0 ≤ γ)
  (hf : ∀ r : ZMod N, r ≠ 0 → (dft (𝟭 (A.image ofAdd)) (to_character N (ofAdd r))).abs
    ≤ α * (β * γ).sqrt / 2)
  (hd : (1 : ℝ) / N < α * β * γ / 2) :
  ∃ x d : ZMod N, d ≠ 0 ∧ x ∈ A ∧ x + d ∈ B ∧ x + 2 * d ∈ C := by
  refine one_five hN rfl rfl rfl _ _
  · intros r hr
    refine (hf r hr).trans (div_le_div_of_le_of_nonneg _ (by norm_num))
    refine mul_le_mul hα (real.sqrt_le_sqrt _) (real.sqrt_nonneg _) (by positivity)
    exact mul_le_mul hβ hγ hγ' (by positivity)
  refine hd.trans_le (div_le_div_of_le_of_nonneg _ (by norm_num))
  exact mul_le_mul (mul_le_mul hα hβ hβ' (by positivity)) hγ hγ' (by positivity)
end

-- lemma one_five_explicit {N : ℕ} {A B C : Finset (ZMod N)} {α β γ : ℝ} (hN : Odd N) [NeZero N]
--   (hα : α = A.card / N) (hβ : β = B.card / N) (hγ : γ = C.card / N)
--   (hf : ∀ r : ZMod N, r ≠ 0 → (dft (𝟭 (A.image ofAdd)) (to_character N (ofAdd r))).abs
--     ≤ α * (β * γ).sqrt / 2)
--   (hd : (1 : ℝ) / N < α * β * γ / 2) :
--   ∃ x d : ZMod N, d ≠ 0 ∧ x ∈ A ∧ x + d ∈ B ∧ x + 2 * d ∈ C :=
-- begin
--   simp only [dft, inner_prod_expect, expect_multiplicative
--     to_character_apply_ofAdd_apply_ofAdd, coe_coe_eq, set_like.coe_mk
--     ofAdd.injective.mem_finset_image, indicate_image, ← AddChar.inv_apply_eq_conj, ← map_neg_eq_inv] at hf
--   -- simp only [ne.def, set_like.coe_mk] at hf
--   -- simp only [ne.def, coe_coe_eq] at hf
-- end

end one_five

section one_six

-- lemma one_add_e (x : ℝ) : 1 + e x = 2 * e (x / 2) * real.cos (π * x) :=
-- begin
--   rw [mul_right_comm, Complex.ofReal_cos, Complex.two_cos, e, e, mul_assoc
--     Complex.ofReal_div, Complex.ofReal_bit0, Complex.ofReal_one, ← mul_assoc (x / 2 : ℂ)
--     div_mul_cancel (x : ℂ) two_ne_zero', mul_left_comm, mul_comm π, Complex.ofReal_mul, neg_mul
--     mul_assoc, add_mul, ← Complex.exp_add, ← two_mul, ← Complex.exp_add, add_left_neg
--     Complex.exp_zero, add_comm]
-- end

lemma one_sub_e_eq {θ : ℝ} :
  1 - e θ = 2 * real.sin (π * θ) * (- Complex.I * e (θ / 2)) := by
  have : Complex.exp (π * θ * Complex.I) = e (θ / 2)
  · rw [e, Complex.ofReal_div, ← mul_assoc, ← mul_assoc, Complex.ofReal_bit0, Complex.ofReal_one
      div_mul_cancel _ (two_ne_zero' ℂ), mul_comm (π : ℂ)]
  rw [Complex.ofReal_sin, Complex.two_sin, mul_assoc, ← mul_assoc Complex.I, mul_neg
    Complex.I_mul_I, neg_neg, one_mul, neg_mul, Complex.ofReal_mul, Complex.exp_neg, this
    ← e_neg, sub_mul, ← map_add_mul, ← map_add_mul, add_left_neg, map_zero_one, add_halves']
end

lemma real.sin_le_self {θ : ℝ} (h : 0 ≤ θ) : real.sin θ ≤ θ := by
  rcases eq_or_ne θ 0 with rfl | hθ'
  · rw [real.sin_zero]
  exact (real.sin_lt (lt_of_le_of_ne' h hθ')).le
end

lemma real.abs_sin_le_abs : ∀ θ, |real.sin θ| ≤ |θ| := by
  suffices : ∀ θ, 0 ≤ θ → |real.sin θ| ≤ |θ|
  · intros θ
    cases le_total 0 θ with hθ hθ
    · exact this _ hθ
    · rw [← abs_neg, ← real.sin_neg, ← abs_neg θ]
      exact this _ (by simpa using hθ)
  intros θ hθ
  rw abs_of_nonneg hθ
  cases le_total θ π
  · rw [abs_of_nonneg (real.sin_nonneg_of_nonneg_of_le_pi hθ h)]
    exact real.sin_le_self hθ
  refine (real.abs_sin_le_one _).trans (h.trans' _)
  linarith only [real.pi_gt_three]
end

-- this can also be lower bounded by 4 θ in the same conditions
lemma one_sub_e_le {θ : ℝ} :
  (1 - e θ).abs ≤ 2 * π * |θ| := by
  rw [one_sub_e_eq, map_mul, map_mul, map_mul, absolute_value.map_neg, Complex.abs_two
    ← abs_of_pos real.pi_pos, Complex.abs_I, one_mul, abs_e, mul_one, Complex.abs_ofReal
    mul_assoc, ← abs_mul, abs_of_pos real.pi_pos]
  exact mul_le_mul_of_nonneg_left (real.abs_sin_le_abs _) (by norm_num)
end

lemma real.abs_le_abs_sin_mul :
  ∀ {θ : ℝ}, |θ| ≤ 1 → |θ| ≤ |real.sin (π / 2 * θ)| := by
  suffices : ∀ θ, 0 ≤ θ → |θ| ≤ 1 → |θ| ≤ |real.sin (π / 2 * θ)|
  · intros θ hθ'
    cases le_total 0 θ with hθ hθ
    · exact this _ hθ hθ'
    · rw [← abs_neg (real.sin _), ← real.sin_neg, ← abs_neg, ← mul_neg]
      exact this (-θ) (by simpa) (by simpa using hθ')
  intros θ hθ hθ'
  exact abs_le_abs_of_nonneg hθ (real.le_sin_mul hθ (le_of_abs_le hθ'))
end

-- don't need this for now but it's nice
-- lemma le_one_sub_e {θ : ℝ} (hθ : |θ| ≤ 1 / 2) :
--   4 * |θ| ≤ (1 - e θ).abs :=
-- begin
--   -- have := real.abs_le_abs_sin_mul
--   rw [one_sub_e_eq, map_mul, map_mul, map_mul, absolute_value.map_neg, Complex.abs_two
--     Complex.abs_I, one_mul, abs_e, mul_one, Complex.abs_ofReal, bit0_eq_two_mul (2 : ℝ)
--     mul_assoc, ← abs_mul, abs_of_pos real.pi_pos]
-- end

lemma abs_lt_one_of_floor_eq {x y : ℝ} (h : ⌊x⌋₊ = ⌊y⌋₊) (hx : 0 ≤ x) (hy : 0 ≤ y) : |x - y| < 1 := by
  apply int.abs_sub_lt_one_of_floor_eq_floor
  rwa [← Nat.cast_floor_eq_int_floor hx, ← Nat.cast_floor_eq_int_floor hy, Nat.cast_inj]
end

lemma pigeons {s : Finset ℝ} {m : ℕ} (hm : m ≠ 0) (hs : m < s.card)
  (hs' : ∀ x ∈ s, x ∈ set.Ico (0 : ℝ) 1) :
  ∃ x y : ℝ, x ≠ y ∧ x ∈ s ∧ y ∈ s ∧ |x - y| < m⁻¹ := by
  let f : ℝ → ℕ := fun x ↦ ⌊x * m⌋₊
  have : ∀ x ∈ s, f x ∈ range m
  · intros x hx
    obtain ⟨l, r⟩ := hs' _ hx
    rw [mem_range, Nat.floor_lt]
    · exact mul_lt_of_lt_one_left (by positivity) r
    positivity
  have this' : (range m).card * 1 < s.card
  · rwa [card_range, mul_one],
  have := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to this this'
  simp only [one_lt_card_iff, mem_filter, mem_range] at this
  obtain ⟨_, h2, x, y, ⟨hx, h⟩, ⟨hy, rfl⟩, h7⟩ := this
  have := abs_lt_one_of_floor_eq h (mul_nonneg (hs' _ hx).1 (Nat.cast_nonneg _))
    (mul_nonneg (hs' _ hy).1 (Nat.cast_nonneg _))
  rw [← sub_mul, abs_mul, Nat.abs_cast, ← lt_div_iff, one_div] at this
  · exact ⟨x, y, h7, hx, hy, this⟩
  positivity
end

lemma pigeons' (f : ℕ → ℝ) (m : ℕ) (hm : m ≠ 0)
  (hs' : ∀ x ≤ m, f x ∈ set.Ico (0 : ℝ) 1) :
  ∃ x y : ℕ, x < y ∧ x ≤ m ∧ y ≤ m ∧ |f x - f y| < m⁻¹ := by
  let g : ℕ → ℕ := fun x ↦ ⌊f x * m⌋₊
  have : ∀ x ∈ range (m + 1), g x ∈ range m
  · intros x hx
    obtain ⟨l, r⟩ := hs' x (by simpa [mem_range_succ_iff] using hx)
    rw [mem_range, Nat.floor_lt]
    · exact mul_lt_of_lt_one_left (by positivity) r
    positivity
  have this' : (range m).card * 1 < (range (m+1)).card
  · rwa [card_range, card_range, mul_one], simp
  have := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to this this'
  simp only [one_lt_card_iff, mem_filter, mem_range, mem_range_succ_iff, g] at this
  obtain ⟨_, h2, x, y, ⟨hx, h⟩, ⟨hy, rfl⟩, h7⟩ := this
  wlog h8 : x < y generalizing x y
  · rw not_lt at h8
    refine this y x hy h7.symm hx (by linarith) h.symm (lt_of_le_of_ne' h8 h7)
  have := abs_lt_one_of_floor_eq h (mul_nonneg (hs' _ hx).1 (Nat.cast_nonneg _))
    (mul_nonneg (hs' _ hy).1 (Nat.cast_nonneg _))
  rw [← sub_mul, abs_mul, Nat.abs_cast, ← lt_div_iff, one_div] at this
  · exact ⟨x, y, h8, hx, hy, this⟩
  positivity
end

-- works with `hr : 1 ≤ r`
lemma circular_pigeons (θ : ℝ) {r : ℕ} (hr : r ≠ 0) :
  ∃ d : ℕ, d ≠ 0 ∧ d ≤ r ∧ (1 - e (θ * d)).abs ≤ 2 * π / r := by
  let f : ℕ → ℝ := λ i, int.fract (θ * i)
  obtain ⟨x, y, hxy, hx, hy, hr'⟩ :=
    pigeons' f r hr (λ i hi, ⟨int.fract_nonneg _, int.fract_lt_one _⟩)
  · refine ⟨y - x, (Nat.sub_pos_of_lt hxy).ne', (Nat.sub_le y x).trans hy, _⟩
    rw abs_sub_comm at hr'
    rw [Nat.cast_sub hxy.le, mul_sub, e_sub, one_sub_div e_ne_zero, ← e_fract (θ * x)
      ← e_fract (θ * y), ← one_sub_div e_ne_zero, ← e_sub]
    · cases lt_or_le r 2
      · rw [sub_eq_add_neg]
        refine (Complex.abs.add_le _ _).trans _
        rw [absolute_value.map_one, absolute_value.map_neg, abs_e, le_div_iff, ← bit0]
        · refine mul_le_mul_of_nonneg_left _ (by norm_num)
          refine real.pi_gt_three.le.trans' _
          norm_cast
          linarith
        rwa [Nat.cast_pos, pos_iff_ne_zero]
      refine one_sub_e_le.trans _
      rw div_eq_mul_inv
      exact mul_le_mul_of_nonneg_left hr'.le (mul_nonneg zero_le_two real.pi_pos.le)
end

lemma divide_up (s : ℕ) (t : ℕ) (hs : t ≤ s) (ht : t ≠ 0) :
  ∃ P : finpartition (range s), ∀ i ∈ P.parts, (∃ x y, i = Ico x y) ∧ t ≤ i.card ∧ i.card < 2 * t := by
  set n := s / t with ← hn
  have hnl : n * t ≤ s := Nat.div_mul_le_self _ _
  have hnu : s < (n + 1) * t
  · rw [add_one_mul]
    exact Nat.lt_div_mul_add ht.bot_lt
  clear_value n
  clear hn
  induction n with n ih generalizing s
  · simp only [one_mul] at hnu
    cases hs.not_lt hnu
  cases n
  · refine ⟨finpartition.indiscrete _, λ i hi, _⟩
    · simp only [bot_eq_empty, ne.def, range_eq_empty_iff]
      linarith
    rw [finpartition.indiscrete_parts, mem_singleton] at hi
    rw one_mul at hnl
    subst i
    refine ⟨⟨0, s, by rw range_eq_Ico⟩, _⟩
    simpa [hnl] using hnu
  simp only [Nat.succ_eq_add_one] at hnl hnu ih
  have h₂ : (n + 1) * t ≤ s - t
  · apply le_tsub_ofAdd_le_left
    linarith only [hnl]
  have h₃ : s - t < (n + 1 + 1) * t
  · rw [tsub_lt_iff_left hs]
    linarith only [hnu]
  have h₁ : t ≤ s - t
  · apply h₂.trans' _
    apply Nat.le_mul_of_pos_left
    simp
  have : disjoint (range (s - t)) (Ico (s - t) s)
  · rw [range_eq_Ico]
    exact Ico_disjoint_Ico_consecutive 0 (s - t) s
  obtain ⟨P, hP⟩ := ih (s - t) h₁ h₂ h₃
  refine ⟨P.extend' this _, _⟩
  · rw [range_eq_Ico, sup_eq_union, Ico_union_Ico_eq_Ico]
    · simp
    · exact Nat.sub_le _ _
  intros i hi
  rw [finpartition.extend'] at hi
  split_ifs at hi
  · exact hP _ (by simpa using hi)
  rw [finpartition.extend_parts, mem_insert] at hi
  rcases hi with rfl | hi
  · refine ⟨⟨_, _, rfl⟩, _⟩
    rw [Nat.card_Ico, Nat.sub_sub_self hs]
    exact ⟨le_rfl, lt_two_mul_self ht.bot_lt⟩
  exact hP _ hi
end

lemma divide_up' (s : ℕ) (t : ℕ) (hs : t ≤ s) (ht₀ : t ≠ 0) :
  ∃ P : finpartition (range s), ∀ p : Finset ℕ, p ∈ P.parts →
    t ≤ p.card ∧ p.card < 2 * t ∧ (∃ i n, p = (range n).image (fun x ↦ i + x)) := by
  obtain ⟨P, hP⟩ := divide_up s t hs ht₀
  refine ⟨P, λ p hp, _⟩
  obtain ⟨⟨x, y, rfl⟩, ht⟩ := hP p hp
  refine ⟨ht.1, ht.2, x, y - x, _⟩
  rw [range_eq_Ico, image_add_left_Ico, add_tsub_cancel_of_le, add_zero]
  replace ht : 0 < _ := ht.1.trans' ht₀.bot_lt
  rw Nat.card_Ico at ht
  refine le_of_lt _
  rwa ← tsub_pos_iff_lt
end

lemma ineq_thing {s d i : ℕ} (h : d ≤ s) (hi : i < d) : s / d ≤ (s - i - 1) / d + 1 := by
  rw [← Nat.succ_eq_add_one, ← Nat.add_div_right _ (bot_le.trans_lt hi)]
  apply Nat.div_le_div_right
  rw [Nat.sub_sub, ← Nat.sub_add_comm, Nat.add_sub_assoc]
  · apply le_self_add
  · rwa Nat.succ_le_iff
  rw Nat.succ_le_iff
  apply hi.trans_le h
end

lemma injective_affine {a d : ℕ} (hd : d ≠ 0) : function.injective (fun x ↦ a + d * x) := by
  intros x y
  rw [add_right_inj]
  simp [hd]
end

lemma mod_partitions_parts_card {s d : ℕ} {i : Finset ℕ} (hd : d ≠ 0) (h : d ≤ s)
  (hi : i ∈ (mod_partitions s d hd h).parts) : s / d ≤ i.card := by
  simp only [mod_partitions_parts_eq, mem_image, mem_range] at hi
  obtain ⟨i, hi, rfl⟩ := hi
  rw [card_image_of_injective, card_range]
  · exact ineq_thing h hi
  apply injective_affine hd
end

lemma partitions_one (N t r d : ℕ) (hrN : r ≤ N) (ht : t ≤ N / r) (ht' : t ≠ 0)
  (hd : d ≠ 0) (hdr : d ≤ r) :
  ∃ P : finpartition (range N), ∀ p : Finset ℕ, p ∈ P.parts →
    t ≤ p.card ∧ p.card < 2 * t ∧ ∃ i n, p = (range n).image (fun x ↦ i + d * x) := by
  -- obtain ⟨d, hd, hdr, hd'⟩ := circular_pigeons θ hr
  -- use d
  let P' := mod_partitions N d hd (hdr.trans hrN)
  have hQ' : ∀ p ∈ P'.parts, ∃ Q : finpartition p, ∀ q : Finset ℕ, q ∈ Q.parts →
    t ≤ q.card ∧ q.card < 2 * t ∧ (∃ i n, q = (range n).image (fun x ↦ i + d * x))
  · intros p hp
    simp only [mod_partitions_parts_eq, mem_image, mem_range] at hp
    obtain ⟨a, ha, rfl⟩ := hp
    obtain ⟨Q, hQ⟩ := divide_up' ((N - a - 1) / d + 1) t (ht.trans $ (ineq_thing
      (hdr.trans hrN) ha).trans' $ Nat.div_le_div_left hdr hd.bot_lt) ht'
    refine ⟨Q.push _ (injective_affine hd), λ q hq, _⟩
    rw [finpartition.push_parts, mem_image] at hq
    obtain ⟨q, hq, rfl⟩ := hq
    obtain ⟨hin1, hin2, i, n, rfl⟩ := hQ _ hq
    rw card_image_of_injective
    · refine ⟨hin1, hin2, a + d * i, n, _⟩
      rw image_image
      congr' 1 with x
      ring_nf
    exact injective_affine hd
  choose Q hQ using hQ'
  refine ⟨P'.bind Q, _⟩
  intros p hp
  rw finpartition.mem_bind at hp
  obtain ⟨p', hp', hp''⟩ := hp
  exact hQ _ _ _ hp''
end

lemma many_triangles_aux {θ z : ℝ} {d b : ℕ} (h : (1 - e (θ * d)).abs ≤ z) :
  (1 - e (θ * d * b)).abs ≤ b * z := by
  induction b with b ih
  · rw [Nat.cast_zero, mul_zero, map_zero_one, sub_self, map_zero, zero_mul]
  rw [Nat.cast_add_one, mul_add_one, map_add_mul, add_one_mul]
  refine (Complex.abs.sub_le _ _ _).trans (add_le_add ih _)
  rwa [← mul_one_sub, map_mul, abs_e, one_mul]
end

lemma many_triangles {θ z : ℝ} {d t a b : ℕ} (h : (1 - e (θ * d)).abs ≤ z) (ha : a < t)
  (hb : b < t) :
  (e (θ * d * a) - e (θ * d * b)).abs ≤ t * z := by
  wlog hab : a ≤ b generalizing a b
  · rw absolute_value.map_sub
    exact this hb ha (le_of_not_le hab)
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [Nat.cast_add, mul_add, map_add_mul, ← mul_one_sub, map_mul, abs_e, one_mul]
  apply (many_triangles_aux h).trans _
  have : b ≤ t := by linarith
  refine mul_le_mul_of_nonneg_right _ (h.trans' (Complex.abs.nonneg _))
  exact_mod_cast this
end

-- 4 π t / r ≤ ε
-- t ≤ N / r

-- 4 π N / r ^ 2 ≤ ε
-- sqrt(4 π N / ε) ≤ r
-- 1 / r ≤ sqrt(ε / 4 π N)
-- t ≤ sqrt (N ε / 4 π)
-- t = ⌈sqrt (N ε / 16 π)⌉
-- ⌈x / 2⌉ ≤ x
-- x ≥ 1
-- N ε / 16 π ≥ 1
-- N ε ≥ 16 π
-- N ≥ 16 π ε⁻¹

lemma partitions_two (θ : ℝ) (N t r : ℕ) (hr : r ≠ 0) (hrN : r ≤ N) (ht : t ≤ N / r) (ht' : t ≠ 0) :
  ∃ d ≠ 0, ∃ P : finpartition (range N), ∀ p : Finset ℕ, p ∈ P.parts →
    t ≤ p.card ∧ (∃ i n, p = (range n).image (fun x ↦ i + d * x)) ∧
    ∀ x y : ℕ, x ∈ p → y ∈ p → (e (θ * x) - e (θ * y)).abs ≤ 4 * π * t / r := by
  obtain ⟨d, hd, hdr, hd'⟩ := circular_pigeons θ hr
  obtain ⟨P, hP⟩ := partitions_one N t r d hrN ht ht' hd hdr
  refine ⟨d, hd, P, _⟩
  intros p hp
  obtain ⟨htn, htn', i, n, rfl⟩ := hP p hp
  refine ⟨htn, ⟨i, n, rfl⟩, _⟩
  simp only [mem_image, mem_range, exists_prop, forall_exists_index, and_imp]
  rintro _ _ a ha rfl b hb rfl
  rw [Nat.cast_add, Nat.cast_add, mul_add, mul_add, map_add_mul, map_add_mul, ← mul_sub, map_mul, abs_e, one_mul
    Nat.cast_mul, Nat.cast_mul, ← mul_assoc, ← mul_assoc]
  apply (many_triangles hd' ha hb).trans _
  rw [mul_comm (4 * π), bit0_eq_two_mul (2 : ℝ), mul_assoc, ← mul_assoc, mul_div_assoc (_ * _)
    mul_comm (t : ℝ)]
  refine mul_le_mul_of_nonneg_right _ _
  rw [card_image_of_injective _ (injective_affine hd), card_range] at htn'
  exact_mod_cast htn'.le
  exact div_nonneg real.two_pi_pos.le (Nat.cast_nonneg _)
end

lemma ceil_thing {x : ℝ} (hx : 1 ≤ x) : (⌈x / 2⌉₊ : ℝ) ≤ x := by
  cases lt_or_le x 2
  · refine hx.trans' _
    simp only [Nat.cast_le_one, Nat.ceil_le, Nat.cast_one]
    linarith
  exact (Nat.ceil_lt_add_one (by linarith)).le.trans (by linarith)
end

lemma floor_thing {x : ℝ} (hx : 1 ≤ x) : x / 2 ≤ ⌊x⌋₊ := by
  cases lt_or_le x 2 with hx' hx'
  · rw [Nat.floor_eq_on_Ico' 1 x ⟨by simpa using hx, by simpa using hx'⟩, Nat.cast_one]
    linarith
  exact (Nat.sub_one_lt_floor _).le.trans' (by linarith)
end

lemma sqrt_div_two {x : ℝ} (hx : 0 ≤ x) : real.sqrt x / 2 = real.sqrt (x / 4) := by
  have : (4 : ℝ) = 2 ^ 2, norm_num
  rw [this, real.sqrt_div hx, real.sqrt_sq]
  norm_num
end

-- some upper bound on ε is needed but can be really weak (i think 24 works)
-- we also need a lower bound on Nε
lemma partitions_three (θ ε : ℝ) (N : ℕ) (hN : 8 * π / ε ≤ N) (hε : 0 < ε) (hε' : ε ≤ 1) :
  ∃ d ≠ 0, ∃ P : finpartition (range N), ∀ p : Finset ℕ, p ∈ P.parts →
    real.sqrt ((N * ε) / (32 * π)) ≤ p.card ∧ (∃ i n, p = (range n).image (fun x ↦ i + d * x)) ∧
    ∀ x y : ℕ, x ∈ p → y ∈ p → (e (θ * x) - e (θ * y)).abs ≤ ε := by
  let t := ⌊real.sqrt ((N * ε) / (8 * π))⌋₊
  let r := ⌈real.sqrt ((2 * π * N) / ε)⌉₊
  have := real.pi_pos
  have hN' : N ≠ 0 := (Nat.cast_pos.1 (hN.trans_lt' (by positivity))).ne'
  have ht'' : 1 ≤ real.sqrt ((N * ε) / (8 * π))
  · rwa [real.le_sqrt', one_pow, le_div_iff, one_mul, ← div_le_iff]
    · exact hε
    · positivity
    · norm_num
  have ht' : t ≠ 0, · rwa [ne.def, Nat.floor_eq_zero, not_lt]
  have : (r : ℝ) ≤ real.sqrt (N * (8 * π) / ε)
  · refine (ceil_thing _).trans_eq' _
    · rw [real.le_sqrt', one_pow, one_le_div hε]
      · refine hε'.trans (one_le_mul_of_one_le_of_one_le _ _)
        · rw Nat.one_le_cast
          exact hN'.bot_lt
        linarith [real.pi_gt_three]
      · norm_num
    change (Nat.ceil _ : ℝ) = _
    rw [sqrt_div_two, mul_rotate, mul_comm 8 π, ← mul_assoc, div_div, ← div_mul_div_comm
      mul_div_right_comm, mul_comm π]
    · norm_num1, refl
    · positivity
  have hr : r ≠ 0
  · simp only [ne.def, Nat.ceil_eq_zero, not_le, real.sqrt_pos]
    positivity
  have ht : t ≤ N / r
  · rw [Nat.le_div_iff_mul_le hr.bot_lt, ←  @Nat.cast_le ℝ, Nat.cast_mul]
    refine (mul_le_mul (Nat.floor_le (real.sqrt_nonneg _)) this (Nat.cast_nonneg _)
      (real.sqrt_nonneg _)).trans_eq _
    rw [← real.sqrt_mul, div_mul_div_comm, ← mul_assoc, mul_comm (8 * π), mul_div_mul_right
      mul_right_comm, mul_div_cancel _ hε.ne', real.sqrt_mul_self (Nat.cast_nonneg N)]
    · positivity
    · positivity
  have hr' : r ≤ N
  · rw [Nat.le_div_iff_mul_le hr.bot_lt] at ht
    exact ht.trans' (Nat.le_mul_of_pos_left ht'.bot_lt)
  obtain ⟨d, hd, P, hP⟩ := partitions_two θ N t r hr hr' ht ht'
  refine ⟨d, hd, P, λ p hp, _⟩
  refine ⟨(Nat.cast_le.2 (hP p hp).1).trans' _, (hP p hp).2.1
    λ x y hx hy, ((hP p hp).2.2 x y hx hy).trans _⟩
  · refine (floor_thing ht'').trans_eq' _
    rw [sqrt_div_two, div_div, mul_right_comm]
    · norm_num1, refl
    · positivity
  refine (div_le_div _ (mul_le_mul_of_nonneg_left (Nat.floor_le (real.sqrt_nonneg _))
    _) _ (Nat.le_ceil _)).trans_eq _
  · positivity
  · positivity
  · positivity
  rw [mul_div_assoc, ← real.sqrt_div, mul_comm, ← eq_div_iff, real.sqrt_eq_iff_mul_self_eq_of_pos
    div_mul_div_comm, mul_mul_mul_comm _ π, div_div_div_eq, ← mul_assoc (8 * π), mul_rotate _ ε
    mul_div_mul_right, mul_mul_mul_comm _ π]
  · ring_nf
  · exact_mod_cast hN'
  all_goals · positivity
end

end one_six

section one_six_next
variable (A : Finset ℕ) {N : ℕ} [NeZero N] (α : ℝ) {η : ℝ} (r : ZMod N)

open Multiplicative

lemma dft_character (f : ZMod N → ℂ) :
  dft f (to_character N (ofAdd r)) = (∑ x : ZMod N, e (-(r * x / N)) * f (ofAdd x)) / N := by
  rw [dft, inner_prod_expect, expect_multiplicative]
  simp only [coe_coe_eq, to_character_apply_ofAdd_apply_ofAdd, subtype.coe_mk
    ← AddChar.inv_apply_eq_conj, ← map_neg_eq_inv, expect_true_univ, ZMod.card, to_add_ofAdd]
end

lemma map_zmod (f : ℕ → ℂ) : ∑ (i : ZMod N), f i.val = ∑ i in range N, f i :=
sum_nbij (λ i, i.val) (λ x hx, mem_range.2 (ZMod.val_lt _)) (by simp)
  (λ i j hi hj h, ZMod.val_injective _ h)
  (λ b hb, ⟨b, by simp, by · rw [ZMod.val_nat_cast, Nat.mod_eq_of_lt], rwa ← mem_range⟩)

lemma find_subprogression_first (hA : A ⊆ range N) (hr : r ≠ 0) :
  dft (𝟭 (A.image (λ i, ofAdd (i : ZMod N)))) (to_character N (ofAdd r)) =
    (∑ x in range N, e (-(r * x / N)) * (ite (x ∈ A) 1 0 - A.card / N)) / N := by
  have : A.image (λ i, ofAdd (i : ZMod N)) = (A.image (λ i : ℕ, (i : ZMod N))).image ofAdd
  · rw [image_image]
  have h1 : to_character N (ofAdd r) ≠ 1
  · rw [← zmod_characters_apply (NeZero.ne N), ne.def, mul_equiv_class.map_eq_one_iff]
    simpa only using hr
  rw [this, ← dft_balance _ _ h1, dft_character]
  congr' 1
  refine sum_nbij (λ i, i.val) (λ x _, mem_range.2 (ZMod.val_lt _)) _
    (λ i j hi hj h, ZMod.val_injective _ h)
    (λ b hb, ⟨b, by simp, by · rw [ZMod.val_nat_cast, Nat.mod_eq_of_lt], rwa ← mem_range⟩)
  intros x hx
  rw [balance, expect_indicate, ZMod.card, indicate_image
    card_image_of_injective _ ofAdd.injective, card_image_of_inj_on, indicate, ZMod.nat_cast_val]
  · congr' 3
    simp only [mem_image, exists_prop, eq_iff_iff]
    split
    · rintro ⟨y, hy, rfl⟩
      rwa [ZMod.val_nat_cast, Nat.mod_eq_of_lt (mem_range.1 (hA hy))]
    intro hx'
    exact ⟨_, hx', by simp⟩
  rintro i hi j hj h
  rw mem_coe at hi hj
  rwa [ZMod.nat_coe_eq_nat_coe_iff', Nat.mod_eq_of_lt (mem_range.1 (hA hi))
    Nat.mod_eq_of_lt (mem_range.1 (hA hj))] at h
end

lemma balance_abs {x : ℕ} {A : Finset ℕ} (hA : A ⊆ range N) :
  (ite (x ∈ A) 1 0 - A.card / N : ℂ).abs ≤ 1 := by
  suffices : |(ite (x ∈ A) 1 0 - A.card / N : ℝ)| ≤ 1
  · simpa only [← Complex.abs_ofReal, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div
      apply_ite (coe : ℝ → ℂ), Complex.ofReal_zero, Complex.ofReal_nat_cast] using this
  have : (A.card : ℝ) / N ≤ 1
  · rw [div_le_one, Nat.cast_le]
    · simpa using card_le_of_subset hA
    rw [Nat.cast_pos]
    exact (NeZero.ne N).bot_lt
  split_ifs
  · rw [abs_of_nonneg, sub_le_self_iff]
    · positivity
    rwa sub_nonneg
  rwa [zero_sub, abs_neg, abs_div, Nat.abs_cast, Nat.abs_cast]
end

lemma find_subprogression_second_inter (hA : A ⊆ range N) (hη : 0 < η) (p : Finset ℕ)
  (hP : ∀ x y, x ∈ p → y ∈ p → Complex.abs (e (-r / N * x) - e (-r / N * y)) ≤ η / 2) :
  (∑ x in p, e (-(r * x / N)) * (ite (x ∈ A) 1 0 - A.card / N)).abs ≤
    |∑ x in p, (ite (x ∈ A) 1 0 - A.card / N)| + p.card * (η / 2) := by
  rcases p.eq_empty_or_nonempty with rfl | ⟨xi, hxi⟩
  · simp only [sum_empty, map_zero, abs_zero, card_empty, Nat.cast_zero, zero_mul, zero_div
      add_zero]
  have : ∑ x in p, e (-(r * x / N)) * (ite (x ∈ A) 1 0 - A.card / N) =
    (∑ x in p, e (-(r * xi / N)) * (ite (x ∈ A) 1 0 - A.card / N)) +
      (∑ x in p, (e (-(r * x / N)) - e (-(r * xi / N))) * (ite (x ∈ A) 1 0 - A.card / N))
  · rw [← sum_add_distrib]
    congr' 1 with x : 1
    ring
  rw [this, ← mul_sum]
  refine (Complex.abs.add_le _ _).trans _
  rw [map_mul, abs_e, one_mul]
  refine add_le_add (le_of_eq _) _
  · simp only [← Complex.abs_ofReal, Complex.ofReal_zero, Complex.ofReal_sub, Complex.ofReal_one
      apply_ite (coe : ℝ → ℂ), Complex.ofReal_div, Complex.ofReal_nat_cast
      Complex.ofReal_sum]
  refine (abv_sum_le_sum_abv _ _).trans _
  rw [← nsmul_eq_mul, ← sum_const]
  refine sum_le_sum _
  intros x hx
  rw [mul_div_right_comm, mul_div_right_comm, ← neg_mul, ← neg_mul, ← neg_div, map_mul]
  refine (mul_le_mul (hP _ _ hx hxi) (balance_abs hA) _ (by positivity)).trans_eq (mul_one _)
  positivity
end

lemma find_subprogression_second (P : finpartition (range N)) (hA : A ⊆ range N) (hr : r ≠ 0)
  (hη : 0 < η)
  (hr' : η ≤ (dft (𝟭 (A.image (λ i, ofAdd (i : ZMod N)))) (to_character N (ofAdd r))).abs)
  (hP : ∀ p ∈ P.parts, ∀ x y, x ∈ p → y ∈ p → ‖e (-r / N * x) - e (-r / N * y)‖ ≤ η / 2) :
  η ≤ (∑ p in P.parts, |∑ x in p, (ite (x ∈ A) 1 0 - A.card / N)|) / N + η / 2 := by
  rw [find_subprogression_first _ _ hA hr, ← P.sup_parts, sup_eq_bUnion
    sum_bUnion P.disjoint, map_div₀, Complex.abs_cast_nat] at hr'
  refine hr'.trans _
  rw [div_le_iff, add_mul, div_mul_cancel, mul_comm (η / 2)]
  rotate
  · rw Nat.cast_ne_zero
    exact NeZero.ne N
  · rw Nat.cast_pos
    exact (NeZero.ne N).bot_lt
  refine (abv_sum_le_sum_abv _ _).trans _
  have : (N : ℝ) * (η / 2) = ∑ p in P.parts, p.card * (η / 2)
  · rw [← sum_mul, ← Nat.cast_sum, P.sum_card_parts, card_range]
  rw [this, ← sum_add_distrib]
  exact sum_le_sum (λ p hp, find_subprogression_second_inter A r hA hη _ (hP _ hp))
end

lemma find_subprogression_third (P : finpartition (range N)) (hA : A ⊆ range N) (hr : r ≠ 0)
  (hη : 0 < η)
  (hr' : η ≤ (dft (𝟭 (A.image (λ i, ofAdd (i : ZMod N)))) (to_character N (ofAdd r))).abs)
  (hP : ∀ p ∈ P.parts, ∀ x y, x ∈ p → y ∈ p → ‖e (-r / N * x) - e (-r / N * y)‖ ≤ η / 2) :
  ∃ p ∈ P.parts, (p.card : ℝ) * (η / 2) ≤
    |∑ x in p, (ite (x ∈ A) 1 0 - A.card / N)| + ∑ x in p, (ite (x ∈ A) 1 0 - A.card / N) := by
  refine exists_le_of_sum_le (P.parts_nonempty _) _
  · simpa using NeZero.ne N
  have h₁ : (N : ℝ) * (η / 2) = ∑ p in P.parts, p.card * (η / 2)
  · rw [← sum_mul, ← Nat.cast_sum, P.sum_card_parts, card_range]
  have h₂ : ∑ p in P.parts, ∑ x in p, (ite (x ∈ A) 1 0 - A.card / N : ℝ) = 0
  · refine (sum_bUnion P.disjoint).symm.trans _
    rw [← sup_eq_bUnion, P.sup_parts, sum_sub_distrib, sum_ite_mem, sum_const, sum_const, card_range
      (inter_eq_right_iff_subset _ _).2 hA, Nat.smul_one_eq_coe, nsmul_eq_mul, mul_div_cancel'
      sub_self]
    rw Nat.cast_ne_zero
    exact NeZero.ne N
  rw [sum_add_distrib, h₂, add_zero, ← h₁]
  have := find_subprogression_second A r P hA hr hη hr' hP
  rwa [← sub_le_iff_le_add, sub_half, le_div_iff'] at this
  rw [Nat.cast_pos, pos_iff_ne_zero]
  exact NeZero.ne N
end

lemma ge_of_abs_add_ge {x y : ℝ} (hy : 0 < y) (h : y ≤ |x| + x) :
  y / 2 ≤ x := by
  rcases abs_cases x with (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩);
  linarith
end

-- upper bound of η ≤ 48 should work?
lemma find_subprogression (hr : r ≠ 0) (hNη : 16 * π / η ≤ N) (hA : A ⊆ range N)
  (hα : α = A.card / N) (hη : 0 < η) (hη' : η ≤ 1)
  (hr' : η ≤ (dft (𝟭 (A.image (λ i, ofAdd (i : ZMod N)))) (to_character N (ofAdd r))).abs) :
∃ (p : Finset ℕ) (i n d : ℕ)
  d ≠ 0 ∧
  (η * N / (64 * π)).sqrt ≤ p.card ∧
  p = (range n).image (fun x ↦ i + d * x) ∧
  (α + η / 4) * (p.card : ℝ) ≤ (A ∩ p).card := by
  have : 8 * π / (η / 2) ≤ N
  · refine hNη.trans_eq' _
    rw [div_div_eq_mul_div, mul_right_comm]
    norm_num
  obtain ⟨d, hd, P, hP⟩ := partitions_three (-r / N) (η / 2) N this (by linarith) (by linarith)
  obtain ⟨p, hp, hp'⟩ := find_subprogression_third A r P hA hr hη hr' (λ p hp, (hP p hp).2.2)
  have h₁ : (N : ℝ) * (η / 2) / (32 * π) = η * N / (64 * π)
  · rw [mul_div_assoc', div_div, ← mul_assoc, mul_comm]
    norm_num
  have h₂ : 0 < (p.card : ℝ)
  · rw [Nat.cast_pos, card_pos, nonempty_iff_ne_empty]
    exact P.ne_bot hp
  have h₃ : 0 < (p.card : ℝ) * (η / 2)
  · positivity
  rw ← h₁
  obtain ⟨hp₁, ⟨i, n, hp₂⟩, -⟩ := hP p hp
  refine ⟨p, i, n, d, hd, hp₁, hp₂, _⟩
  have := ge_of_abs_add_ge h₃ hp'
  rwa [sum_sub_distrib, sum_const, mul_div_assoc, div_div, ← bit0_eq_two_mul, nsmul_eq_mul, ← hα
    le_sub_iff_add_le', ← mul_add, mul_comm, sum_ite_mem, inter_comm, sum_const, nsmul_one] at this
end

end one_six_next

section single_step

structure config where
  N : ℕ
  A : Finset ℕ
  hN : N ≠ 0
  hAN : A ⊆ range N
  hA : add_salem_spencer (A : set ℕ)

def config.α (C : config) : ℝ := C.A.card / C.N

lemma config.α_def (C : config) : C.α = C.A.card / C.N := rfl

lemma config.cast_N_pos (C : config) : 0 < (C.N : ℝ) :=
by · rw [Nat.cast_pos, pos_iff_ne_zero], exact C.hN

lemma config.α_eq (C : config) : C.α * C.N = C.A.card :=
by · rw [config.α, div_mul_cancel], exact C.cast_N_pos.ne'

lemma config.α_nonneg (C : config) : 0 ≤ C.α := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
lemma config.α_le_one (C : config) : C.α ≤ 1 :=
div_le_one_of_le (Nat.cast_le.2 ((card_le_of_subset C.hAN).trans_eq (by simp))) (Nat.cast_nonneg _)

lemma config.α_pow_le_one (C : config) (n : ℕ) : C.α ^ n ≤ 1 := pow_le_one n C.α_nonneg C.α_le_one

def config_of_subset_Ico {n m k : ℕ} {A : Finset ℕ} (hAnm : A ⊆ Ico n m) (h : k ≠ 0)
  (hk : n + k = m) (hA' : add_salem_spencer (A : set ℕ)) : config :=
· N := k
  A := A.image (λ i, i - n)
  hN := by simpa
  hAN := (image_subset_image hAnm).trans_eq $
    by rw [Nat.image_sub_const_Ico le_rfl, Nat.sub_self, range_eq_Ico, ← hk, add_tsub_cancel_left]
  hA := by
    rwa [← add_salem_spencer_add_right_iff, ← coe_image, Finset.image_image, image_congr, image_id]
    intros x hx
    dsimp
    rw Nat.sub_add_cancel
    exact (Finset.mem_Ico.1 (hAnm hx)).1
  end

lemma card_config_of_subset_Ico {n m k : ℕ} {A} (hAnm : A ⊆ Ico n m) (h) (hk : n + k = m) (hA') :
  (config_of_subset_Ico hAnm h hk hA').A.card = A.card := by
  rw [config_of_subset_Ico, card_image_of_inj_on]
  intros i hi j hj h
  exact tsub_inj_left (mem_Ico.1 (hAnm hi)).1 (mem_Ico.1 (hAnm hj)).1 h
end

lemma α_config_of_subset_Ico {n m k : ℕ} {A} (hAnm : A ⊆ Ico n m) (h) (hk : n + k = m) (hA') :
  (config_of_subset_Ico hAnm h hk hA').α = A.card / k :=
by · rw [config.α_def, card_config_of_subset_Ico], refl

lemma exists_odds {n : ℕ} (hn : even n) (hn' : n ≠ 0) :
  ∃ m₁ m₂ : ℕ, m₁ + m₂ = n ∧ Odd m₁ ∧ Odd m₂ ∧ n ≤ 4 * m₁ ∧ n ≤ 4 * m₂ := by
  rw even_iff_exists_two_mul at hn
  obtain ⟨n, rfl⟩ := hn
  cases n
  · simpa using hn'
  simp only [Nat.succ_eq_add_one]
  rcases Nat.even_or_odd' n with ⟨n, (rfl | rfl)⟩
  · refine ⟨2 * n + 1, 2 * n + 1, (two_mul _).symm, _, _, by linarith, by linarith⟩;
    simp with parity_simps
  · refine ⟨2 * n + 1, 2 * n + 3, by ring_nf, _, _, by linarith, by linarith⟩;
    simp with parity_simps
end

-- make the size Odd without decreasing density and decreasing size by no more than a quarter
lemma make_odd (C : config) : ∃ C : config, Odd C.N ∧ (C.N : ℝ) / 4 ≤ C.N ∧ C.α ≤ C.α := by
  cases (Nat.even_or_odd C.N).symm
  · refine ⟨C, h, _, le_rfl⟩
    have : 0 ≤ (C.N : ℝ) := Nat.cast_nonneg C.N
    linarith
  obtain ⟨m₁, m₂, hm, hm₁, hm₂, hm₁', hm₂'⟩ := exists_odds h C.hN
  have : disjoint (range m₁) (Ico m₁ C.N)
  · rw range_eq_Ico
    exact Ico_disjoint_Ico_consecutive 0 m₁ C.N
  have cs : (C.A ∩ range m₁).card + (C.A ∩ Ico m₁ C.N).card = C.A.card
  · rw [← card_disjoint_union, ← inter_distrib_left, range_eq_Ico
      Ico_union_Ico_eq_Ico (Nat.zero_le _), ← range_eq_Ico, (inter_eq_left_iff_subset _ _).2]
    · exact C.hAN
    · rw ← hm
      exact le_self_add
    exact disjoint_of_subset_left (inter_subset_right _ _)
      (disjoint_of_subset_right (inter_subset_right _ _) this)
  rw [←  @Nat.cast_le ℝ, Nat.cast_mul, Nat.cast_bit0, Nat.cast_bit0, Nat.cast_one
    ← div_le_iff' (show (0 : ℝ) < 4, by positivity)] at hm₁' hm₂'
  have : C.α * m₁ ≤ (C.A ∩ range m₁).card ∨ C.α * m₂ ≤ (C.A ∩ Ico m₁ C.N).card
  · by_contra'
    have := add_lt_add this.1 this.2
    rwa [← mul_add, ← Nat.cast_add, ← Nat.cast_add, cs, hm, config.α_eq, lt_self_iff_false] at this
  cases this with h h
  · refine ⟨⟨m₁, C.A ∩ range m₁, hm₁.pos.ne', inter_subset_right _ _, _⟩, hm₁, hm₁', _⟩
    · exact C.hA.mono (by simp only [coe_inter, set.inter_subset_left])
    rwa [config.α_def (config.mk _ _ _ _ _), le_div_iff (config.cast_N_pos _)]
  · refine ⟨config_of_subset_Ico (inter_subset_right _ _) hm₂.pos.ne' hm
      (C.hA.mono (inter_subset_left _ _)), hm₂, hm₂', _⟩
    rwa [config.α_def (config_of_subset_Ico _ _ _ _), le_div_iff (config.cast_N_pos _)
      card_config_of_subset_Ico]
end

lemma floor_third {N : ℕ} (hN : 12 ≤ N) : (N : ℝ) / 4 ≤ ((N / 3 : ℕ) : ℝ) := by
  rw [←  @Nat.floor_div_eq_div ℝ, Nat.cast_bit1, Nat.cast_one]
  refine (Nat.sub_one_lt_floor _).le.trans' _
  have : (12 : ℝ) ≤ N, by exact_mod_cast hN
  linarith
end

-- 22 works instead of 24 here
lemma ceil_third {N : ℕ} (hN : 24 ≤ N) : ((N / 3 : ℕ) : ℝ) + 1 ≤ (3 * N : ℝ) / 8 := by
  rw [←  @Nat.floor_div_eq_div ℝ, ← le_sub_iff_add_le, Nat.cast_bit1, Nat.cast_one]
  refine (Nat.floor_le _).trans _
  · positivity
  have : (24 : ℝ) ≤ N, by exact_mod_cast hN
  linarith
end

lemma difference (a c d : ℕ) : c / d ≤ (a + c) / d - a / d ∧ (a + c) / d - a / d ≤ c / d + 1 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  simp only [Nat.add_div hd, add_assoc]
  split_ifs;
  norm_num
end

lemma diff_thirds (n N : ℕ) :
  N / 3 ≤ (n + 1) * N / 3 - n * N / 3 ∧ (n + 1) * N / 3 - n * N / 3 ≤ N / 3 + 1 :=
by · rw add_one_mul, exact difference _ _ _

lemma empty_middle (C : config) (hC : 24 ≤ C.N)
  (h3 : ↑(C.A ∩ Ico (C.N / 3) (2 * C.N / 3)).card < C.α * C.N / 5) :
  ∃ C : config, (C.N : ℝ) / 4 ≤ C.N ∧ (16 / 15) * C.α ≤ C.α := by
  have h₀ : C.N ≠ 0 := C.hN
  have h₁ : C.N / 3 ≤ 2 * C.N / 3 := Nat.div_le_div_right (Nat.le_mul_of_pos_left (Nat.le_succ _))
  have h₂ : 2 * C.N / 3 ≤ C.N :=
    Nat.div_le_of_le_mul (Nat.mul_le_mul_of_nonneg_right (Nat.le_succ _))
  have h₃ : range (C.N / 3) ∪ Ico (C.N / 3) (2 * C.N / 3) ∪ Ico (2 * C.N / 3) C.N = range C.N
  · rw [range_eq_Ico, Ico_union_Ico_eq_Ico (Nat.zero_le _) h₁
      Ico_union_Ico_eq_Ico (Nat.zero_le _) h₂]
  have h₆ : 0 < C.N / 3 := (Nat.div_pos (hC.trans' (show 3 ≤ 24, by norm_num)) (by norm_num))
  have h₇ : C.N / 3 ≤ C.N - 2 * C.N / 3
  · rw le_tsub_iff_left h₂
    refine (Nat.add_div_le_add_div _ _ _).trans _
    rw [← add_one_mul, ← bit1, Nat.mul_div_cancel_left]
    norm_num
  have h₇' : ((C.N / 3 : ℕ) : ℝ) ≤ ((C.N - 2 * C.N / 3 : ℕ) : ℝ)
  · rwa Nat.cast_le
  have h₈ : ((C.N - 2 * C.N / 3 : ℕ) : ℝ) ≤ 3 * C.N / 8
  · refine (ceil_third hC).trans' _
    rw [← Nat.cast_add_one, Nat.cast_le]
    refine (diff_thirds 2 _).2.trans_eq' _
    simp
  have : 2 * C.α * C.N / 5 ≤ (C.A ∩ range (C.N / 3)).card ∨
         2 * C.α * C.N / 5 ≤ (C.A ∩ Ico (2 * C.N / 3) C.N).card
  · by_contra'
    refine not_le_of_lt (add_lt_add_of_le_of_lt (add_le_add this.1.le h3.le) this.2) _
    rw [← add_div, ← add_div, mul_assoc, ← add_one_mul, ← add_mul, ← Nat.cast_add, ← Nat.cast_add
      range_eq_Ico, ← card_disjoint_union, ← inter_distrib_left, ← card_disjoint_union
      ← inter_distrib_left, ← range_eq_Ico, h₃, config.α_eq, ← bit1, ← bit1_add', ← bit0
      mul_div_cancel_left, (inter_eq_left_iff_subset _ _).2 C.hAN]
    · norm_num
    · refine disjoint.inf_left' _ (disjoint.inf_right' _ _)
      rw [Ico_union_Ico_eq_Ico (Nat.zero_le _) h₁]
      exact Ico_disjoint_Ico_consecutive _ _ _
    · refine disjoint.inf_left' _ (disjoint.inf_right' _ _)
      exact Ico_disjoint_Ico_consecutive _ _ _
  cases this with h₄ h₄
  · refine ⟨⟨C.N / 3, C.A ∩ range (C.N / 3), h₆.ne', inter_subset_right _ _, _⟩, _, _⟩
    · exact C.hA.mono (by simp only [coe_inter, set.inter_subset_left])
    · exact floor_third (hC.trans' (by norm_num))
    · rw [config.α_def (config.mk _ _ _ _ _), le_div_iff (config.cast_N_pos _)]
      refine h₄.trans' _
      refine (mul_le_mul_of_nonneg_left (h₇'.trans h₈) (mul_nonneg (by norm_num)
        (config.α_nonneg _))).trans _
      linarith only
  · have h₅ : 2 * C.N / 3 + (C.N - 2 * C.N / 3) = C.N
    · rw [add_tsub_cancel_of_le h₂]
    have h₉ : C.N - 2 * C.N / 3 ≠ 0 := (h₇.trans_lt' h₆).ne'
    refine ⟨config_of_subset_Ico (inter_subset_right C.A (Ico (2 * C.N / 3) C.N)) h₉ h₅
      (C.hA.mono (inter_subset_left _ _)), _, _⟩
    · exact (floor_third (hC.trans' (by norm_num))).trans h₇'
    rw [config.α_def (config_of_subset_Ico _ _ _ _), le_div_iff (config.cast_N_pos _)
      card_config_of_subset_Ico]
    refine h₄.trans' _
    refine (mul_le_mul_of_nonneg_left h₈ (mul_nonneg (by norm_num)
      (config.α_nonneg _))).trans _
    linarith only
end

lemma middle_AP {N : ℕ} (hN : Odd N) {A : Finset ℕ} (hA : A ⊆ range N) {x d : ZMod N} (hd : d ≠ 0)
  (hx : x ∈ A.image (coe : ℕ → ZMod N))
  (hy : x + d ∈ (A ∩ Ico (N / 3) (2 * N / 3)).image (coe : ℕ → ZMod N))
  (hz : x + 2 * d ∈ (A ∩ Ico (N / 3) (2 * N / 3)).image (coe : ℕ → ZMod N)) :
  ¬ add_salem_spencer (A : set ℕ) := by
  simp only [mem_image, exists_prop, mem_inter, mem_Ico] at hx hy hz
  have : 2 * (x + d) - (x + 2 * d) = x
  · ring
  obtain ⟨x', hx', hx'''⟩ := hx
  obtain ⟨y', ⟨hy', hy''⟩, hy'''⟩ := hy
  obtain ⟨z', ⟨hz', hz''⟩, hz'''⟩ := hz
  have : (x' : ZMod N) + z' = y' + y'
  · rw [hx''', hy''', hz''']
    ring
  have : (x' : ZMod N) = y' + y' - z'
  · rw [hx''', hy''', hz''']
    ring
  have xl : z' ≤ y' + y'
  · rw ← two_mul
    refine (Nat.mul_le_mul_left _ hy''.1).trans' _
    rw ← Nat.lt_add_one_iff
    refine hz''.2.trans_le _
    rw [two_mul, Nat.add_div, ← two_mul, add_le_add_iff_left]
    · split_ifs;
      simp
    norm_num
  have xu : y' + y' - z' < N
  · rw [tsub_lt_iff_left xl, ← two_mul]
    refine (Nat.mul_lt_mul_of_pos_left hy''.2 (by norm_num1)).trans_le
      ((Nat.mul_div_le_mul_div_assoc _ _ _).trans ((add_le_add_right hz''.1 _).trans_eq' _))
    rw [← Nat.add_mul_div_left, ← mul_assoc, ← one_add_mul];
    norm_num
  rw [← Nat.cast_add, ← Nat.cast_sub xl, ZMod.nat_coe_eq_nat_coe_iff', Nat.mod_eq_of_lt xu
    Nat.mod_eq_of_lt (mem_range.1 (hA hx'))] at this
  rw [add_salem_spencer_iff_eq_right]
  simp only [not_forall, mem_coe, exists_prop, exists_and_distrib_left]
  refine ⟨x', z', y', _, hy', hz', hx', _⟩
  · rw [this, Nat.sub_add_cancel xl]
  rintro rfl
  apply hd
  simpa [hx'''] using hy'''
end

open Multiplicative

lemma full_middle (C : config) [NeZero C.N] (hC : Odd C.N) (hN : 50 / C.α ^ 3 < C.N) (hα : 0 < C.α)
  (h3 : C.α * C.N / 5 ≤ (C.A ∩ Ico (C.N / 3) (2 * C.N / 3)).card) :
  ∃ r : ZMod C.N, r ≠ 0 ∧
    C.α ^ 2 / 10 <
      (dft (𝟭 (C.A.image (λ i, ofAdd (i : ZMod C.N)))) (to_character C.N (ofAdd r))).abs := by
  haveI : NeZero C.N := ⟨C.hN⟩
  let A : Finset (ZMod C.N) := C.A.image coe
  let B : Finset (ZMod C.N) := (C.A ∩ Ico (C.N / 3) (2 * C.N / 3)).image coe
  have hA : set.inj_on (coe : ℕ → ZMod C.N) C.A
  · intros i hi j hj h
    rwa [ZMod.nat_coe_eq_nat_coe_iff', Nat.mod_eq_of_lt, Nat.mod_eq_of_lt] at h
    · exact mem_range.1 (C.hAN hj)
    · exact mem_range.1 (C.hAN hi)
  have hα : C.α ≤ A.card / C.N
  · rw [card_image_of_inj_on hA]
    refl
  have hβ : C.α / 5 ≤ B.card / C.N
  · rwa [card_image_of_inj_on (hA.mono (inter_subset_left _ _)), le_div_iff (config.cast_N_pos _)
      div_mul_eq_mul_div]
  have hβ' : 0 ≤ C.α / 5
  · have := C.α_nonneg
    positivity
  by_contra'
  have bound : 1 / (C.N : ℝ) < C.α * (C.α / 5) * (C.α / 5) / 2
  · rw [mul_div_assoc', mul_div_assoc', div_mul_eq_mul_div, div_div, div_div
      one_div_lt (config.cast_N_pos _), one_div_div]
    · refine hN.trans_eq' _
      rw [pow_succ, sq, mul_assoc]
      norm_num
    positivity
  have h : ∀ (r : ZMod C.N), r ≠ 0 →
    (dft (𝟭 (image ofAdd A)) (to_character C.N (ofAdd r))).abs ≤
      C.α * real.sqrt (C.α / 5 * (C.α / 5)) / 2
  · intros r hr
    rw [image_image]
    refine (this r hr).trans_eq _
    rw [real.sqrt_mul_self hβ', sq, mul_div_assoc', div_div]
    norm_num
  obtain ⟨x, d, hd, hA, hB, hB'⟩ := one_five' hC hα hβ hβ hβ' hβ' h bound
  exact middle_AP hC C.hAN hd hA hB hB' C.hA
end

def density_change (k δ : ℝ) : ℝ := δ * (1 + δ / k)

lemma density_change_gt {k δ : ℝ} (hk : 0 < k) (hδ : 0 < δ) : δ < density_change k δ := by
  refine lt_mul_right hδ _
  rw lt_add_iff_pos_right
  positivity
end

lemma density_change_mono {k δ₁ δ₂ : ℝ} (hk : 0 ≤ k) (hδ₁ : 0 ≤ δ₁) (hδ₂ : δ₁ ≤ δ₂) :
  density_change k δ₁ ≤ density_change k δ₂ :=
mul_le_mul hδ₂ (add_le_add_left (div_le_div_of_le_of_nonneg hδ₂ hk) _)
  (add_nonneg zero_le_one (div_nonneg hδ₁ hk)) (by linarith)

open real

-- 16 ≤ (C₁.α ^ 6 * C₁.N) / (640 * π) ^ 3
-- 16 * (640 * π) ^ 3 ≤ C₁.α ^ 6 * C₁.N
-- 16 * (640 * π) ^ 3 / C₁.α ^ 6 ≤ C₁.N

lemma one_step (C : config) (hC : (90 / C.α) ^ 6 ≤ C.N) (hC' : 0 < C.α) :
  ∃ C : config, (C.N : ℝ) ^ (1 / 3 : ℝ) ≤ C.N ∧ density_change 40 C.α ≤ C.α := by
  obtain ⟨C₁, hC₁, hC₁', hC₁''⟩ := make_odd C
  have : C₁.N ≠ 0 := (Odd.pos hC₁).ne'
  have h' := hC'.trans_le hC₁''
  haveI : NeZero C₁.N := ⟨this⟩
  have h₃ : (90 / C₁.α) ^ 6 / 4 ≤ C₁.N
  · refine (div_le_div_of_le (by norm_num) (hC.trans' _)).trans hC₁'
    exact pow_le_pow_of_le_left (by positivity)
      (div_le_div_of_le_left (by norm_num1) hC' hC₁'') _
  have h₄ : 132860250000 / C₁.α ^ 6 ≤ C₁.N
  · refine h₃.trans' _
    rw [div_pow, div_div, mul_comm, ← div_div]
    norm_num
  rw [div_le_iff' (show (0 : ℝ) < 4, by norm_num)] at hC₁'
  cases lt_or_le ((C₁.A ∩ Ico (C₁.N / 3) (2 * C₁.N / 3)).card : ℝ) (C₁.α * C₁.N / 5)
  · have : 24 ≤ C₁.N
    · rw [←  @Nat.cast_le ℝ]
      refine h₄.trans' ((div_le_div_of_le_left _ (pow_pos h' _) (C₁.α_pow_le_one _)).trans' _);
      norm_num
    obtain ⟨C₂, hC₂, hC₂'⟩ := empty_middle C₁ this h
    refine ⟨C₂, _, (density_change_mono (by positivity) C.α_nonneg hC₁'').trans (hC₂'.trans' _)⟩
    · refine hC₂.trans' ((rpow_le_rpow (Nat.cast_nonneg _) hC₁' (by norm_num)).trans _)
      rw [← rpow_le_rpow_iff, ← rpow_mul, div_mul_cancel _ (show (3 : ℝ) ≠ 0, by norm_num), rpow_one
        (show (3 : ℝ) = (3 : ℕ), by norm_cast), rpow_nat_cast, div_pow, le_div_iff', ← mul_assoc
        ← pow_succ', pow_succ' _ 2]
      refine mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      · norm_cast
        refine (pow_le_pow_of_le_left _ this 2).trans' _;
        norm_num
      all_goals · positivity
    rw [density_change, mul_comm]
    nlinarith [C₁.α_le_one, C₁.α_nonneg]
  have h₅ : C₁.α ^ 2 / 10 ≤ 1
  · refine div_le_one_of_le _ (by norm_num)
    refine (pow_le_pow_of_le_left h'.le C₁.α_le_one _).trans _
    norm_num
  have := pi_pos
  have h₆ : 16 * π / (C₁.α ^ 2 / 10) ≤ C₁.N
  · refine h₄.trans' _
    rw [div_div_eq_mul_div, le_div_iff (pow_pos h' _), div_mul_comm, div_eq_mul_inv
      ← pow_sub_of_lt _ (show 2 < 6, by norm_num), mul_assoc _ π, mul_left_comm _ π]
    refine (mul_le_of_le_one_left (by positivity) (C₁.α_pow_le_one _)).trans _
    refine (mul_le_mul_of_nonneg_right pi_lt_315.le (by norm_num)).trans _
    norm_num
  have h₇ : 50 / C₁.α ^ 3 < C₁.N
  · refine h₄.trans_lt' _
    rw [lt_div_iff (pow_pos h' _), div_mul_comm, div_eq_mul_inv
      ← pow_sub_of_lt _ (show 3 < 6, by norm_num)]
    refine (mul_le_of_le_one_left (by positivity) (C₁.α_pow_le_one _)).trans_lt _
    norm_num
  obtain ⟨r, hr, hr'⟩ := full_middle C₁ hC₁ h₇ h' h
  obtain ⟨p, i, n, d, hd, size_lower_bound, hp, density_lower_bound⟩ :=
    find_subprogression _ C₁.α _ hr h₆ C₁.hAN rfl (by positivity) h₅ hr'.le
  have hp' : p.card = n
  · rw [hp, card_image_of_injective _ (injective_affine hd), card_range]
  have : n ≠ 0
  · have h : 0 < sqrt (C₁.α ^ 2 / 10 * C₁.N / (64 * π))
    · positivity
    replace h := h.trans_le size_lower_bound
    rwa [hp', Nat.cast_pos, pos_iff_ne_zero] at h
  let A := (range n).filter (fun x ↦ i + d * x ∈ C₁.A)
  have A : A.image (fun x ↦ i + d * x) = C₁.A ∩ p
  · rw [inter_comm, ← filter_mem_eq_inter, hp, image_filter]
  have A'' : A.card = (C₁.A ∩ p).card
  · rw [← A, card_image_of_injective _ (injective_affine hd)]
  refine ⟨⟨n, A, this, filter_subset _ _, _⟩, _, _⟩
  · intros x y z
    simp only [A, Finset.mem_coe, and_imp, mem_filter, mem_range]
    intros hx hx' hy hy' hz hz' e
    refine injective_affine hd (C₁.hA hx' hy' hz' _)
    rw [add_assoc, add_assoc, add_right_inj, add_left_comm, add_left_comm (d * z), add_right_inj
      ← mul_add, e, mul_add]
  · dsimp
    have h : 0 < C₁.α ^ 2 * C₁.N / (10 * (64 * π))
    · positivity
    rw ← hp'
    refine size_lower_bound.trans' _
    rw [← real.rpow_le_rpow_iff (rpow_nonneg_of_nonneg (Nat.cast_nonneg _) _) (real.sqrt_nonneg _)
      (show (0 : ℝ) < 3, by norm_num), div_mul_eq_mul_div, div_div, ← rpow_mul (Nat.cast_nonneg _)
      div_mul_cancel _ (show (3 : ℝ) ≠ 0, by norm_num), rpow_one, sqrt_eq_rpow, ← rpow_mul h.le
      mul_comm (1 / 2 : ℝ), rpow_mul h.le, ← sqrt_eq_rpow]
    refine hC₁'.trans _
    rw [le_sqrt (mul_nonneg (show (0 : ℝ) ≤ 4, by norm_num) (Nat.cast_nonneg _))
      (rpow_pos_of_pos h _).le, (show (3 : ℝ) = (3 : ℕ), by norm_cast), rpow_nat_cast
      ← div_mul_eq_mul_div, mul_pow, mul_pow, pow_succ (C₁.N : ℝ) 2, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right _ (by positivity)
    rw [← div_le_iff', div_pow, div_div_eq_mul_div, ← pow_mul, ← bit0_eq_two_mul, mul_pow, mul_pow
      ← mul_assoc, ← mul_assoc]
    swap
    · positivity
    refine h₄.trans' (div_le_div_of_le (by positivity) _)
    refine (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_left pi_pos.le pi_lt_315.le _)
      (by positivity)).trans _
    norm_num

  rw [config.α_def (config.mk _ _ _ _ _), le_div_iff (config.cast_N_pos _)]
  rw [div_div, sq, mul_div_assoc, ← mul_one_add] at density_lower_bound
  norm_num1 at density_lower_bound
  dsimp
  rw [← hp', A'']
  refine (mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)).trans density_lower_bound
  exact density_change_mono (by norm_num) C.α_nonneg hC₁''
end

end single_step

section final

lemma first_order_bernoulli_lt {x y : ℝ} (hx : 0 < x) (hy : 1 < y) : 1 + y * x < (1 + x) ^ y := by
  let f := fun x ↦ (1 + x) ^ y - (1 + y * x)
  let f' := fun x ↦ 1 * y * (1 + x) ^ (y - 1) - y * 1
  have hf' : ∀ x, f' x = y * ((1 + x) ^ (y - 1) - 1)
  · intro x
    simp only [f']
    ring
  have hf : ∀ z, has_deriv_at f (f' z) z
  · intro z
    exact (((has_deriv_at_id' _).const_add _).rpow_const (or.inr hy.le)).sub
      (((has_deriv_at_id' z).const_mul y).const_add _)
  have hf₁ : continuous f
  · rw continuous_iff_continuous_at
    intro x
    exact (hf x).continuous_at
  have hf₃ : ∀ z ∈ interior (set.Ici (0 : ℝ)), 0 < deriv f z
  · intros z hz
    rw interior_Ici at hz
    simp only [(hf z).deriv, hf', one_mul]
    refine mul_pos (by linarith) (sub_pos_of_lt _)
    exact (real.one_lt_rpow (lt_add_of_pos_right _ hz) (sub_pos_of_lt hy))
  have := convex.strict_mono_on_of_deriv_pos (convex_Ici 0) hf₁.continuous_on
    hf₃ set.left_mem_Ici hx.le hx
  simp only [f] at this
  simpa using this
end

lemma first_order_bernoulli_le {x y : ℝ} (hx : 0 ≤ x) (hy : 1 ≤ y) : 1 + y * x ≤ (1 + x) ^ y := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  rcases hy.eq_or_lt with rfl | hy
  · simp
  exact (first_order_bernoulli_lt hx hy).le
end

lemma second_order_bernoulli_lt {x y : ℝ} (hx : 0 < x) (hy : 2 < y) :
  1 + y * x + y * (y - 1) / 2 * x ^ 2 < (1 + x) ^ y := by
  let f := fun x ↦ (1 + x) ^ y - (1 + (y * x + y * (y - 1) / 2 * x ^ 2))
  let f' := fun x ↦ 1 * y * (1 + x) ^ (y - 1) - (y * 1 + y * (y - 1) / 2 * ((2 : ℕ) * x ^ 1))
  have hf' : ∀ x, f' x = y * ((1 + x) ^ (y - 1) - (1 + (y - 1) * x))
  · intro x
    simp only [f', Nat.cast_two, pow_one]
    ring
  have hf : ∀ z, has_deriv_at f (f' z) z
  · intro z
    refine has_deriv_at.sub _ _
    · exact (has_deriv_at.rpow_const ((has_deriv_at_id' _).const_add _) (or.inr (by linarith)))
    refine (((has_deriv_at_id' _).const_mul y).add (has_deriv_at.const_mul _ _)).const_add _
    refine has_deriv_at_pow _ _
  have hf₁ : continuous f
  · rw continuous_iff_continuous_at
    intro x
    exact (hf x).continuous_at
  have hf₃ : ∀ z ∈ interior (set.Ici (0 : ℝ)), 0 < deriv f z
  · intros z hz
    rw interior_Ici at hz
    simp only [(hf z).deriv, hf', one_mul]
    refine mul_pos (by linarith) _
    rw sub_pos
    exact first_order_bernoulli_lt hz (by linarith)
  have := convex.strict_mono_on_of_deriv_pos (convex_Ici 0) hf₁.continuous_on hf₃ set.left_mem_Ici
    hx.le hx
  simp only [f] at this
  simpa [add_assoc] using this
end

lemma second_order_bernoulli_le {x y : ℝ} (hx : 0 ≤ x) (hy : 2 ≤ y) :
  1 + y * x + y * (y - 1) / 2 * x ^ 2 ≤ (1 + x) ^ y := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  rcases hy.eq_or_lt with rfl | hy
  · norm_cast, ring_nf
  exact (second_order_bernoulli_lt hx hy).le
end


lemma density_change_iterate_gt {k δ : ℝ} {m : ℕ} (hk : 0 < k) (hδ : 0 < δ) :
  δ ≤ (density_change k^[m] δ) := by
  induction m
  · simp
  apply m_ih.trans _
  rw function.iterate_succ_apply'
  exact (density_change_gt hk (hδ.trans_le m_ih)).le
end

lemma density_change_iterate_le {k δ : ℝ} {m n : ℕ} (hk : 0 < k) (hδ : 0 < δ) (hmn : m ≤ n) :
  (density_change k^[m] δ) ≤ (density_change k^[n] δ) := by
  obtain ⟨_, rfl⟩ := exists_add_of_le hmn
  rw [add_comm, function.iterate_add_apply]
  exact density_change_iterate_gt hk (hδ.trans_le (density_change_iterate_gt hk hδ))
end

lemma density_change_pos {k δ : ℝ} (hk : 0 < k) (hδ : 0 < δ) : 0 < density_change k δ :=
hδ.trans (density_change_gt hk hδ)

lemma density_change_iterate_pos {k δ : ℝ} {m : ℕ} (hk : 0 < k) (hδ : 0 < δ) :
  0 < (density_change k^[m] δ) :=
hδ.trans_le (density_change_iterate_gt hk hδ)

lemma density_change_iterate_mono {k δ₁ δ₂ : ℝ} {m : ℕ} (hk : 0 < k) (hδ₁ : 0 < δ₁)
  (hδ₂ : δ₁ ≤ δ₂) :
  density_change k^[m] δ₁ ≤ (density_change k^[m] δ₂) := by
  induction m with m ih
  · simp [hδ₂]
  rw [function.iterate_succ_apply', function.iterate_succ_apply']
  exact density_change_mono hk.le (density_change_iterate_pos hk hδ₁).le ih
end

lemma helper {k δ x : ℝ} (hk : 0 < k) (hδ : 0 < δ) (hx : 1 ≤ x) :
  density_change k δ * x ≤ density_change k (δ * x) := by
  rw [density_change, density_change, mul_right_comm]
  refine mul_le_mul_of_nonneg_left (add_le_add_left _ _) (by nlinarith)
  exact div_le_div_of_le_of_nonneg (by nlinarith) hk.le
end

lemma density_change_iterate_gt_pow {k δ : ℝ} {m : ℕ} (hk : 0 < k) (hδ : 0 < δ) :
  δ * (1 + δ / k) ^ m ≤ (density_change k^[m] δ) := by
  induction m with m ih
  · simp
  rw function.iterate_succ_apply'
  refine ((helper hk hδ _).trans_eq' _).trans (density_change_mono hk.le _ ih)
  · refine one_le_pow_of_one_le _ _
    simp only [le_add_iff_nonneg_right]
    positivity
  · rw [pow_succ, ← mul_assoc]
    refl
  positivity
end

lemma density_change_basic {k δ : ℝ} {m : ℕ} (hk : 0 < k) (hδ : 0 < δ) :
  δ * (1 + m * (δ / k)) ≤ (density_change k^[m] δ) :=
(density_change_iterate_gt_pow hk hδ).trans' $ by
  refine mul_le_mul_of_nonneg_left (one_add_mul_le_pow _ _) hδ.le
  exact (div_nonneg hδ.le hk.le).trans' (by norm_num)
end

lemma density_change_daniel {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 3) :
  2 * δ ≤ (density_change 40^[⌊40 / δ⌋₊] δ) := by
  have h₁ : 3 / 2 * δ ≤ (density_change 40^[⌈20 / δ⌉₊] δ)
  · rw [mul_comm]
    refine (density_change_basic (by norm_num) hδ).trans' (mul_le_mul_of_nonneg_left _ hδ.le)
    have : (1 / 2 : ℝ) ≤ ⌈20 / δ⌉₊ * (δ / 40)
    · refine (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)).trans_eq' _
      rw div_mul_div_cancel _ hδ.ne'
      norm_num
    linarith
  have h₂ : 2 * δ ≤ (density_change 40^[⌈(80 / 9) / δ⌉₊] (3 / 2 * δ))
  · refine (density_change_basic (by norm_num) _).trans' _
    · linarith
    rw mul_right_comm
    refine mul_le_mul_of_nonneg_right _ hδ.le
    have : (1 / 3 : ℝ) ≤ ↑⌈(80 / 9) / δ⌉₊ * (3 / 2 * δ / 40)
    · refine (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)).trans_eq' _
      rw [div_mul_div_comm, mul_comm _ δ, mul_div_assoc, mul_div_mul_left _ _ hδ.ne']
      norm_num
    rw [← div_le_iff', ← sub_le_iff_le_add']
    · norm_num [this]
    · norm_num
  have h₃ : (⌈20 / δ⌉₊ : ℝ) + ⌈(80 / 9) / δ⌉₊ ≤ ⌊40 / δ⌋₊
  · refine (add_le_add (Nat.ceil_lt_add_one (by positivity)).le
      (Nat.ceil_lt_add_one _).le).trans ((Nat.sub_one_lt_floor _).le.trans' _)
    · positivity
    rw [div_add_one hδ.ne', div_sub_one hδ.ne', div_add_one hδ.ne', div_add_div_same]
    apply div_le_div_of_le_of_nonneg _ hδ.le
    linarith
  refine h₂.trans ((density_change_iterate_mono (by norm_num) _ h₁).trans _)
  · positivity
  rw [← function.iterate_add_apply, add_comm]
  refine density_change_iterate_le (by norm_num) hδ (by exact_mod_cast h₃)
end

lemma density_change_third {k δ : ℝ} {m : ℕ} (hk : 0 < k) (hδ : 0 < δ) (hm : 2 ≤ m):
  δ * (1 + m * δ / k + m * (m - 1) / 2 * δ ^ 2 / k ^ 2) ≤ (density_change k^[m] δ) := by
  refine ((density_change_iterate_gt_pow hk hδ).trans' (mul_le_mul_of_nonneg_left _ hδ.le))
  rw [← real.rpow_nat_cast _ m, mul_div_assoc, mul_div_assoc, ← div_pow]
  exact (second_order_bernoulli_le (by positivity) (by exact_mod_cast hm))
end

lemma density_change_me {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
  2 * δ ≤ (density_change 40^[⌊40 / δ⌋₊] δ) := by
  refine (density_change_third (by norm_num) hδ _).trans' _
  · rw [Nat.le_floor_iff', le_div_iff hδ, Nat.cast_two]
    · linarith
    · linarith
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_left _ hδ.le
  have : 40 / δ - 1 ≤ ⌊40 / δ⌋₊ := (Nat.sub_one_lt_floor _).le
  have : 1 + (40 / δ - 1) * δ / 40 + (40 / δ - 1) * (40 / δ - 1 - 1) / 2 * δ ^ 2 / 40 ^ 2 ≤
    1 + (⌊40 / δ⌋₊ : ℝ) * δ / 40 + ⌊40 / δ⌋₊ * (⌊40 / δ⌋₊ - 1) / 2 * δ ^ 2 / 40 ^ 2
  · refine add_le_add_three le_rfl (by nlinarith) _
    refine div_le_div_of_le_of_nonneg (mul_le_mul_of_nonneg_right _ (by nlinarith)) (by norm_num)
    refine div_le_div_of_le_of_nonneg (mul_le_mul this (by linarith) _ (by simp)) (by norm_num)
    rw [le_sub_iff_add_le, le_sub_iff_add_le, le_div_iff hδ, ← le_div_iff']
    · norm_num1, linarith
    · norm_num
  refine this.trans' _
  field_simp [hδ.ne']
  rw le_div_iff
  · ring_nf SOP
    nlinarith
  positivity
end

lemma density_change_overall {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1) :
  ∃ m ≤ ⌊80 / δ⌋₊, 1 < (density_change 40^[m] δ) := by
  have ih : ∀ n, 2 ^ n * δ ≤ 1 →
    2 ^ (n + 1) * δ ≤ (density_change 40^[∑ i in range (n+1), ⌊40 / (2 ^ i * δ)⌋₊] δ)
  · intro n
    induction n with n ih
    · simp only [pow_zero, one_mul, pow_one, range_one, sum_singleton]
      exact density_change_me hδ
    intro hδ'
    refine ((density_change_me (by positivity) hδ').trans_eq' _).trans _
    · rw [← mul_assoc, ← pow_succ]
    have : 2 ^ n * δ ≤ 1 :=
      hδ'.trans' (mul_le_mul_of_nonneg_right (pow_le_pow (by norm_num) (Nat.le_succ _)) hδ.le)
    refine (density_change_iterate_mono (by norm_num) _ (ih this)).trans _
    · positivity
    rw [sum_range_succ _ (n+1), ← function.iterate_add_apply, add_comm]
  let n := ⌊- real.logb 2 δ⌋₊
  have : ∑ (i : ℕ) in range (n + 1), ⌊40 / (2 ^ i * δ)⌋₊ ≤ ⌊80 / δ⌋₊
  · rw [Nat.le_floor_iff (show 0 ≤ 80 / δ, by positivity), Nat.cast_sum]
    have : ∑ x in range (n + 1), (⌊40 / (2 ^ x * δ)⌋₊ : ℝ) ≤
      ∑ x in range (n + 1), 40 / (2 ^ x * δ)
    · exact sum_le_sum (λ i hi, Nat.floor_le (by positivity))
    refine this.trans _
    simp_rw [← div_div, ← sum_div, div_eq_mul_inv, range_eq_Ico, ← inv_pow, ← mul_sum]
    refine mul_le_mul_of_nonneg_right _ (by positivity)
    refine (mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one (by norm_num) _) _).trans_eq _
    · norm_num
    · norm_num
    · norm_num
  refine ⟨_, this, _⟩
  refine (ih _ _).trans_lt' _
  · rw [← le_div_iff hδ, ← real.rpow_nat_cast, ← real.le_logb_iff_rpow_le, one_div, real.logb_inv]
    · apply Nat.floor_le _
      rw neg_nonneg
      exact real.logb_nonpos (by norm_num) hδ.le hδ'
    · norm_num
    · positivity
  rw [← div_lt_iff hδ, one_div, ← real.rpow_nat_cast, ← real.logb_lt_iff_lt_rpow, real.logb_inv
    Nat.cast_add_one]
  · exact Nat.lt_floor_add_one _
  · norm_num
  · positivity
end

lemma density_change_overall' {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1) :
  1 < (density_change 40^[⌊80 / δ⌋₊] δ) := by
  obtain ⟨m, hm, hm'⟩ := density_change_overall hδ hδ'
  exact hm'.trans_le (density_change_iterate_le (by norm_num) hδ hm)
end

open real

theorem almost_there {C : config} (h : 0 < C.α) :
  (C.N : ℝ) ^ (((1 / 3) : ℝ) ^ (⌊80 / C.α⌋₊)) ≤ (90 / C.α) ^ 6 := by
  have : ∀ i, ∃ Ci : config, 0 < Ci.α ∧
    ((C.N : ℝ) ^ ((1 / 3 : ℝ) ^ i) ≤ Ci.N ∧ (density_change 40^[i] C.α ≤ Ci.α) ∨
      (C.N : ℝ) ^ ((1 / 3 : ℝ) ^ i) ≤ (90 / C.α) ^ 6)
  · intro i
    induction i with i ih
    · exact ⟨C, h, by simp⟩
    obtain ⟨C', hC'₁, hC'⟩ := ih
    rw [or_iff_not_imp_right, not_le] at hC'
    rw [pow_succ', real.rpow_mul (Nat.cast_nonneg _)]
    cases lt_or_le ((90 / C.α) ^ 6) ((C.N : ℝ) ^ (1 / 3 : ℝ) ^ i) with h' h'
    · obtain ⟨hC'₂, hC'₃⟩ := hC' h'
      have : (90 / C.α) ^ 6 ≤ (90 / C.α) ^ 6
      · refine pow_le_pow_of_le_left (by positivity) (div_le_div_of_le_left (by norm_num) h _) _
        exact hC'₃.trans' (density_change_iterate_gt (by norm_num) h)
      obtain ⟨C'', hC''₁, hC''₂⟩ := one_step C (hC'₂.trans' (h'.le.trans' this)) hC'₁
      refine ⟨C'', hC''₂.trans_lt' (density_change_pos (by norm_num) hC'₁), or.inl ⟨_, _⟩⟩
      · exact hC''₁.trans' (real.rpow_le_rpow (by positivity) hC'₂ (by positivity))
      rw function.iterate_succ_apply'
      exact hC''₂.trans' (density_change_mono (by positivity)
        (density_change_iterate_pos (by positivity) h).le hC'₃)
    refine ⟨C, hC'₁, or.inr (h'.trans' _)⟩
    refine (real.rpow_le_rpow_of_exponent_le _ (show (1 / 3 : ℝ) ≤ 1, by norm_num)).trans_eq
      (real.rpow_one _)
    refine real.one_le_rpow _ (by positivity)
    rw [Nat.one_le_cast, Nat.succ_le_iff, pos_iff_ne_zero]
    exact C.hN
  obtain ⟨C, hC'₁, hC'⟩ := this ⌊80 / C.α⌋₊
  refine hC'.resolve_left (λ h', _)
  exact not_lt_of_le C.α_le_one (h'.2.trans_lt' (density_change_overall' h C.α_le_one))
end


lemma bit_more_precise {C : config} (h : 0 < C.α) (h' : 1 < C.N) :
  log (log C.N) ≤ (80 * log 3) / C.α + log (log (90 / C.α)) + log 6 := by
  have := C.cast_N_pos
  have : 0 < log (90 / C.α)
  · exact log_pos ((one_lt_div h).2 (C.α_le_one.trans_lt (by norm_num)))
  have : 0 < log C.N
  · refine log_pos _
    rwa Nat.one_lt_cast
  have := almost_there h
  rw [← log_le_log, log_rpow, log_pow, ← log_le_log, log_mul, log_pow, log_mul, one_div, log_inv
    mul_neg, neg_add_le_iff_le_add, ← add_assoc, add_right_comm, Nat.cast_bit0, Nat.cast_bit1
    Nat.cast_one] at this
  · refine this.trans (add_le_add_right (add_le_add_right _ _) _)
    rw ← div_mul_eq_mul_div
    exact mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (log_nonneg (by norm_num))
  all_goals · positivity
end

lemma bound_one {x : ℝ} (hx : 1 ≤ x) : log (90 * x) ≤ 5 * x := by
  rw [log_mul (by positivity : (90 : ℝ) ≠ 0) (by positivity : x ≠ 0), ← le_sub_iff_add_le']
  refine (log_le_sub_one_of_pos (by positivity)).trans _
  suffices : log 90 ≤ 5
  · linarith
  rw [log_le_iff_le_exp (show (0 : ℝ) < 90, by norm_num), ← exp_one_rpow]
  norm_cast
  have : 2.7 ≤ exp 1 := exp_one_gt_d9.le.trans' (by norm_num)
  refine (pow_le_pow_of_le_left _ this _).trans' _;
  norm_num
end

lemma bound_two {x : ℝ} (hx : 1 ≤ x) : log (5 * x) + log 6 ≤ 4 * x := by
  rw [log_mul (by positivity : (5 : ℝ) ≠ 0) (by positivity : x ≠ 0), add_right_comm
    ← le_sub_iff_add_le', ← log_mul (show (5 : ℝ) ≠ 0, by norm_num) (show (6 : ℝ) ≠ 0, by norm_num)]
  refine (log_le_sub_one_of_pos (by positivity)).trans _
  suffices : log 30 ≤ 4
  · norm_num1
    linarith
  rw [log_le_iff_le_exp (show (0 : ℝ) < 30, by norm_num), ← exp_one_rpow]
  norm_cast
  have : 2.7 ≤ exp 1 := exp_one_gt_d9.le.trans' (by norm_num)
  refine (pow_le_pow_of_le_left _ this _).trans' _;
  norm_num
end

lemma bound_three {x : ℝ} (hx : 1 ≤ x) : log (log (90 * x)) + log 6 ≤ 4 * x := by
  refine (bound_two hx).trans' (add_le_add_right ((log_le_log (log_pos (by linarith)) _).2 _) _)
  · positivity
  exact bound_one hx
end

lemma second_last {C : config} (h : 0 < C.α) (h' : 1 < C.N) : log (log C.N) ≤ 100 / C.α := by
  refine (bit_more_precise h h').trans _
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, add_assoc, ← le_sub_iff_add_le', ← sub_mul]
  refine (bound_three (one_le_inv h C.α_le_one)).trans (mul_le_mul_of_nonneg_right _ _)
  swap
  · positivity
  suffices : ((10 : ℕ) : ℝ) * log 3 ≤ ((11 : ℕ) : ℝ), · norm_cast at this, linarith
  rw [← log_pow, log_le_iff_le_exp (pow_pos _ _), ← exp_one_rpow, rpow_nat_cast]
  have : 2.715 ≤ exp 1 := exp_one_gt_d9.le.trans' (by norm_num)
  refine (pow_le_pow_of_le_left _ this _).trans' _
  all_goals {norm_num}
end

-- for N = 0 it's trivial, for N = 1, 2 it's false
theorem roth {N : ℕ} (hN : 3 ≤ N) : (roth_number_nat N : ℝ) ≤ 100 * N / log (log N) := by
  obtain ⟨A, hA, hA', hA''⟩ := roth_number_nat_spec N
  rw ← hA'
  have llpos : 0 < log (log N)
  · refine log_pos _
    have : (3 : ℝ) ≤ N, by exact_mod_cast hN
    rw lt_log_iff_exp_lt
    refine (exp_one_lt_d9.trans_le (by linarith))
    linarith
  cases Nat.eq_zero_or_pos A.card
  · rw [h, Nat.cast_zero]
    exact div_nonneg (by positivity) llpos.le
  let C : config := ⟨N, A, by linarith, hA, hA''⟩
  have hN' : 1 < N := by linarith
  have : 0 < C.α
  · refine div_pos _ C.cast_N_pos
    rwa Nat.cast_pos
  have ineq : _ ≤ _ / (_ / _) := second_last this hN'
  dsimp at ineq
  rwa [div_div_eq_mul_div, le_div_iff, ← le_div_iff' llpos] at ineq
  rwa Nat.cast_pos
end

end final
