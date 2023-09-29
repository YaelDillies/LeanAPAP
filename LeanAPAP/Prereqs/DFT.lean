import LeanAPAP.Mathlib.Algebra.BigOperators.Ring
import LeanAPAP.Mathlib.Analysis.Complex.Basic
import LeanAPAP.Mathlib.Logic.Basic
import LeanAPAP.Mathlib.NumberTheory.LegendreSymbol.AddChar.Duality
import LeanAPAP.Prereqs.Convolution.Basic

/-!
# Discrete Fourier transform

This file defines the discrete Fourier transform and shows the Parseval-Plancherel identity and
Fourier inversion formula for it.
-/

attribute [-ext] Complex.ext

open AddChar Finset Function
open Fintype (card)
open scoped BigOperators ComplexConjugate ComplexOrder

variable {α γ : Type*} [AddCommGroup α] [Fintype α] {f : α → ℂ} {ψ : AddChar α ℂ} {n : ℕ}

/-- The discrete Fourier transform. -/
def dft (f : α → ℂ) : AddChar α ℂ → ℂ := λ ψ ↦ ⟪ψ, f⟫_[ℂ]

lemma dft_apply (f : α → ℂ) (ψ : AddChar α ℂ) : dft f ψ = ⟪ψ, f⟫_[ℂ] := rfl

@[simp] lemma dft_zero : dft (0 : α → ℂ) = 0 := by ext; simp [dft_apply]

@[simp] lemma dft_add (f g : α → ℂ) : dft (f + g) = dft f + dft g := by
  ext; simp [l2inner_add_right, dft_apply]

@[simp] lemma dft_sub (f g : α → ℂ) : dft (f - g) = dft f - dft g := by
  ext; simp [l2inner_sub_right, dft_apply]

@[simp] lemma dft_const (a : ℂ) (hψ : ψ ≠ 0) : dft (const α a) ψ = 0 := by
  simp only [dft_apply, l2inner_eq_sum, const_apply, ←sum_mul, ←map_sum,
    sum_eq_zero_iff_ne_zero.2 hψ, map_zero, MulZeroClass.zero_mul]

@[simp] lemma dft_smul [DistribSMul γ ℂ] [Star γ] [StarModule γ ℂ] [SMulCommClass γ ℂ ℂ] (c : γ)
    (f : α → ℂ) : dft (c • f) = c • dft f := by ext; simp [l2inner_smul_right, dft_apply]

/-- **Parseval-Plancherel identity** for the discrete Fourier transform. -/
@[simp] lemma l2inner_dft (f g : α → ℂ) : ⟪dft f, dft g⟫_[ℂ] = card α * ⟪f, g⟫_[ℂ] := by
  classical simp_rw [dft, l2inner_eq_sum, map_sum, map_mul, starRingEnd_self_apply, sum_mul,
    mul_sum, @sum_comm _ _ (AddChar _ _), mul_mul_mul_comm _ (conj $ f _), ←sum_mul, ←
    AddChar.inv_apply_eq_conj, ←map_neg_eq_inv, ←map_add_mul, AddChar.sum_apply_eq_ite,
    add_neg_eq_zero, ite_mul, MulZeroClass.zero_mul, Fintype.sum_ite_eq]

/-- **Parseval-Plancherel identity** for the discrete Fourier transform. -/
lemma L2norm_dft_sq (f : α → ℂ) : ‖dft f‖_[2] ^ 2 = card α * ‖f‖_[2] ^ 2 :=
  Complex.ofReal_injective $ by push_cast; simpa only [l2inner_self] using l2inner_dft f f

/-- **Parseval-Plancherel identity** for the discrete Fourier transform. -/
@[simp] lemma L2norm_dft (f : α → ℂ) : ‖dft f‖_[2] = Real.sqrt (card α) * ‖f‖_[2] := by
  simpa using congr_arg Real.sqrt (L2norm_dft_sq f)

/-- **Fourier inversion** for the discrete Fourier transform. -/
lemma dft_inversion (f : α → ℂ) (a : α) : ∑ ψ : AddChar α ℂ, dft f ψ * ψ a = card α * f a := by
  classical simp_rw [dft, l2inner_eq_sum, sum_mul, @sum_comm _ α, mul_right_comm _ (f _), ←sum_mul,
    ←AddChar.inv_apply_eq_conj, inv_mul_eq_div, ←map_sub_eq_div, AddChar.sum_apply_eq_ite,
    sub_eq_zero, ite_mul, MulZeroClass.zero_mul, Fintype.sum_ite_eq]

lemma dft_dft_doubleDualEmb (f : α → ℂ) (a : α) :
    dft (dft f) (doubleDualEmb a) = card α * f (-a) := by
  simp only [←dft_inversion, mul_comm (conj _), dft_apply, l2inner_eq_sum, map_neg_eq_inv,
    AddChar.inv_apply_eq_conj, doubleDualEmb_apply]

lemma dft_dft (f : α → ℂ) : dft (dft f) = card α * f ∘ doubleDualEquiv.symm ∘ Neg.neg :=
  funext λ a ↦ by
    simp_rw [Pi.mul_apply, Function.comp_apply, map_neg, Pi.nat_apply, ←dft_dft_doubleDualEmb,
      doubleDualEmb_doubleDualEquiv_symm_apply]

lemma dft_injective : Injective (dft : (α → ℂ) → AddChar α ℂ → ℂ) := λ f g h ↦
  funext λ a ↦
    mul_right_injective₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero) $
      (dft_inversion _ _).symm.trans $ by rw [h, dft_inversion]

lemma dft_inv (ψ : AddChar α ℂ) (hf : IsSelfAdjoint f) : dft f ψ⁻¹ = conj (dft f ψ) := by
  simp_rw [dft_apply, l2inner_eq_sum, map_sum, AddChar.inv_apply', map_mul,
    AddChar.inv_apply_eq_conj, Complex.conj_conj, (hf.apply _).conj_eq]

@[simp]
lemma dft_conj (f : α → ℂ) (ψ : AddChar α ℂ) : dft (conj f) ψ = conj (dft f ψ⁻¹) := by
  simp only [dft_apply, l2inner_eq_sum, map_sum, map_mul, ←inv_apply', ←inv_apply_eq_conj,
    inv_inv, Pi.conj_apply]

lemma dft_conjneg_apply (f : α → ℂ) (ψ : AddChar α ℂ) : dft (conjneg f) ψ = conj (dft f ψ) := by
  simp only [dft_apply, l2inner_eq_sum, conjneg_apply, map_sum, map_mul, IsROrC.conj_conj]
  refine' Equiv.sum_comp' (Equiv.neg α) _ _ λ i ↦ _
  simp only [Equiv.neg_apply, ←inv_apply_eq_conj, ←inv_apply', inv_apply]

@[simp]
lemma dft_conjneg (f : α → ℂ) : dft (conjneg f) = conj (dft f) := funext $ dft_conjneg_apply _

@[simp] lemma dft_balance (f : α → ℂ) (hψ : ψ ≠ 0) : dft (balance f) ψ = dft f ψ := by
  simp only [balance, Pi.sub_apply, dft_sub, dft_const _ hψ, sub_zero]

lemma dft_dilate (f : α → ℂ) (ψ : AddChar α ℂ) (hn : n.Coprime (card α)) :
    dft (dilate f n) ψ = dft f (ψ ^ n) := by
  simp_rw [dft_apply, l2inner_eq_sum, dilate]
  refine' sum_nbij' ((n⁻¹ : ZMod (card α)).val • ·) _ (λ x _ ↦ _) (n • ·) _ _ _ <;>
    simp only [pow_apply, ←map_nsmul_pow, mem_univ, nsmul_zmod_val_inv_nsmul hn, zmod_val_inv_nsmul_nsmul hn, eq_self_iff_true,
      forall_const]

@[simp] lemma dft_trivChar [DecidableEq α] : dft (trivChar : α → ℂ) = 1 := by
  ext; simp [trivChar_apply, dft_apply, l2inner_eq_sum, ←map_sum]

@[simp] lemma dft_one : dft (1 : α → ℂ) = card α • trivChar :=
  dft_injective $ by classical rw [dft_smul, dft_trivChar, dft_dft, Pi.one_comp, nsmul_eq_mul]

variable [DecidableEq α]

@[simp] lemma dft_indicate_zero (A : Finset α) : dft (𝟭 A) 0 = A.card := by
  simp only [dft_apply, l2inner_eq_sum, sum_indicate, AddChar.zero_apply, map_one, one_mul]

lemma dft_conv_apply (f g : α → ℂ) (ψ : AddChar α ℂ) : dft (f ∗ g) ψ = dft f ψ * dft g ψ := by
  simp_rw [dft, l2inner_eq_sum, conv_eq_sum_sub', mul_sum, sum_mul, ←sum_product',
    univ_product_univ]
  refine'
    sum_nbij' (λ x ↦ (x.1 - x.2, x.2)) (by simp) (λ x _ ↦ _) (λ x ↦ (x.1 + x.2, x.2))
      (by simp) (by simp) (by simp)
  rw [mul_mul_mul_comm, ←map_mul, ←map_add_mul, add_sub_cancel'_right]

lemma dft_dconv_apply (f g : α → ℂ) (ψ : AddChar α ℂ) :
    dft (f ○ g) ψ = dft f ψ * conj (dft g ψ) := by
  rw [←conv_conjneg, dft_conv_apply, dft_conjneg_apply]

@[simp] lemma dft_conv (f g : α → ℂ) : dft (f ∗ g) = dft f * dft g := funext $ dft_conv_apply _ _

@[simp]
lemma dft_dconv (f g : α → ℂ) : dft (f ○ g) = dft f * conj (dft g) := funext $ dft_dconv_apply _ _

@[simp] lemma dft_iterConv (f : α → ℂ) : ∀ n, dft (f ∗^ n) = dft f ^ n
  | 0 => dft_trivChar
  | n + 1 => by simp [iterConv_succ, pow_succ, dft_iterConv]

lemma lpNorm_conv_le_lpNorm_dconv (hn₀ : n ≠ 0) (hn : Even n) (f : α → ℂ) :
    ‖f ∗ f‖_[n] ≤ ‖f ○ f‖_[n] := by
  cases isEmpty_or_nonempty α
  · rw [Subsingleton.elim (f ∗ f) (f ○ f)]
  refine' le_of_pow_le_pow _ _ hn₀.bot_lt (le_of_mul_le_mul_left _ (_ : (0 : ℝ) < card α ^ n))
  sorry -- positivity
  swap
  sorry -- positivity
  obtain ⟨n, rfl⟩ := hn.two_dvd
  simp_rw [lpNorm_pow_eq_sum hn₀, mul_sum, ←mul_pow, ←nsmul_eq_mul, ←norm_nsmul, nsmul_eq_mul, ←
    dft_inversion, dft_conv, dft_dconv, Pi.mul_apply]
  rw [←Real.norm_of_nonneg (sum_nonneg λ i _ ↦ ?_), ←Complex.norm_real]
  rw [Complex.ofReal_sum (univ : Finset α)]
  any_goals positivity
  simp_rw [pow_mul', ←norm_pow _ n, Complex.ofReal_pow, ←Complex.conj_mul', map_pow, map_sum,
    map_mul, Fintype.sum_pow, Fintype.sum_mul_sum]
  simp only [@sum_comm _ _ α, ←mul_sum, prod_mul_prod_comm]
  refine' (norm_sum_le _ _).trans_eq (Complex.ofReal_injective _)
  simp only [norm_mul, norm_prod, IsROrC.norm_conj, ←pow_mul]
  push_cast
  have : ∀ f g : Fin n → AddChar α ℂ, 0 ≤ ∑ a, ∏ i, conj (f i a) * g i a := by
    rintro f g
    suffices : ∑ a, ∏ i, conj (f i a) * g i a = if ∑ i, (g i - f i) = 0 then (card α : ℂ) else 0
    · rw [this]
      split_ifs <;> positivity
    simp_rw [←AddChar.sum_eq_ite, AddChar.sum_apply, AddChar.sub_apply, AddChar.map_neg_eq_inv,
      AddChar.inv_apply_eq_conj, mul_comm]
  simp only [IsROrC.ofReal_pow, pow_mul, ←Complex.conj_mul', map_sum, map_mul, Complex.conj_conj,
    Pi.conj_apply, mul_pow, Fintype.sum_pow, ←sq, Fintype.sum_mul_sum]
  conv_lhs =>
    arg 2
    ext
    rw [←Complex.eq_coe_norm_of_nonneg (this _ _)]
  letI : Fintype (Fin n → AddChar α ℂ) := @Pi.fintype _ _ _ _ λ i ↦ AddChar.instFintype _ _
  simp only [@sum_comm _ _ α, mul_sum, map_prod, map_mul, IsROrC.conj_conj, ←prod_mul_distrib]
  refine' sum_congr rfl λ x _ ↦ sum_congr rfl λ a _ ↦ prod_congr rfl λ i _ ↦ _
  ring

--TODO: Can we unify with `lpNorm_conv_le_lpNorm_dconv`?
lemma lpNorm_conv_le_lpNorm_dconv' (hn₀ : n ≠ 0) (hn : Even n) (f : α → ℝ) :
    ‖f ∗ f‖_[n] ≤ ‖f ○ f‖_[n] := by
  simpa only [←Complex.coe_comp_conv, ←Complex.coe_comp_dconv, Complex.lpNorm_coe_comp] using
    lpNorm_conv_le_lpNorm_dconv hn₀ hn ((↑) ∘ f)
