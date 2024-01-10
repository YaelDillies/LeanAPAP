import LeanAPAP.Mathlib.Algebra.BigOperators.Ring
import LeanAPAP.Prereqs.AddChar.PontryaginDuality
import LeanAPAP.Prereqs.Discrete.Convolution.Basic
import LeanAPAP.Prereqs.Discrete.LpNorm.Compact

/-!
# Discrete Fourier transform

This file defines the discrete Fourier transform and shows the Parseval-Plancherel identity and
Fourier inversion formula for it.
-/

open AddChar Finset Function
open Fintype (card)
open scoped BigOps ComplexConjugate ComplexOrder

variable {α γ : Type*} [AddCommGroup α] [Fintype α] {f : α → ℂ} {ψ : AddChar α ℂ} {n : ℕ}

/-- The discrete Fourier transform. -/
def dft (f : α → ℂ) : AddChar α ℂ → ℂ := fun ψ ↦ ⟪ψ, f⟫_[ℂ]

lemma dft_apply (f : α → ℂ) (ψ : AddChar α ℂ) : dft f ψ = ⟪ψ, f⟫_[ℂ] := rfl

@[simp] lemma dft_zero : dft (0 : α → ℂ) = 0 := by ext; simp [dft_apply]

@[simp] lemma dft_add (f g : α → ℂ) : dft (f + g) = dft f + dft g := by
  ext; simp [l2Inner_add_right, dft_apply]

@[simp] lemma dft_neg (f : α → ℂ) : dft (-f) = - dft f := by ext; simp [dft_apply]

@[simp] lemma dft_sub (f g : α → ℂ) : dft (f - g) = dft f - dft g := by
  ext; simp [l2Inner_sub_right, dft_apply]

@[simp] lemma dft_const (a : ℂ) (hψ : ψ ≠ 0) : dft (const α a) ψ = 0 := by
  simp only [dft_apply, l2Inner_eq_sum, const_apply, ←sum_mul, ←map_sum,
    sum_eq_zero_iff_ne_zero.2 hψ, map_zero, zero_mul]

@[simp] lemma dft_smul [DistribSMul γ ℂ] [Star γ] [StarModule γ ℂ] [SMulCommClass γ ℂ ℂ] (c : γ)
    (f : α → ℂ) : dft (c • f) = c • dft f := by ext; simp [l2Inner_smul_right, dft_apply]

/-- **Parseval-Plancherel identity** for the discrete Fourier transform. -/
@[simp] lemma nl2Inner_dft (f g : α → ℂ) : ⟪dft f, dft g⟫ₙ_[ℂ] = ⟪f, g⟫_[ℂ] := by
  classical
  unfold dft
  simp_rw [l2Inner_eq_sum, nl2Inner_eq_expect, map_sum, map_mul, starRingEnd_self_apply, sum_mul,
    mul_sum, expect_sum_comm, mul_mul_mul_comm _ (conj $ f _), ←expect_mul, ←
    AddChar.inv_apply_eq_conj, ←map_neg_eq_inv, ←map_add_mul, AddChar.expect_apply_eq_ite,
    add_neg_eq_zero, boole_mul, Fintype.sum_ite_eq]

/-- **Parseval-Plancherel identity** for the discrete Fourier transform. -/
@[simp] lemma nl2Norm_dft (f : α → ℂ) : ‖dft f‖ₙ_[2] = ‖f‖_[2] :=
  (sq_eq_sq nlpNorm_nonneg lpNorm_nonneg).1 $ Complex.ofReal_injective $ by
    push_cast; simpa only [nl2Inner_self, l2Inner_self] using nl2Inner_dft f f

/-- **Fourier inversion** for the discrete Fourier transform. -/
lemma dft_inversion (f : α → ℂ) (a : α) : 𝔼 ψ, dft f ψ * ψ a = f a := by
  classical simp_rw [dft, l2Inner_eq_sum, sum_mul, expect_sum_comm, mul_right_comm _ (f _),
    ← expect_mul, ←AddChar.inv_apply_eq_conj, inv_mul_eq_div, ←map_sub_eq_div, AddChar.expect_apply_eq_ite, sub_eq_zero, boole_mul, Fintype.sum_ite_eq]

/-- **Fourier inversion** for the discrete Fourier transform. -/
lemma dft_inversion' (f : α → ℂ) (a : α) : ∑ ψ : AddChar α ℂ, dft f ψ * ψ a = card α * f a := by
  rw [mul_comm, ← div_eq_iff, ← dft_inversion f, ← AddChar.card_eq,
    Fintype.expect_eq_sum_div_card (α := ℂ)]
  simp

lemma dft_dft_doubleDualEmb (f : α → ℂ) (a : α) :
    dft (dft f) (doubleDualEmb a) = card α * f (-a) := by
  simp only [←dft_inversion f (-a), mul_comm (conj _), dft_apply, l2Inner_eq_sum, map_neg_eq_inv,
    AddChar.inv_apply_eq_conj, doubleDualEmb_apply, ← Fintype.card_mul_expect, AddChar.card_eq]

lemma dft_dft (f : α → ℂ) : dft (dft f) = card α * f ∘ doubleDualEquiv.symm ∘ Neg.neg :=
  funext fun a ↦ by
    simp_rw [Pi.mul_apply, Function.comp_apply, map_neg, Pi.nat_apply, ←dft_dft_doubleDualEmb,
      doubleDualEmb_doubleDualEquiv_symm_apply]

lemma dft_injective : Injective (dft : (α → ℂ) → AddChar α ℂ → ℂ) := fun f g h ↦
  funext fun a ↦ (dft_inversion _ _).symm.trans $ by rw [h, dft_inversion]

lemma dft_inv (ψ : AddChar α ℂ) (hf : IsSelfAdjoint f) : dft f ψ⁻¹ = conj (dft f ψ) := by
  simp_rw [dft_apply, l2Inner_eq_sum, map_sum, AddChar.inv_apply', map_mul,
    AddChar.inv_apply_eq_conj, Complex.conj_conj, (hf.apply _).conj_eq]

@[simp]
lemma dft_conj (f : α → ℂ) (ψ : AddChar α ℂ) : dft (conj f) ψ = conj (dft f ψ⁻¹) := by
  simp only [dft_apply, l2Inner_eq_sum, map_sum, map_mul, ←inv_apply', ←inv_apply_eq_conj,
    inv_inv, Pi.conj_apply]

lemma dft_conjneg_apply (f : α → ℂ) (ψ : AddChar α ℂ) : dft (conjneg f) ψ = conj (dft f ψ) := by
  simp only [dft_apply, l2Inner_eq_sum, conjneg_apply, map_sum, map_mul, IsROrC.conj_conj]
  refine' Fintype.sum_equiv (Equiv.neg α) _ _ fun i ↦ _
  simp only [Equiv.neg_apply, ←inv_apply_eq_conj, ←inv_apply', inv_apply]

@[simp]
lemma dft_conjneg (f : α → ℂ) : dft (conjneg f) = conj (dft f) := funext $ dft_conjneg_apply _

@[simp] lemma dft_balance (f : α → ℂ) (hψ : ψ ≠ 0) : dft (balance f) ψ = dft f ψ := by
  simp only [balance, Pi.sub_apply, dft_sub, dft_const _ hψ, sub_zero]

lemma dft_dilate (f : α → ℂ) (ψ : AddChar α ℂ) (hn : (card α).Coprime n) :
    dft (dilate f n) ψ = dft f (ψ ^ n) := by
  simp_rw [dft_apply, l2Inner_eq_sum, dilate]
  rw [← Nat.card_eq_fintype_card] at hn
  refine (Fintype.sum_bijective _ hn.nsmul_right_bijective _ _  ?_).symm
  simp only [pow_apply, ← map_nsmul_pow, zmod_val_inv_nsmul_nsmul hn, forall_const]

@[simp] lemma dft_trivChar [DecidableEq α] : dft (trivChar : α → ℂ) = 1 := by
  ext; simp [trivChar_apply, dft_apply, l2Inner_eq_sum, ←map_sum]

@[simp] lemma dft_one : dft (1 : α → ℂ) = card α • trivChar :=
  dft_injective $ by classical rw [dft_smul, dft_trivChar, dft_dft, Pi.one_comp, nsmul_eq_mul]

variable [DecidableEq α]

@[simp] lemma dft_indicate_zero (A : Finset α) : dft (𝟭 A) 0 = A.card := by
  simp only [dft_apply, l2Inner_eq_sum, sum_indicate, AddChar.zero_apply, map_one, one_mul]

lemma dft_conv_apply (f g : α → ℂ) (ψ : AddChar α ℂ) : dft (f ∗ g) ψ = dft f ψ * dft g ψ := by
  simp_rw [dft, l2Inner_eq_sum, conv_eq_sum_sub', mul_sum, sum_mul, ←sum_product',
    univ_product_univ]
  refine Fintype.sum_equiv ((Equiv.prodComm _ _).trans $
    ((Equiv.refl _).prodShear Equiv.subRight).trans $ Equiv.prodComm _ _)  _ _ fun (a, b) ↦ ?_
  simp only [Equiv.trans_apply, Equiv.prodComm_apply, Equiv.prodShear_apply, Prod.fst_swap,
    Equiv.refl_apply, Prod.snd_swap, Equiv.subRight_apply, Prod.swap_prod_mk, Prod.forall]
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

@[simp] lemma dft_iterConv_apply (f : α → ℂ) (n : ℕ) (ψ : AddChar α ℂ) :
    dft (f ∗^ n) ψ = dft f ψ ^ n := congr_fun (dft_iterConv _ _) _

lemma lpNorm_conv_le_lpNorm_dconv (hn₀ : n ≠ 0) (hn : Even n) (f : α → ℂ) :
    ‖f ∗ f‖_[n] ≤ ‖f ○ f‖_[n] := by
  cases isEmpty_or_nonempty α
  · rw [Subsingleton.elim (f ∗ f) (f ○ f)]
  refine' le_of_pow_le_pow_left hn₀ (by positivity) $
    le_of_mul_le_mul_left _ (by positivity : (0 : ℝ) < card α ^ n)
  obtain ⟨n, rfl⟩ := hn.two_dvd
  simp_rw [lpNorm_pow_eq_sum hn₀, mul_sum, ←mul_pow, ←nsmul_eq_mul, ←norm_nsmul, nsmul_eq_mul,
    ← dft_inversion', dft_conv, dft_dconv, Pi.mul_apply]
  rw [←Real.norm_of_nonneg (sum_nonneg fun i _ ↦ ?_), ←Complex.norm_real]
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
  simp only [@sum_comm _ _ α, mul_sum, map_prod, map_mul, IsROrC.conj_conj, ←prod_mul_distrib]
  refine' sum_congr rfl fun x _ ↦ sum_congr rfl fun a _ ↦ prod_congr rfl fun i _ ↦ _
  ring

--TODO: Can we unify with `lpNorm_conv_le_lpNorm_dconv`?
lemma lpNorm_conv_le_lpNorm_dconv' (hn₀ : n ≠ 0) (hn : Even n) (f : α → ℝ) :
    ‖f ∗ f‖_[n] ≤ ‖f ○ f‖_[n] := by
  simpa only [←Complex.coe_comp_conv, ←Complex.coe_comp_dconv, Complex.lpNorm_coe_comp] using
    lpNorm_conv_le_lpNorm_dconv hn₀ hn ((↑) ∘ f)
