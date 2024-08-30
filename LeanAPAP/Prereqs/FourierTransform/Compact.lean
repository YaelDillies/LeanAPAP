import LeanAPAP.Prereqs.Convolution.Compact
import LeanAPAP.Prereqs.Expect.Complex
import LeanAPAP.Prereqs.FourierTransform.Discrete
import LeanAPAP.Prereqs.Function.Indicator.Basic

/-!
# Discrete Fourier transform in the compact normalisation

This file defines the discrete Fourier transform in the compact normalisation and shows the
Parseval-Plancherel identity and Fourier inversion formula for it.
-/

noncomputable section

open AddChar Finset Function MeasureTheory
open Fintype (card)
open scoped ComplexConjugate ComplexOrder

variable {α γ : Type*} [AddCommGroup α] [Fintype α] {f : α → ℂ} {ψ : AddChar α ℂ} {n : ℕ}

/-- The discrete Fourier transform. -/
def cft (f : α → ℂ) : AddChar α ℂ → ℂ := fun ψ ↦ ⟪ψ, f⟫ₙ_[ℂ]

lemma cft_apply (f : α → ℂ) (ψ : AddChar α ℂ) : cft f ψ = ⟪ψ, f⟫ₙ_[ℂ] := rfl

@[simp] lemma cft_zero : cft (0 : α → ℂ) = 0 := by ext; simp [cft_apply]

@[simp] lemma cft_add (f g : α → ℂ) : cft (f + g) = cft f + cft g := by
  ext; simp [cL2Inner_add_right, cft_apply]

@[simp] lemma cft_neg (f : α → ℂ) : cft (-f) = - cft f := by ext; simp [cft_apply]

@[simp] lemma cft_sub (f g : α → ℂ) : cft (f - g) = cft f - cft g := by
  ext; simp [cL2Inner_sub_right, cft_apply]

@[simp] lemma cft_const (a : ℂ) (hψ : ψ ≠ 0) : cft (const α a) ψ = 0 := by
  simp only [cft_apply, cL2Inner_eq_expect, const_apply, ← expect_mul, ← map_expect,
    expect_eq_zero_iff_ne_zero.2 hψ, map_zero, zero_mul]

@[simp] lemma cft_smul [DistribSMul γ ℂ] [Star γ] [StarModule γ ℂ] [IsScalarTower γ ℂ ℂ]
    [SMulCommClass γ ℂ ℂ] (c : γ) (f : α → ℂ) : cft (c • f) = c • cft f := by
  have := SMulCommClass.symm γ ℂ ℂ
  ext
  simp [cL2Inner_smul_right, cft_apply]

/-- **Parseval-Plancherel identity** for the discrete Fourier transform. -/
@[simp] lemma dL2Inner_cft (f g : α → ℂ) : ⟪cft f, cft g⟫_[ℂ] = ⟪f, g⟫ₙ_[ℂ] := by
  classical
  unfold cft
  simp_rw [dL2Inner_eq_sum, cL2Inner_eq_expect, map_expect, map_mul, starRingEnd_self_apply,
    expect_mul, mul_expect, ← expect_sum_comm, mul_mul_mul_comm _ (conj $ f _), ← sum_mul, ←
    AddChar.inv_apply_eq_conj, ← map_neg_eq_inv, ← map_add_eq_mul, AddChar.sum_apply_eq_ite]
  simp [add_neg_eq_zero, card_univ, Fintype.card_ne_zero, NNRat.smul_def (α := ℂ)]

/-- **Parseval-Plancherel identity** for the discrete Fourier transform. -/
@[simp] lemma dL2Norm_cft [MeasurableSpace α] [DiscreteMeasurableSpace α] (f : α → ℂ) :
    ‖cft f‖_[2] = ‖f‖ₙ_[2] :=
  (sq_eq_sq (zero_le _) (zero_le _)).1 $ NNReal.coe_injective $ Complex.ofReal_injective $ by
    push_cast; simpa only [cL2Inner_self, dL2Inner_self] using dL2Inner_cft f f

/-- **Fourier inversion** for the discrete Fourier transform. -/
lemma cft_inversion (f : α → ℂ) (a : α) : ∑ ψ, cft f ψ * ψ a = f a := by
  classical simp_rw [cft, cL2Inner_eq_expect, expect_mul, ← expect_sum_comm, mul_right_comm _ (f _),
    ← sum_mul, ← AddChar.inv_apply_eq_conj, inv_mul_eq_div, ← map_sub_eq_div,
    AddChar.sum_apply_eq_ite, sub_eq_zero, ite_mul, zero_mul, Fintype.expect_ite_eq]
  simp [add_neg_eq_zero, card_univ, NNRat.smul_def (α := ℂ), Fintype.card_ne_zero]

lemma dft_cft_doubleDualEmb (f : α → ℂ) (a : α) : dft (cft f) (doubleDualEmb a) = f (-a) := by
  simp only [← cft_inversion f (-a), mul_comm (conj _), dft_apply, dL2Inner_eq_sum, map_neg_eq_inv,
    AddChar.inv_apply_eq_conj, doubleDualEmb_apply]

lemma cft_dft_doubleDualEmb (f : α → ℂ) (a : α) : cft (dft f) (doubleDualEmb a) = f (-a) := by
  simp only [← dft_inversion f (-a), mul_comm (conj _), cft_apply, cL2Inner_eq_expect,
    map_neg_eq_inv, AddChar.inv_apply_eq_conj, doubleDualEmb_apply]

lemma dft_cft (f : α → ℂ) : dft (cft f) = f ∘ doubleDualEquiv.symm ∘ Neg.neg :=
  funext fun a ↦ by simp_rw [Function.comp_apply, map_neg, ← dft_cft_doubleDualEmb,
      doubleDualEmb_doubleDualEquiv_symm_apply]

lemma cft_dft (f : α → ℂ) : cft (dft f) = f ∘ doubleDualEquiv.symm ∘ Neg.neg :=
  funext fun a ↦ by simp_rw [Function.comp_apply, map_neg, ← cft_dft_doubleDualEmb,
      doubleDualEmb_doubleDualEquiv_symm_apply]

lemma cft_injective : Injective (cft : (α → ℂ) → AddChar α ℂ → ℂ) := fun f g h ↦
  funext fun a ↦ (cft_inversion _ _).symm.trans $ by rw [h, cft_inversion]

lemma cft_inv (ψ : AddChar α ℂ) (hf : IsSelfAdjoint f) : cft f ψ⁻¹ = conj (cft f ψ) := by
  simp_rw [cft_apply, cL2Inner_eq_expect, map_expect, AddChar.inv_apply', map_mul,
    AddChar.inv_apply_eq_conj, Complex.conj_conj, (hf.apply _).conj_eq]

@[simp]
lemma cft_conj (f : α → ℂ) (ψ : AddChar α ℂ) : cft (conj f) ψ = conj (cft f ψ⁻¹) := by
  simp only [cft_apply, cL2Inner_eq_expect, map_expect, map_mul, ← inv_apply', ← inv_apply_eq_conj,
    inv_inv, Pi.conj_apply]

lemma cft_conjneg_apply (f : α → ℂ) (ψ : AddChar α ℂ) : cft (conjneg f) ψ = conj (cft f ψ) := by
  simp only [cft_apply, cL2Inner_eq_expect, conjneg_apply, map_expect, map_mul, RCLike.conj_conj]
  refine Fintype.expect_equiv (Equiv.neg _) _ _ fun i ↦ ?_
  simp only [Equiv.neg_apply, ← inv_apply_eq_conj, ← inv_apply', inv_apply]

@[simp]
lemma cft_conjneg (f : α → ℂ) : cft (conjneg f) = conj (cft f) := funext $ cft_conjneg_apply _

@[simp] lemma cft_balance (f : α → ℂ) (hψ : ψ ≠ 0) : cft (balance f) ψ = cft f ψ := by
  simp only [balance, Pi.sub_apply, cft_sub, cft_const _ hψ, sub_zero]

lemma cft_dilate (f : α → ℂ) (ψ : AddChar α ℂ) (hn : (card α).Coprime n) :
    cft (dilate f n) ψ = cft f (ψ ^ n) := by
  simp_rw [cft_apply, cL2Inner_eq_expect, dilate]
  rw [← Nat.card_eq_fintype_card] at hn
  refine (Fintype.expect_bijective _ hn.nsmul_right_bijective _ _  ?_).symm
  simp only [pow_apply, ← map_nsmul_eq_pow, zmod_val_inv_nsmul_nsmul hn, forall_const]

@[simp] lemma cft_trivNChar [DecidableEq α] : cft (trivNChar : α → ℂ) = 1 := by
  ext
  simp [trivChar_apply, cft_apply, cL2Inner_eq_expect, ← map_expect, card_univ,
    NNRat.smul_def (α := ℂ)]

@[simp] lemma cft_one : cft (1 : α → ℂ) = trivChar :=
  dft_injective $ by classical rw [dft_trivChar, dft_cft, Pi.one_comp]

variable [DecidableEq α]

@[simp] lemma cft_indicate_zero (s : Finset α) : cft (𝟭 s) 0 = s.dens := by
  simp only [cft_apply, cL2Inner_eq_expect, expect_indicate, AddChar.zero_apply, map_one, one_mul,
    dens, NNRat.smul_def (α := ℂ), div_eq_inv_mul]
  simp

lemma cft_nconv_apply (f g : α → ℂ) (ψ : AddChar α ℂ) : cft (f ∗ₙ g) ψ = cft f ψ * cft g ψ := by
  simp_rw [cft, cL2Inner_eq_expect, nconv_eq_expect_sub', mul_expect, expect_mul, ← expect_product',
    univ_product_univ]
  refine Fintype.expect_equiv ((Equiv.prodComm _ _).trans $
    ((Equiv.refl _).prodShear Equiv.subRight).trans $ Equiv.prodComm _ _)  _ _ fun (a, b) ↦ ?_
  simp only [Equiv.trans_apply, Equiv.prodComm_apply, Equiv.prodShear_apply, Prod.fst_swap,
    Equiv.refl_apply, Prod.snd_swap, Equiv.subRight_apply, Prod.swap_prod_mk, Prod.forall]
  rw [mul_mul_mul_comm, ← map_mul, ← map_add_eq_mul, add_sub_cancel]

lemma cft_cdconv_apply (f g : α → ℂ) (ψ : AddChar α ℂ) :
    cft (f ○ₙ g) ψ = cft f ψ * conj (cft g ψ) := by
  rw [← nconv_conjneg, cft_nconv_apply, cft_conjneg_apply]

@[simp] lemma cft_nconv (f g : α → ℂ) : cft (f ∗ₙ g) = cft f * cft g :=
  funext $ cft_nconv_apply _ _

@[simp]
lemma cft_cdconv (f g : α → ℂ) : cft (f ○ₙ g) = cft f * conj (cft g) :=
  funext $ cft_cdconv_apply _ _

@[simp] lemma cft_iterNConv (f : α → ℂ) : ∀ n, cft (f ∗^ₙ n) = cft f ^ n
  | 0 => cft_trivNChar
  | n + 1 => by simp [iterNConv_succ, pow_succ, cft_iterNConv]

@[simp] lemma cft_iterNConv_apply (f : α → ℂ) (n : ℕ) (ψ : AddChar α ℂ) :
    cft (f ∗^ₙ n) ψ = cft f ψ ^ n := congr_fun (cft_iterNConv _ _) _

-- lemma dL2Norm_iterNConv (f : α → ℂ) (n : ℕ) : ‖f ∗^ₙ n‖ₙ_[2] = ‖f ^ n‖_[2] := by
--   rw [← dL2Norm_cft, cft_iterNConv, ← ENNReal.coe_two, dLpNorm_pow]
--   norm_cast
--   refine (sq_eq_sq (by positivity) $ by positivity).1 ?_
--   rw [← ENNReal.coe_two, dLpNorm_pow, ← pow_mul', ← Complex.ofReal_inj]
--   push_cast
--   simp_rw [pow_mul, ← Complex.mul_conj', conj_iterConv_apply, mul_pow]

variable [MeasurableSpace α] [DiscreteMeasurableSpace α]

lemma cLpNorm_nconv_le_cLpNorm_cdconv (hn₀ : n ≠ 0) (hn : Even n) (f : α → ℂ) :
    ‖f ∗ₙ f‖ₙ_[n] ≤ ‖f ○ₙ f‖ₙ_[n] := by
  cases isEmpty_or_nonempty α
  · rw [Subsingleton.elim (f ∗ₙ f) (f ○ₙ f)]
  refine le_of_pow_le_pow_left hn₀ (by positivity) ?_
  obtain ⟨n, rfl⟩ := hn.two_dvd
  simp_rw [← NNReal.coe_le_coe, NNReal.coe_pow, cLpNorm_pow_eq_expect_norm hn₀,
    ← cft_inversion (f ∗ₙ f), ← cft_inversion (f ○ₙ f), cft_nconv, cft_cdconv, Pi.mul_apply]
  rw [← Real.norm_of_nonneg (expect_nonneg fun i _ ↦ ?_), ← Complex.norm_real]
  rw [Complex.ofReal_expect (univ : Finset α)]
  any_goals positivity
  simp_rw [pow_mul', ← norm_pow _ n, Complex.ofReal_pow, ← Complex.conj_mul', map_pow, map_sum,
    map_mul, Fintype.sum_pow, Fintype.sum_mul_sum]
  sorry
  -- simp only [@expect_comm _ _ α, ← mul_expect, prod_mul_prod_comm]
  -- refine (norm_expect_le _ _).trans_eq (Complex.ofReal_injective _)
  -- simp only [norm_mul, norm_prod, RCLike.norm_conj, ← pow_mul]
  -- push_cast
  -- have : ∀ f g : Fin n → AddChar α ℂ, 0 ≤ ∑ a, ∏ i, conj (f i a) * g i a := by
  --   rintro f g
  --   suffices : ∑ a, ∏ i, conj (f i a) * g i a = if ∑ i, (g i - f i) = 0 then (card α : ℂ) else 0
  --   · rw [this]
  --     split_ifs <;> positivity
  --   simp_rw [← AddChar.expect_eq_ite, AddChar.expect_apply, AddChar.sub_apply, AddChar.map_neg_eq_inv,
  --     AddChar.inv_apply_eq_conj, mul_comm]
  -- simp only [RCLike.ofReal_pow, pow_mul, ← Complex.conj_mul', map_expect, map_mul, Complex.conj_conj,
  --   Pi.conj_apply, mul_pow, Fintype.expect_pow, ← sq, Fintype.expect_mul_expect]
  -- conv_lhs =>
  --   arg 2
  --   ext
  --   rw [← Complex.eq_coe_norm_of_nonneg (this _ _)]
  -- simp only [@expect_comm _ _ α, mul_expect, map_prod, map_mul, RCLike.conj_conj, ← prod_mul_distrib]
  -- refine expect_congr rfl fun x _ ↦ expect_congr rfl fun a _ ↦ prod_congr rfl fun i _ ↦ _
  -- ring

--TODO: Can we unify with `cLpNorm_nconv_le_cLpNorm_cdconv`?
lemma cLpNorm_nconv_le_cLpNorm_cdconv' (hn₀ : n ≠ 0) (hn : Even n) (f : α → ℝ) :
    ‖f ∗ₙ f‖ₙ_[n] ≤ ‖f ○ₙ f‖ₙ_[n] := by
  simpa only [← Complex.coe_comp_nconv, ← Complex.coe_comp_cdconv, Complex.cLpNorm_coe_comp] using
    cLpNorm_nconv_le_cLpNorm_cdconv hn₀ hn ((↑) ∘ f)
