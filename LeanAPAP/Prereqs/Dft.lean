import Project.Mathlib.Algebra.BigOperators.Ring
import Project.Mathlib.Logic.Basic
import Project.Mathlib.NumberTheory.LegendreSymbol.AddChar.Duality
import Project.Prereqs.Convolution.Basic

#align_import prereqs.dft

/-!
# Discrete Fourier transform

This file defines the discrete Fourier transform and shows the Parseval-Plancherel identity and
Fourier inversion formula for it.
-/


open AddChar Finset

open Fintype (card)

open Function

open scoped BigOperators ComplexConjugate ComplexOrder

variable {α γ : Type _} [AddCommGroup α] [Fintype α] {f : α → ℂ} {ψ : AddChar α ℂ} {n : ℕ}

/-- The discrete Fourier transform. -/
def dft (f : α → ℂ) : AddChar α ℂ → ℂ := fun ψ => ⟪ψ, f⟫_[ℂ]

theorem dft_apply (f : α → ℂ) (ψ : AddChar α ℂ) : dft f ψ = ⟪ψ, f⟫_[ℂ] :=
  rfl

@[simp]
theorem dft_zero : dft (0 : α → ℂ) = 0 := by ext <;> simp [dft_apply]

@[simp]
theorem dft_add (f g : α → ℂ) : dft (f + g) = dft f + dft g := by
  ext : 1 <;> simp [l2inner_add_right, dft_apply]

@[simp]
theorem dft_sub (f g : α → ℂ) : dft (f - g) = dft f - dft g := by
  ext : 1 <;> simp [l2inner_sub_right, dft_apply]

@[simp]
theorem dft_const (a : ℂ) (hψ : ψ ≠ 0) : dft (const α a) ψ = 0 := by
  simp only [dft_apply, l2inner_eq_sum, const_apply, ← sum_mul, ← map_sum,
    sum_eq_zero_iff_ne_zero.2 hψ, map_zero, MulZeroClass.zero_mul]

@[simp]
theorem dft_smul [DistribSMul γ ℂ] [Star γ] [StarModule γ ℂ] [SMulCommClass γ ℂ ℂ] (c : γ)
    (f : α → ℂ) : dft (c • f) = c • dft f := by ext : 1 <;> simp [l2inner_smul_right, dft_apply]

/-- **Parseval-Plancherel identity** for the discrete Fourier transform. -/
@[simp]
theorem l2inner_dft (f g : α → ℂ) : ⟪dft f, dft g⟫_[ℂ] = card α * ⟪f, g⟫_[ℂ] := by
  classical simp_rw [dft, l2inner_eq_sum, map_sum, map_mul, starRingEnd_self_apply, sum_mul,
    mul_sum, @sum_comm _ _ (AddChar _ _), mul_mul_mul_comm _ (conj <| f _), ← sum_mul, ←
    AddChar.inv_apply_eq_conj, ← map_neg_eq_inv, ← map_add_mul, AddChar.sum_apply_eq_ite,
    add_neg_eq_zero, ite_mul, MulZeroClass.zero_mul, Fintype.sum_ite_eq]

/-- **Parseval-Plancherel identity** for the discrete Fourier transform. -/
theorem L2norm_dft_sq (f : α → ℂ) : ‖dft f‖_[2] ^ 2 = card α * ‖f‖_[2] ^ 2 :=
  Complex.ofReal_injective <| by push_cast <;> simpa only [l2inner_self] using l2inner_dft f f

/-- **Parseval-Plancherel identity** for the discrete Fourier transform. -/
@[simp]
theorem L2norm_dft (f : α → ℂ) : ‖dft f‖_[2] = Real.sqrt (card α) * ‖f‖_[2] := by
  simpa using congr_arg Real.sqrt (L2norm_dft_sq f)

/-- **Fourier inversion** for the discrete Fourier transform. -/
theorem dft_inversion (f : α → ℂ) (a : α) : ∑ ψ : AddChar α ℂ, dft f ψ * ψ a = card α * f a := by
  classical simp_rw [dft, l2inner_eq_sum, sum_mul, @sum_comm _ α, mul_right_comm _ (f _), ← sum_mul,
    ← AddChar.inv_apply_eq_conj, inv_mul_eq_div, ← map_sub_eq_div, AddChar.sum_apply_eq_ite,
    sub_eq_zero, ite_mul, MulZeroClass.zero_mul, Fintype.sum_ite_eq]

theorem dft_dft_doubleDualEmb (f : α → ℂ) (a : α) :
    dft (dft f) (doubleDualEmb a) = card α * f (-a) := by
  simp only [← dft_inversion, mul_comm (conj _), dft_apply, l2inner_eq_sum, map_neg_eq_inv,
    AddChar.inv_apply_eq_conj, double_dual_emb_apply]

theorem dft_dft (f : α → ℂ) : dft (dft f) = card α * f ∘ doubleDualEquiv.symm ∘ Neg.neg :=
  funext fun a => by
    simp_rw [Pi.mul_apply, Function.comp_apply, map_neg, Pi.nat_apply, ← dft_dft_doubleDualEmb,
      double_dual_emb_double_dual_equiv_symm_apply]

theorem dft_injective : Injective (dft : (α → ℂ) → AddChar α ℂ → ℂ) := fun f g h =>
  funext fun a =>
    mul_right_injective₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero) <|
      (dft_inversion _ _).symm.trans <| by rw [h, dft_inversion]

theorem dft_inv (ψ : AddChar α ℂ) (hf : IsSelfAdjoint f) : dft f ψ⁻¹ = conj (dft f ψ) := by
  simp_rw [dft_apply, l2inner_eq_sum, map_sum, AddChar.inv_apply', map_mul,
    AddChar.inv_apply_eq_conj, Complex.conj_conj, (hf.apply _).conj_eq]

@[simp]
theorem dft_conj (f : α → ℂ) (ψ : AddChar α ℂ) : dft (conj f) ψ = conj (dft f ψ⁻¹) := by
  simp only [dft_apply, l2inner_eq_sum, map_sum, map_mul, ← inv_apply', ← inv_apply_eq_conj,
    inv_inv, Pi.conj_apply]

theorem dft_conjneg_apply (f : α → ℂ) (ψ : AddChar α ℂ) : dft (conjneg f) ψ = conj (dft f ψ) :=
  by
  simp only [dft_apply, l2inner_eq_sum, conjneg_apply, map_sum, map_mul, IsROrC.conj_conj]
  refine' Equiv.sum_comp' (Equiv.neg _) _ _ fun i => _
  simp only [Equiv.neg_apply, ← inv_apply_eq_conj, ← inv_apply', inv_apply]

@[simp]
theorem dft_conjneg (f : α → ℂ) : dft (conjneg f) = conj (dft f) :=
  funext <| dft_conjneg_apply _

@[simp]
theorem dft_balance (f : α → ℂ) (hψ : ψ ≠ 0) : dft (balance f) ψ = dft f ψ := by
  simp only [balance, Pi.sub_apply, dft_sub, dft_const _ hψ, sub_zero]

theorem dft_dilate (f : α → ℂ) (ψ : AddChar α ℂ) (hn : n.coprime (card α)) :
    dft (dilate f n) ψ = dft f (ψ ^ n) :=
  by
  simp_rw [dft_apply, l2inner_eq_sum, dilate]
  refine' sum_nbij' ((· • ·) (n⁻¹ : ZMod (card α)).val) _ (fun x hx => _) ((· • ·) n) _ _ _
  · simp only [mem_univ, forall_const]
  · rw [pow_apply, ← map_nsmul_pow, nsmul_zMod_val_inv_nsmul hn]
  all_goals
    simp only [hn, mem_univ, nsmul_zMod_val_inv_nsmul, zMod_val_inv_nsmul_nsmul, eq_self_iff_true,
      forall_const]

@[simp]
theorem dft_trivChar [DecidableEq α] : dft (trivChar : α → ℂ) = 1 := by
  ext ψ : 1 <;> simp [trivChar_apply, dft_apply, l2inner_eq_sum, ← map_sum]

@[simp]
theorem dft_one : dft (1 : α → ℂ) = card α • trivChar :=
  dft_injective <| by classical rw [dft_smul, dft_trivChar, dft_dft, Pi.one_comp, nsmul_eq_mul]

variable [DecidableEq α]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem dft_indicate_zero (A : Finset α) : dft (𝟭 A) 0 = A.card := by
  simp only [dft_apply, l2inner_eq_sum, sum_indicate, AddChar.zero_apply, map_one, one_mul]

theorem dft_conv_apply (f g : α → ℂ) (ψ : AddChar α ℂ) : dft (f ∗ g) ψ = dft f ψ * dft g ψ :=
  by
  simp_rw [dft, l2inner_eq_sum, conv_eq_sum_sub', mul_sum, sum_mul, ← sum_product',
    univ_product_univ]
  refine'
    sum_nbij' (fun x => (x.1 - x.2, x.2)) (by simp) (fun x _ => _) (fun x => (x.1 + x.2, x.2))
      (by simp) (by simp) (by simp)
  rw [mul_mul_mul_comm, ← map_mul, ← map_add_mul, add_sub_cancel'_right]

theorem dft_dconv_apply (f g : α → ℂ) (ψ : AddChar α ℂ) :
    dft (f ○ g) ψ = dft f ψ * conj (dft g ψ) := by
  rw [← conv_conjneg, dft_conv_apply, dft_conjneg_apply]

@[simp]
theorem dft_conv (f g : α → ℂ) : dft (f ∗ g) = dft f * dft g :=
  funext <| dft_conv_apply _ _

@[simp]
theorem dft_dconv (f g : α → ℂ) : dft (f ○ g) = dft f * conj (dft g) :=
  funext <| dft_dconv_apply _ _

@[simp]
theorem dft_iterConv (f : α → ℂ) : ∀ n, dft (f ∗^ n) = dft f ^ n
  | 0 => dft_trivChar
  | n + 1 => by simp [iterConv_succ, pow_succ, dft_iterConv]

theorem lpnorm_conv_le_lpnorm_dconv (hn₀ : n ≠ 0) (hn : Even n) (f : α → ℂ) :
    ‖f ∗ f‖_[n] ≤ ‖f ○ f‖_[n] :=
  by
  refine' le_of_pow_le_pow _ _ hn₀.bot_lt (le_of_mul_le_mul_left _ (_ : (0 : ℝ) < card α ^ n))
  any_goals positivity
  obtain ⟨n, rfl⟩ := hn.two_dvd
  simp_rw [lpnorm_pow_eq_sum hn₀, mul_sum, ← mul_pow, ← nsmul_eq_mul, ← norm_nsmul, nsmul_eq_mul, ←
    dft_inversion, dft_conv, dft_dconv, Pi.mul_apply]
  rw [← Real.norm_of_nonneg (sum_nonneg fun i _ => _), ← Complex.norm_real, IsROrC.ofReal_sum]
  any_goals positivity
  simp_rw [pow_mul', ← norm_pow _ n, Complex.ofReal_pow, ← IsROrC.conj_mul', map_pow, map_sum,
    map_mul, Fintype.sum_pow, Fintype.sum_hMul_sum]
  simp only [@sum_comm _ _ α, ← mul_sum, prod_mul_prod_comm]
  refine' (norm_sum_le _ _).trans_eq (Complex.ofReal_injective _)
  simp only [norm_mul, norm_prod, IsROrC.norm_conj, ← pow_mul]
  push_cast
  have : ∀ f g : Fin n → AddChar α ℂ, 0 ≤ ∑ a, ∏ i, conj (f i a) * g i a :=
    by
    rintro f g
    suffices ∑ a, ∏ i, conj (f i a) * g i a = if ∑ i, (g i - f i) = 0 then card α else 0
      by
      rw [this]
      split_ifs <;> positivity
    simp_rw [← AddChar.sum_eq_ite, AddChar.sum_apply, AddChar.sub_apply, AddChar.map_neg_eq_inv,
      AddChar.inv_apply_eq_conj, mul_comm]
  simp only [IsROrC.ofReal_pow, pow_mul, ← IsROrC.conj_mul', map_sum, map_mul, IsROrC.conj_conj,
    Pi.conj_apply, mul_pow, Fintype.sum_pow, ← sq, Fintype.sum_hMul_sum]
  conv_lhs =>
    congr
    skip
    ext
    rw [← Complex.eq_coe_norm_of_nonneg (this _ _)]
  letI : Fintype (Fin n → AddChar α ℂ) := @Pi.fintype _ _ _ _ fun i => AddChar.fintype _ _
  simp only [@sum_comm _ _ α, mul_sum, map_prod, map_mul, IsROrC.conj_conj, ← prod_mul_distrib]
  refine' sum_congr rfl fun x _ => sum_congr rfl fun a _ => prod_congr rfl fun i _ => _
  ring

@[simp]
theorem IsROrC.lpnorm_coe_comp {𝕜 : Type _} [IsROrC 𝕜] (p) (f : α → ℝ) :
    ‖(coe : ℝ → 𝕜) ∘ f‖_[p] = ‖f‖_[p] := by
  simp only [← lpnorm_norm _ ((coe : ℝ → 𝕜) ∘ f), ← lpnorm_norm _ f, Function.comp_apply,
    IsROrC.norm_ofReal, Real.norm_eq_abs]

--TODO: Can we unify with `Lpnorm_conv_le_Lpnorm_dconv`?
theorem lpnorm_conv_le_lpnorm_dconv' (hn₀ : n ≠ 0) (hn : Even n) (f : α → ℝ) :
    ‖f ∗ f‖_[n] ≤ ‖f ○ f‖_[n] := by
  simpa only [← IsROrC.coe_comp_conv, ← IsROrC.coe_comp_dconv, IsROrC.lpnorm_coe_comp] using
    lpnorm_conv_le_lpnorm_dconv hn₀ hn (coe ∘ f)

