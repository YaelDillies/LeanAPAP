import LeanAPAP.Prereqs.Expect.Basic
import LeanAPAP.Prereqs.Function.Indicator.Defs
import LeanAPAP.Prereqs.Function.Translate
import LeanAPAP.Prereqs.LpNorm.Discrete.Defs

/-!
# Lp norms
-/

open Finset Function Real
open scoped BigOperators ComplexConjugate ENNReal NNReal

variable {ι 𝕜 : Type*} [Fintype ι]

/-! ### Lp norm -/

section NormedAddCommGroup
variable {α : ι → Type*} [∀ i, NormedAddCommGroup (α i)] {p q : ℝ≥0∞} {f g h : ∀ i, α i}

section one_le
variable [NormedField 𝕜] [∀ i, NormedSpace ℝ (α i)]

lemma lpNorm_expect_le [∀ i, Module ℚ≥0 (α i)] (hp : 1 ≤ p) {κ : Type*} (s : Finset κ)
    (f : κ → ∀ i, α i) : ‖𝔼 i ∈ s, f i‖_[p] ≤ 𝔼 i ∈ s, ‖f i‖_[p] := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  refine (le_inv_smul_iff_of_pos $ by positivity).2 ?_
  rw [Nat.cast_smul_eq_nsmul, ← lpNorm_nsmul hp, card_smul_expect]
  exact lpNorm_sum_le hp _ _

end one_le
end NormedAddCommGroup

/-! #### Inner product -/

section lpNorm
variable {α β : Type*} [AddCommGroup α] [Fintype α] {p : ℝ≥0∞}

@[simp]
lemma lpNorm_translate [NormedAddCommGroup β] (a : α) (f : α → β) : ‖τ a f‖_[p] = ‖f‖_[p] := by
  obtain p | p := p
  · simp only [linftyNorm_eq_ciSup, ENNReal.none_eq_top, translate_apply]
    exact (Equiv.subRight _).iSup_congr fun _ ↦ rfl
  obtain rfl | hp := eq_or_ne p 0
  · simp only [l0Norm_eq_card, translate_apply, Ne, ENNReal.some_eq_coe, ENNReal.coe_zero,
      Nat.cast_inj]
    exact card_equiv (Equiv.subRight a) (by simp)
  · simp only [lpNorm_eq_sum hp, ENNReal.some_eq_coe, translate_apply]
    congr 1
    exact Fintype.sum_equiv (Equiv.subRight _) _ _ fun _ ↦ rfl

@[simp] lemma lpNorm_conjneg [RCLike β] (f : α → β) : ‖conjneg f‖_[p] = ‖f‖_[p] := by
  simp only [conjneg, lpNorm_conj]
  obtain p | p := p
  · simp only [linftyNorm_eq_ciSup, ENNReal.none_eq_top, conjneg, RCLike.norm_conj]
    exact (Equiv.neg _).iSup_congr fun _ ↦ rfl
  obtain rfl | hp := eq_or_ne p 0
  · simp only [l0Norm_eq_card, Ne, ENNReal.some_eq_coe, ENNReal.coe_zero, Nat.cast_inj]
    exact card_equiv (Equiv.neg _) (by simp)
  · simp only [lpNorm_eq_sum hp, ENNReal.some_eq_coe]
    congr 1
    exact Fintype.sum_equiv (Equiv.neg _) _ _ fun _ ↦ rfl

lemma lpNorm_translate_sum_sub_le [NormedAddCommGroup β] (hp : 1 ≤ p) {ι : Type*} (s : Finset ι)
    (a : ι → α) (f : α → β) : ‖τ (∑ i ∈ s, a i) f - f‖_[p] ≤ ∑ i ∈ s, ‖τ (a i) f - f‖_[p] := by
  induction' s using Finset.cons_induction with i s ih hs
  · simp
  calc
    _ = ‖τ (∑ j ∈ s, a j) (τ (a i) f - f) + (τ (∑ j ∈ s, a j) f - f)‖_[p] := by
        rw [sum_cons, translate_add', translate_sub_right, sub_add_sub_cancel]
    _ ≤ ‖τ (∑ j ∈ s, a j) (τ (a i) f - f)‖_[p] + ‖(τ (∑ j ∈ s, a j) f - f)‖_[p] :=
        lpNorm_add_le hp _ _
    _ ≤ ‖τ (∑ j ∈ s, a j) (τ (a i) f - f)‖_[p] + ∑ j ∈ s, ‖(τ (a j) f - f)‖_[p] :=
        add_le_add_left hs _
    _ = _ := by rw [lpNorm_translate, sum_cons]

end lpNorm

/-! ### Indicator -/

section indicate
variable {α β : Type*} [RCLike β] [Fintype α] [DecidableEq α] {s : Finset α} {p : ℝ≥0}

lemma lpNorm_rpow_indicate (hp : p ≠ 0) (s : Finset α) : ‖𝟭_[β] s‖_[p] ^ (p : ℝ) = s.card := by
  have : ∀ x, (ite (x ∈ s) 1 0 : ℝ) ^ (p : ℝ) =
    ite (x ∈ s) (1 ^ (p : ℝ)) (0 ^ (p : ℝ)) := fun x ↦ by split_ifs <;> simp
  simp [lpNorm_rpow_eq_sum, hp, indicate_apply, apply_ite Norm.norm, -sum_const, card_eq_sum_ones,
    sum_boole, this, zero_rpow, filter_mem_eq_inter]

lemma lpNorm_indicate (hp : p ≠ 0) (s : Finset α) : ‖𝟭_[β] s‖_[p] = s.card ^ (p⁻¹ : ℝ) := by
  refine (eq_rpow_inv ?_ ?_ ?_).2 (lpNorm_rpow_indicate ?_ _) <;> positivity

lemma lpNorm_pow_indicate {p : ℕ} (hp : p ≠ 0) (s : Finset α) :
    ‖𝟭_[β] s‖_[p] ^ (p : ℝ) = s.card := by
  simpa using lpNorm_rpow_indicate (Nat.cast_ne_zero.2 hp) s

lemma l2Norm_sq_indicate (s : Finset α) : ‖𝟭_[β] s‖_[2] ^ 2 = s.card := by
  simpa using lpNorm_pow_indicate two_ne_zero s

lemma l2Norm_indicate (s : Finset α) : ‖𝟭_[β] s‖_[2] = Real.sqrt s.card := by
  rw [eq_comm, sqrt_eq_iff_eq_sq, l2Norm_sq_indicate] <;> positivity

@[simp] lemma l1Norm_indicate (s : Finset α) : ‖𝟭_[β] s‖_[1] = s.card := by
  simpa using lpNorm_pow_indicate one_ne_zero s

end indicate

section mu
variable {α β : Type*} [RCLike β] [Fintype α] [DecidableEq α] {s : Finset α} {p : ℝ≥0}

lemma lpNorm_mu (hp : 1 ≤ p) (hs : s.Nonempty) : ‖μ_[β] s‖_[p] = s.card ^ ((p : ℝ)⁻¹ - 1) := by
  rw [mu, lpNorm_smul (ENNReal.one_le_coe_iff.2 hp) (s.card⁻¹ : β) (𝟭_[β] s), lpNorm_indicate,
      norm_inv, RCLike.norm_natCast, inv_mul_eq_div, ← rpow_sub_one] <;> positivity

lemma lpNorm_mu_le (hp : 1 ≤ p) : ‖μ_[β] s‖_[p] ≤ s.card ^ (p⁻¹ - 1 : ℝ) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
    positivity
  · exact (lpNorm_mu hp hs).le

lemma l1Norm_mu (hs : s.Nonempty) : ‖μ_[β] s‖_[1] = 1 := by simpa using lpNorm_mu le_rfl hs

lemma l1Norm_mu_le_one : ‖μ_[β] s‖_[1] ≤ 1 := by simpa using lpNorm_mu_le le_rfl

end mu
