import LeanAPAP.Mathlib.NumberTheory.LegendreSymbol.AddChar.Basic
import LeanAPAP.Prereqs.Convolution.Order
import LeanAPAP.Prereqs.Rudin

noncomputable section

open Finset Fintype Function Real
open scoped BigOperators Nat

variable {G : Type*} [AddCommGroup G] [Fintype G] {A : Finset G}

def energy (n : ℕ) (A : Finset G) (ν : G → ℂ) : ℝ :=
  ∑ γ in piFinset fun _ : Fin n ↦ A, ∑ δ in piFinset fun _ : Fin n ↦ A, ‖ν (∑ i, γ i - ∑ i, δ i)‖

@[simp]
lemma energy_nonneg (n : ℕ) (A : Finset G) (ν : G → ℂ) : 0 ≤ energy n A ν :=
  sum_nonneg fun _γ _ ↦ sum_nonneg fun _δ _ ↦ norm_nonneg _

lemma energy_nsmul (m n : ℕ) (A : Finset G) (ν : G → ℂ) :
    energy n A (m • ν) = m • energy n A ν := by
  simp only [energy, nsmul_eq_mul, mul_sum, @Pi.coe_nat G (fun _ ↦ ℂ) _ m, Pi.mul_apply, norm_mul,
    Complex.norm_nat]

@[simp] lemma energy_zero (A : Finset G) (ν : G → ℂ) : energy 0 A ν = ‖ν 0‖ := by simp [energy]

variable [DecidableEq G]

def boringEnergy (n : ℕ) (A : Finset G) : ℝ := energy n A trivChar

lemma boringEnergy_eq (n : ℕ) (A : Finset G) : boringEnergy n A = ∑ x, (𝟭 A ∗^ n) x ^ 2 := by
  classical
  simp only [boringEnergy, energy, apply_ite norm, trivChar_apply, norm_one, norm_zero, sum_boole,
    sub_eq_zero]
  rw [←Finset.sum_fiberwise _ fun f : Fin n → G ↦ ∑ i, f i]
  congr with x
  rw [indicate_iterConv_apply, sq, ←nsmul_eq_mul, ←sum_const]
  refine' sum_congr rfl fun f hf ↦ _
  simp_rw [(mem_filter.1 hf).2, eq_comm]

@[simp] lemma boringEnergy_zero (A : Finset G) : boringEnergy 0 A = 1 := by simp [boringEnergy]
@[simp] lemma boringEnergy_one (A : Finset G) : boringEnergy 1 A = A.card := by
  simp [boringEnergy_eq, indicate_apply]

example {n : ℕ} : ((n : NNReal) : ENNReal) = n := by rw [ENNReal.coe_nat]

lemma lpNorm_dft_indicate_pow (n : ℕ) (A : Finset G) :
    ‖dft (𝟭 A)‖_[↑(2 * n)] ^ (2 * n) = card G * boringEnergy n A := by
  obtain rfl | hn := n.eq_zero_or_pos
  · sorry -- simp
  refine Complex.ofReal_injective ?_
  calc
    ↑(‖dft (𝟭 A)‖_[↑(2 * n)] ^ (2 * n))
      = ⟪dft (𝟭 A ∗^ n), dft (𝟭 A ∗^ n)⟫_[ℂ] := ?_
    _ = card G * ⟪𝟭 A ∗^ n, 𝟭 A ∗^ n⟫_[ℂ] := l2inner_dft _ _
    _ = ↑(card G * boringEnergy n A) := ?_
  · rw [lpNorm_pow_eq_sum]
    simp_rw [pow_mul', ←norm_pow _ n, Complex.ofReal_sum, Complex.ofReal_pow, ←Complex.conj_mul',
      l2inner_eq_sum, dft_iterConv_apply]
    positivity
  · simp only [l2inner_eq_sum, boringEnergy_eq, Complex.ofReal_mul, Complex.ofReal_nat_cast,
      Complex.ofReal_sum, Complex.ofReal_pow, mul_eq_mul_left_iff, Nat.cast_eq_zero, card_ne_zero,
      or_false, sq]
    congr with a
    simp
    sorry
    sorry

lemma l2Norm_dft_indicate (A : Finset G) : ‖dft (𝟭 A)‖_[2] = sqrt A.card := by
  sorry -- simpa using lpNorm_dft_indicate_pow 1 A

def changConst : ℝ := 8 * Real.exp 1

lemma one_lt_changConst : 1 < changConst := one_lt_mul (by norm_num) $ one_lt_exp_iff.2 one_pos

lemma AddDissociated.boringEnergy_le (hA : AddDissociated (A : Set G)) (n : ℕ) :
    boringEnergy n A ≤ changConst ^ n * n ^ n * A.card ^ n := by
  obtain rfl | hn := n.eq_zero_or_pos
  · simp
  have := rudin_ineq (le_mul_of_one_le_right zero_le_two $ Nat.one_le_iff_ne_zero.2 hn.ne')
    (dft (𝟭_[ℂ] A)) ?_
  · replace this := pow_le_pow_of_le_left ?_ this (2 * n)
    rw [lpNorm_dft_indicate_pow, l2Norm_dft_indicate] at this
    convert this using 0
    simp_rw [mul_pow, pow_mul]
    rw [exp_pow, sq_sqrt, sq_sqrt]
    simp_rw [←mul_pow]
    simp [changConst]
    ring_nf
    all_goals sorry -- positivity
  rwa [dft_dft, ←nsmul_eq_mul, support_smul', support_comp_eq_preimage, support_indicate,
    Set.preimage_comp, Set.neg_preimage, addDissociated_neg, AddEquiv.addDissociated_preimage]
  sorry -- positivity
