import LeanAPAP.Prereqs.AddChar.Basic
import LeanAPAP.Prereqs.Discrete.Convolution.Order
import LeanAPAP.Prereqs.Discrete.DFT.Compact

noncomputable section

open Finset Fintype Function Real
open scoped BigOperators Nat

variable {G : Type*} [AddCommGroup G] [Fintype G] {A : Finset G}

def energy (n : ℕ) (A : Finset G) (ν : G → ℂ) : ℝ :=
  ∑ γ in piFinset fun _ : Fin n ↦ A, ∑ δ in piFinset fun _ : Fin n ↦ A, ‖ν (∑ i, γ i - ∑ i, δ i)‖

@[simp]
lemma energy_nonneg (n : ℕ) (A : Finset G) (ν : G → ℂ) : 0 ≤ energy n A ν := by
  unfold energy; positivity

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

lemma lpNorm_cft_indicate_pow (n : ℕ) (A : Finset G) :
    ‖cft (𝟭 A)‖ₙ_[↑(2 * n)] ^ (2 * n) = boringEnergy n A := sorry


lemma lpNorm_dft_indicate_pow (n : ℕ) (A : Finset G) :
    ‖dft (𝟭 A)‖_[↑(2 * n)] ^ (2 * n) = card G * boringEnergy n A := by
  sorry
  -- obtain rfl | hn := n.eq_zero_or_pos
  -- · simp
  -- refine Complex.ofReal_injective ?_
  -- calc
  --   ↑(‖dft (𝟭 A)‖_[↑(2 * n)] ^ (2 * n))
  --     = ⟪dft (𝟭 A ∗^ n), dft (𝟭 A ∗^ n)⟫_[ℂ] := ?_
  --   _ = card G * ⟪𝟭 A ∗^ n, 𝟭 A ∗^ n⟫_[ℂ] := nl2Inner_dft _ _
  --   _ = ↑(card G * boringEnergy n A) := ?_
  -- · rw [lpNorm_pow_eq_sum]
  --   simp_rw [pow_mul', ←norm_pow _ n, Complex.ofReal_sum, Complex.ofReal_pow, ←Complex.conj_mul',
  --     l2Inner_eq_sum, dft_iterConv_apply]
  --   positivity
  -- · simp only [l2Inner_eq_sum, boringEnergy_eq, Complex.ofReal_mul, Complex.ofReal_nat_cast,
  --     Complex.ofReal_sum, Complex.ofReal_pow, mul_eq_mul_left_iff, Nat.cast_eq_zero, card_ne_zero,
  --     or_false, sq]
  --   congr with a
  --   simp
  --   sorry
  --   sorry

lemma l2Norm_dft_indicate (A : Finset G) : ‖dft (𝟭 A)‖_[2] = sqrt A.card := by
  sorry -- simpa using lpNorm_dft_indicate_pow 1 A
