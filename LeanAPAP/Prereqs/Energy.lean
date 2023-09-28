import LeanAPAP.Mathlib.NumberTheory.LegendreSymbol.AddChar.Basic
import LeanAPAP.Prereqs.Convolution.Order
import LeanAPAP.Prereqs.Rudin

noncomputable section

open Finset Fintype

open scoped BigOperators Nat

variable {G : Type*} [AddCommGroup G] [Fintype G] {A : Finset G}

def energy (n : ℕ) (A : Finset G) (ν : G → ℂ) : ℝ :=
  ∑ γ in piFinset λ _ : Fin n ↦ A, ∑ δ in piFinset λ _ : Fin n ↦ A, ‖ν (∑ i, γ i - ∑ i, δ i)‖

@[simp]
lemma energy_nonneg (n : ℕ) (A : Finset G) (ν : G → ℂ) : 0 ≤ energy n A ν :=
  sum_nonneg λ _γ _ ↦ sum_nonneg λ _δ _ ↦ norm_nonneg _

lemma energy_nsmul (m n : ℕ) (A : Finset G) (ν : G → ℂ) : energy n A (m • ν) = m • energy n A ν := by
  simp only [energy, nsmul_eq_mul, mul_sum, @Pi.coe_nat G (λ _ ↦ ℂ) _ m, Pi.mul_apply, norm_mul,
    Complex.norm_nat]

variable [DecidableEq G]

def boringEnergy (n : ℕ) (A : Finset G) : ℝ :=
  energy n A trivChar

lemma boringEnergy_eq (n : ℕ) (A : Finset G) : boringEnergy n A = ∑ x, (𝟭 A ∗^ n) x ^ 2 := by
  classical
  simp only [boringEnergy, energy, apply_ite norm, trivChar_apply, norm_one, norm_zero, sum_boole,
    sub_eq_zero]
  rw [←Finset.sum_fiberwise _ λ f : Fin n → G ↦ ∑ i, f i]
  congr with x
  rw [indicate_iterConv_apply, sq, ←nsmul_eq_mul, ←sum_const]
  refine' sum_congr rfl λ f hf ↦ _
  simp_rw [(mem_filter.1 hf).2, eq_comm]

--TODO(Thomas): Figure out the constant
def thomasConst : ℝ := 8 * Real.exp 1

lemma Finset.AddDissociated.indicate_iterConv_apply_le (hA : A.AddDissociated) :
    ∀ (n : ℕ) (a : G), (𝟭_[ℝ] A ∗^ n) a ≤ thomasConst ^ n * n ^ n :=
  sorry

lemma Finset.AddDissociated.boringEnergy_le (hA : A.AddDissociated) (n : ℕ) :
    boringEnergy n A ≤ thomasConst ^ n * n ^ n * A.card ^ n :=
  calc
    boringEnergy n A = ∑ x, (𝟭 A ∗^ n) x * (𝟭 A ∗^ n) x := by simp_rw [boringEnergy_eq, sq]
    _ ≤ ∑ x, (thomasConst : ℝ) ^ n * n ^ n * (𝟭 A ∗^ n) x :=
      (sum_le_sum λ x _ ↦
        mul_le_mul_of_nonneg_right (hA.indicate_iterConv_apply_le _ _) $
          iterConv_nonneg indicate_nonneg _)
    _ = _ := by rw [←mul_sum, sum_iterConv, sum_indicate]
