import Project.Mathlib.NumberTheory.LegendreSymbol.AddChar.Basic
import Project.Prereqs.Convolution.Order
import Project.Prereqs.Dissociation

#align_import prereqs.energy

noncomputable section

open Finset Fintype

open scoped BigOperators Nat

variable {G : Type _} [AddCommGroup G] [Fintype G] {A : Finset G}

def energy (n : ℕ) (A : Finset G) (ν : G → ℂ) : ℝ :=
  ∑ γ in piFinset fun _ : Fin n => A, ∑ δ in piFinset fun _ : Fin n => A, ‖ν (∑ i, γ i - ∑ i, δ i)‖

@[simp]
theorem energy_nonneg (n : ℕ) (A : Finset G) (ν : G → ℂ) : 0 ≤ energy n A ν :=
  sum_nonneg fun γ _ => sum_nonneg fun δ _ => norm_nonneg _

theorem energy_nsmul (m n : ℕ) (A : Finset G) (ν : G → ℂ) : energy n A (m • ν) = m • energy n A ν :=
  by
  simp only [energy, nsmul_eq_mul, mul_sum, @Pi.coe_nat G (fun _ => ℂ) _ m, Pi.mul_apply, norm_mul,
    Complex.norm_nat]

variable [DecidableEq G]

def boringEnergy (n : ℕ) (A : Finset G) : ℝ :=
  energy n A trivChar

theorem boringEnergy_eq (n : ℕ) (A : Finset G) : boringEnergy n A = ∑ x, (𝟭 A ∗^ n) x ^ 2 := by
  classical
  simp only [boringEnergy, energy, apply_ite norm, trivChar_apply, norm_one, norm_zero, sum_boole,
    sub_eq_zero]
  rw [← Finset.sum_fiberwise _ fun f : Fin n → G => ∑ i, f i]
  congr with x
  rw [indicate_iterConv_apply, sq, ← nsmul_eq_mul, ← sum_const]
  refine' sum_congr rfl fun f hf => _
  simp_rw [(mem_filter.1 hf).2, eq_comm]

--TODO(Thomas): Figure out the constant
def thomasConst : ℕ :=
  sorry

theorem Finset.AddDissociated.indicate_iterConv_apply_le (hA : A.AddDissociated) :
    ∀ (n : ℕ) (a : G), (𝟭_[ℝ] A ∗^ n) a ≤ thomasConst ^ n * n ^ n :=
  sorry

theorem Finset.AddDissociated.boringEnergy_le (hA : A.AddDissociated) (n : ℕ) :
    boringEnergy n A ≤ thomasConst ^ n * n ^ n * A.card ^ n :=
  calc
    boringEnergy n A = ∑ x, (𝟭 A ∗^ n) x * (𝟭 A ∗^ n) x := by simp_rw [boringEnergy_eq, sq]
    _ ≤ ∑ x, thomasConst ^ n * n ^ n * (𝟭 A ∗^ n) x :=
      (sum_le_sum fun x _ =>
        mul_le_mul_of_nonneg_right (hA.indicate_iterConv_apply_le _ _) <|
          iterConv_nonneg indicate_nonneg _)
    _ = _ := by rw [← mul_sum, sum_iterConv, sum_indicate]

