import LeanAPAP.Prereqs.FourierTransform.Compact

/-!
# Large spectrum of a function
-/

open Finset Fintype
open scoped ComplexConjugate NNReal

variable {G : Type*} [AddCommGroup G] [Fintype G] [MeasurableSpace G] {f : G → ℂ} {η : ℝ}
  {ψ : AddChar G ℂ} {Δ : Finset (AddChar G ℂ)} {m : ℕ}

/-- The `η`-large spectrum of a function. -/
noncomputable def largeSpec (f : G → ℂ) (η : ℝ) : Finset (AddChar G ℂ) :=
  {ψ | η * ‖f‖ₙ_[1] ≤ ‖cft f ψ‖}

lemma mem_largeSpec_iff_cft : ψ ∈ largeSpec f η ↔ η * ‖f‖ₙ_[1] ≤ ‖cft f ψ‖ := by simp [largeSpec]
lemma mem_largeSpec_iff_dft : ψ ∈ largeSpec f η ↔ η * ‖f‖_[1] ≤ ‖dft f ψ‖ := by
  simp [largeSpec]; sorry

lemma largeSpec_anti (f : G → ℂ) : Antitone (largeSpec f) := fun η ν h ψ ↦ by
  simp_rw [mem_largeSpec_iff_cft]; exact (mul_le_mul_of_nonneg_right h (by positivity)).trans

@[simp] lemma largeSpec_zero_left (η : ℝ) : largeSpec (0 : G → ℂ) η = univ := by simp [largeSpec]
@[simp] lemma largeSpec_zero_right (f : G → ℂ) : largeSpec f 0 = univ := by simp [largeSpec]
