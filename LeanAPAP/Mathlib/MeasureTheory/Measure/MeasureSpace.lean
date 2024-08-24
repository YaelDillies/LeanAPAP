import Mathlib.MeasureTheory.Measure.MeasureSpace

open scoped ENNReal

namespace MeasureTheory.Measure
variable {ι α : Type*} {mα : MeasurableSpace α} {f : ι → Measure α}

@[simp] lemma sum_eq_zero : sum f = 0 ↔ ∀ i, f i = 0 := by
  simp (config := { contextual := true }) [Measure.ext_iff, forall_swap (α := ι)]

variable {R : Type*} [Zero R] [SMulWithZero R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
  [NoZeroSMulDivisors R ℝ≥0∞] {c : ℝ≥0∞}

-- TODO: Replace in mathlib
lemma ae_smul_measure_iff' {p : α → Prop} {c : R} (hc : c ≠ 0) {μ : Measure α} :
    (∀ᵐ x ∂c • μ, p x) ↔ ∀ᵐ x ∂μ, p x := by simp [ae_iff, hc]

@[simp] lemma ae_smul_measure_eq' (hc : c ≠ 0) (μ : Measure α) : ae (c • μ) = ae μ := by
  ext; exact ae_smul_measure_iff hc

end MeasureTheory.Measure
