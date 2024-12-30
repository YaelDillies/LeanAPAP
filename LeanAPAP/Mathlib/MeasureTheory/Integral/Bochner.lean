import Mathlib.MeasureTheory.Integral.Bochner

namespace MeasureTheory
variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {f : α → ℝ}

lemma abs_integral_le_integral_abs : |∫ a, f a ∂μ| ≤ ∫ a, |f a| ∂μ :=
  norm_integral_le_integral_norm f

end MeasureTheory
