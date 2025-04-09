import Mathlib.MeasureTheory.OuterMeasure.Basic

open scoped ENNReal

namespace MeasureTheory
variable {α F : Type*} [FunLike F (Set α) ENNReal] [OuterMeasureClass F α] {μ : F} {s t : Set α}

lemma measure_eq_top_mono (h : s ⊆ t) (hs : μ s = ∞) : μ t = ∞ := eq_top_mono (measure_mono h) hs
lemma measure_lt_top_mono (h : s ⊆ t) (ht : μ t < ∞) : μ s < ∞ := (measure_mono h).trans_lt ht

end MeasureTheory
