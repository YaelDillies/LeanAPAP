import Mathlib.MeasureTheory.Measure.Typeclasses
import LeanAPAP.Mathlib.MeasureTheory.OuterMeasure.Basic

open Set
open scoped ENNReal

namespace MeasureTheory
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {a : α}

lemma measure_singleton_lt_top [SigmaFinite μ] : μ {a} < ∞ :=
  measure_lt_top_mono (singleton_subset_iff.2 <| mem_spanningSetsIndex ..)
    (measure_spanningSets_lt_top _ _)

variable [Countable α]

/-- A measure on a countable space is sigma-finite iff it gives finite mass to every singleton. -/
lemma sigmaFinite_iff_measure_singleton_lt_top : SigmaFinite μ ↔ ∀ a, μ {a} < ∞ where
  mp _ a := measure_singleton_lt_top
  mpr hμ := by
    cases isEmpty_or_nonempty α
    · rw [Subsingleton.elim μ 0]
      infer_instance
    · obtain ⟨f, hf⟩ := exists_surjective_nat α
      exact ⟨⟨⟨fun n ↦ {f n}, by simp, by simpa [hf.forall] using hμ, by simp [hf.range_eq]⟩⟩⟩

end MeasureTheory
