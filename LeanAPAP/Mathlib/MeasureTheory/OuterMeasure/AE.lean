import Mathlib.MeasureTheory.OuterMeasure.AE

open Filter MeasureTheory ENNReal Set

variable {F α β : Type*} [FunLike F (Set α) ℝ≥0∞] [OuterMeasureClass F α] {μ : F} {f : α → β}

lemma ae_eq_rfl : f =ᵐ[μ] f := ae_eq_refl _

@[simp] lemma ae_eq_top  : ae μ = ⊤ ↔ ∀ a, μ {a} ≠ 0 := by
  simp only [Filter.ext_iff, mem_ae_iff, mem_top, ne_eq]
  refine ⟨fun h a ha ↦ by simpa [ha] using (h {a}ᶜ).1, fun h s ↦ ⟨fun hs ↦ ?_, ?_⟩⟩
  · rw [← compl_empty_iff, ← not_nonempty_iff_eq_empty]
    rintro ⟨a, ha⟩
    exact h _ $ measure_mono_null (singleton_subset_iff.2 ha) hs
  · rintro rfl
    simp
