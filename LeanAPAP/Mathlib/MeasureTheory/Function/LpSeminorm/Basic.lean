import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

noncomputable section

open TopologicalSpace MeasureTheory Filter
open scoped NNReal ENNReal Topology

variable {α E F G : Type*} {m m0 : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {μ ν : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G] {f : α → F}

namespace MeasureTheory

lemma eLpNormEssSup_lt_top_iff_isBoundedUnder :
    eLpNormEssSup f μ < ⊤ ↔ IsBoundedUnder (· ≤ ·) (ae μ) fun x ↦ ‖f x‖₊ where
  mp h := ⟨(eLpNormEssSup f μ).toNNReal, by
    simp_rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal h.ne]; exact ae_le_eLpNormEssSup⟩
  mpr := by rintro ⟨C, hC⟩; exact eLpNormEssSup_lt_top_of_ae_nnnorm_bound (C := C) hC

lemma eLpNorm_lt_top_of_finite [Finite α] [IsFiniteMeasure μ] : eLpNorm f p μ < ∞ := by
  obtain rfl | hp₀ := eq_or_ne p 0
  · simp
  obtain rfl | hp := eq_or_ne p ∞
  · simp only [eLpNorm_exponent_top, eLpNormEssSup_lt_top_iff_isBoundedUnder]
    sorry
  rw [eLpNorm_lt_top_iff_lintegral_rpow_nnnorm_lt_top hp₀ hp]
  refine IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal μ ?_
  sorry

@[simp] lemma Memℒp.of_discrete [DiscreteMeasurableSpace α] [Finite α] [IsFiniteMeasure μ] :
    Memℒp f p μ := by
  refine ⟨.of_finite, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_nnnorm_lt_top]
  refine IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal μ ?f_bdd
  sorry
  sorry
  sorry

@[simp] lemma eLpNorm_of_isEmpty [IsEmpty α] (f : α → E) (p : ℝ≥0∞) : eLpNorm f p μ = 0 := by
  simp [Subsingleton.elim f 0]

-- TODO: Make `p` and `μ` explicit in `eLpNorm_const_smul`

lemma eLpNorm_nsmul [NormedSpace ℝ F] (n : ℕ) (f : α → F) :
    eLpNorm (n • f) p μ = n * eLpNorm f p μ := by
  simpa [Nat.cast_smul_eq_nsmul] using eLpNorm_const_smul (n : ℝ) f

end MeasureTheory
