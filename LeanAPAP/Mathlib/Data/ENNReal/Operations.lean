import Mathlib.Algebra.Module.Basic
import Mathlib.Data.ENNReal.Operations

open scoped NNReal

namespace ENNReal

lemma nnreal_smul_lt_top {x : ℝ≥0} {y : ℝ≥0∞} (hy : y < ⊤) : x • y < ⊤ := mul_lt_top (by simp) hy
lemma nnreal_smul_ne_top {x : ℝ≥0} {y : ℝ≥0∞} (hy : y ≠ ⊤) : x • y ≠ ⊤ := mul_ne_top (by simp) hy

lemma nnreal_smul_ne_top_iff {x : ℝ≥0} {y : ℝ≥0∞} (hx : x ≠ 0) : x • y ≠ ⊤ ↔ y ≠ ⊤ :=
  ⟨by rintro h rfl; simp [smul_top, hx] at h, nnreal_smul_ne_top⟩

lemma nnreal_smul_lt_top_iff {x : ℝ≥0} {y : ℝ≥0∞} (hx : x ≠ 0) : x • y < ⊤ ↔ y < ⊤ := by
  rw [lt_top_iff_ne_top, lt_top_iff_ne_top, nnreal_smul_ne_top_iff hx]

end ENNReal
