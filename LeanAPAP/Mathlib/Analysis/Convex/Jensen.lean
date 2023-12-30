import Mathlib.Analysis.Convex.Jensen

open Set
open scoped Convex

section MaximumPrinciple
variable {ι 𝕜 E β} [LinearOrderedField 𝕜] [AddCommGroup E] [LinearOrderedAddCommGroup β] [Module 𝕜 E]
  [Module 𝕜 β] [OrderedSMul 𝕜 β] {s : Set E} {f : E → β} {t : Finset ι} {w : ι → 𝕜} {p : ι → E}
  {x y z : E}

/-- **Maximum principle** for convex functions on a segment. If a function `f` is convex on the
segment `[x, y]`, then the eventual maximum of `f` on `[x, y]` is at `x` or `y`. -/
lemma ConvexOn.le_max_of_mem_segment (hf : ConvexOn 𝕜 [x -[𝕜] y] f) (hz : z ∈ [x -[𝕜] y]) :
    f z ≤ max (f x) (f y) := by
  rw [← convexHull_pair] at hf hz; simpa using hf.exists_ge_of_mem_convexHull hz

/-- **Minimum principle** for concave functions on a segment. If a function `f` is concave on the
segment `[x, y]`, then the eventual minimum of `f` on `[x, y]` is at `x` or `y`. -/
lemma ConcaveOn.min_le_of_mem_segment (hf : ConcaveOn 𝕜 [x -[𝕜] y] f) (hz : z ∈ [x -[𝕜] y]) :
    min (f x) (f y) ≤ f z := by
  rw [← convexHull_pair] at hf hz; simpa using hf.exists_le_of_mem_convexHull hz

/-- **Maximum principle** for convex functions on an interval. If a function `f` is convex on the
interval `[x, y]`, then the eventual maximum of `f` on `[x, y]` is at `x` or `y`. -/
lemma ConvexOn.le_max_of_mem_Icc {f : 𝕜 → β} {x y z : 𝕜} (hf : ConvexOn 𝕜 (Icc x y) f)
    (hz : z ∈ Icc x y) : f z ≤ max (f x) (f y) := by
  rw [← segment_eq_Icc (hz.1.trans hz.2)] at hf hz; exact hf.le_max_of_mem_segment hz

/-- **Minimum principle** for concave functions on an interval. If a function `f` is concave on the
interval `[x, y]`, then the eventual minimum of `f` on `[x, y]` is at `x` or `y`. -/
lemma ConcaveOn.min_le_of_mem_Icc {f : 𝕜 → β} {x y z : 𝕜} (hf : ConcaveOn 𝕜 (Icc x y) f)
    (hz : z ∈ Icc x y) : min (f x) (f y) ≤ f z := by
  rw [← segment_eq_Icc (hz.1.trans hz.2)] at hf hz; exact hf.min_le_of_mem_segment hz

end MaximumPrinciple
