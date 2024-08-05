import Mathlib.Data.Rat.Cast.Order

namespace NNRat
variable {K : Type*} [LinearOrderedSemifield K] {p : ℚ≥0}

@[simp, norm_cast] lemma cast_le_one : (p : K) ≤ 1 ↔ p ≤ 1 := by rw [← cast_le (K := K), cast_one]
@[simp, norm_cast] lemma one_le_cast : 1 ≤ (p : K) ↔ 1 ≤ p := by rw [← cast_le (K := K), cast_one]
@[simp, norm_cast] lemma cast_lt_one : (p : K) < 1 ↔ p < 1 := by rw [← cast_lt (K := K), cast_one]
@[simp, norm_cast] lemma one_lt_cast : 1 < (p : K) ↔ 1 < p := by rw [← cast_lt (K := K), cast_one]

end NNRat
