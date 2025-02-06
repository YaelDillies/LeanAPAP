import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

open Set

namespace ENNReal
variable {α : Type*} (s : Set α)

-- TODO: Replace
alias tsum_set_one := tsum_set_one_eq
alias tsum_set_const := tsum_set_const_eq

@[simp]
lemma tsum_one : ∑' _ : α, (1 : ℝ≥0∞) = ENat.card α := by
  rw [← tsum_univ]
  simpa [-tsum_set_one_eq, -tsum_set_const_eq, encard_univ, tsum_univ] using tsum_set_one univ

-- TODO: Delete `tsum_const_eq`
@[simp]
lemma tsum_const (c : ℝ≥0∞) : ∑' _ : α, c = ENat.card α * c := by
  rw [← tsum_univ]
  simpa [-tsum_set_one_eq, -tsum_set_const_eq, encard_univ, tsum_univ] using tsum_set_const univ c

end ENNReal
