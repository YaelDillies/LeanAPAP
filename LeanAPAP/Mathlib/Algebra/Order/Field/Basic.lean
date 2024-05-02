import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Basic
import LeanAPAP.Mathlib.Data.NNRat.Defs

namespace NNRat
variable {α : Type*} [LinearOrderedSemifield α] {q : ℚ≥0}

@[simp] lemma cast_pos : 0 < (q : α) ↔ 0 < q := by
  rw [cast_def, div_pos_iff_of_pos_right, Nat.cast_pos, num_pos]; positivity

end NNRat
