import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Tactic.Positivity.Basic
import LeanAPAP.Prereqs.NNRat.Algebra

namespace NNRat

@[simp] lemma cast_pos {α : Type*} [LinearOrderedSemifield α] {q : ℚ≥0} : 0 < (q : α) ↔ 0 < q := by
  rw [cast_def, div_pos_iff_of_pos_right, Nat.cast_pos, num_pos]; positivity

instance {α : Type*} [LinearOrderedSemifield α] [Module ℚ≥0 α] [CompAction α] :
    PosSMulStrictMono ℚ≥0 α where
  elim q hq a b hab := by
    rw [NNRat.smul_def, NNRat.smul_def]
    exact mul_lt_mul_of_pos_left hab $ cast_pos.2 hq

end NNRat
