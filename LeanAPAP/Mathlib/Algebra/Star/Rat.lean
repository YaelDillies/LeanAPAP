import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Star.Rat

variable {α : Type*}

@[simp] lemma star_nnqsmul [AddCommMonoid α] [Module ℚ≥0 α] [StarAddMonoid α] (q : ℚ≥0) (a : α) :
    star (q • a) = q • star a := sorry

@[simp] lemma star_qsmul [AddCommGroup α] [Module ℚ α] [StarAddMonoid α] (q : ℚ) (a : α) :
    star (q • a) = q • star a := sorry

instance StarAddMonoid.toStarModuleNNRat [AddCommMonoid α] [Module ℚ≥0 α] [StarAddMonoid α] :
    StarModule ℚ≥0 α where star_smul := star_nnqsmul

instance StarAddMonoid.toStarModuleRat [AddCommGroup α] [Module ℚ α] [StarAddMonoid α] :
    StarModule ℚ α where star_smul := star_qsmul
