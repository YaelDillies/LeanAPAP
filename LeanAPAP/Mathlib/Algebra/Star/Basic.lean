import Mathlib.Algebra.Star.Basic

/-!
# TODO

Swap arguments to `star_nsmul`/`star_zsmul`
-/

variable {α : Type*}

instance StarAddMonoid.toStarModuleInt [AddCommGroup α] [StarAddMonoid α] : StarModule ℤ α where
  star_smul _ _ := star_zsmul _ _
