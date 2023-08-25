import Mathbin.Analysis.NormedSpace.Ray
import Project.Mathlib.LinearAlgebra.Ray

#align_import mathlib.analysis.normed_space.ray

section NormedAddCommGroup

variable {E : Type _} [NormedAddCommGroup E]

theorem norm_nsmul [NormedSpace ℝ E] (n : ℕ) (x : E) : ‖n • x‖ = n • ‖x‖ :=
  by
  induction' n with n ih
  · simp
  · rw [succ_nsmul, succ_nsmul, SameRay.norm_add, ih]
    exact sameRay_nsmul_right _ _

end NormedAddCommGroup

