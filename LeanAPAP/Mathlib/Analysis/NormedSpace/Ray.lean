import Mathlib.Analysis.NormedSpace.Ray
import LeanAPAP.Mathlib.LinearAlgebra.Ray

section NormedAddCommGroup
variable {E : Type*} [NormedAddCommGroup E]

lemma norm_nsmul [NormedSpace ℝ E] (n : ℕ) (x : E) : ‖n • x‖ = n • ‖x‖ := by
  induction' n with n ih
  · simp
  · rw [succ_nsmul, succ_nsmul, SameRay.norm_add, ih]
    exact sameRay_nsmul_right _ _

end NormedAddCommGroup
