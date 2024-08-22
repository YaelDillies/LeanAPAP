import Mathlib.Analysis.RCLike.Basic

/-!
# TODO

Rename `Real.RCLike` to `Real.instRCLike`
-/

open scoped ComplexConjugate

namespace RCLike
variable {K : Type*} [RCLike K] {z : K}

@[simp] lemma nnnorm_conj : ‖conj z‖₊ = ‖z‖₊ := by simp [nnnorm]
@[simp] lemma nnnorm_natCast (n : ℕ) : ‖(n : K)‖₊ = n := by simp [nnnorm]

end RCLike
