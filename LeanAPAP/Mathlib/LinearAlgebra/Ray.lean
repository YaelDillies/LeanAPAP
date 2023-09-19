import Mathlib.LinearAlgebra.Ray

section SameRay
variable {R M : Type*} [StrictOrderedCommSemiring R] [AddCommMonoid M] [Module R M] {n : ℕ}
  {x y : M}

--TODO: Can we unify with `sameRay_nonneg_smul_right`?
/-- A vector is in the same ray as a nonnegative integer multiple of itself. -/
lemma sameRay_nsmul_right (v : M) (n : ℕ) : SameRay R v (n • v) := by
  rw [nsmul_eq_smul_cast R]; exact SameRay.sameRay_nonneg_smul_right v (Nat.cast_nonneg _)

--TODO: Can we unify with `sameRay_nonneg_smul_right`?
/-- A vector is in the same ray as a nonnegative integer multiple of itself. -/
lemma sameRay_nsmul_left (v : M) (n : ℕ) : SameRay R (n • v) v :=
  (sameRay_nsmul_right _ _).symm

/-- A vector is in the same ray as a nonnegative integer multiple of one it is in the same ray as.
-/
lemma SameRay.nsmul_right (h : SameRay R x y) (n : ℕ) : SameRay R x (n • y) :=
  h.trans (sameRay_nsmul_right y _) λ hy ↦ Or.inr $ by rw [hy, smul_zero]

/-- A nonnegative integer multiple of a vector is in the same ray as one it is in the same ray as.
-/
lemma SameRay.nsmul_left (h : SameRay R x y) (n : ℕ) : SameRay R (n • x) y :=
  (h.symm.nsmul_right _).symm

end SameRay
