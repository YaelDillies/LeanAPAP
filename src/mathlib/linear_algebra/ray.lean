import linear_algebra.ray

namespace same_ray
variables {R M : Type*} [strict_ordered_comm_semiring R] [add_comm_monoid M] [module R M] {n : ℕ}
  {x y : M}

--TODO: Can we unify with `same_ray_nonneg_smul_right`?
/-- A vector is in the same ray as a nonnegative integer multiple of itself. -/
lemma _root_.same_ray_nsmul_right (v : M) (n : ℕ) : same_ray R v (n • v) :=
begin
  convert same_ray_nonneg_smul_right v _,
  swap,
  exact n,
  sorry,
  exact nat.cast_nonneg _,
end

--TODO: Can we unify with `same_ray_nonneg_smul_right`?
/-- A vector is in the same ray as a nonnegative integer multiple of itself. -/
lemma _root_.same_ray_nsmul_left (v : M) (n : ℕ) : same_ray R (n • v) v :=
(same_ray_nsmul_right _ _).symm

/-- A vector is in the same ray as a nonnegative integer multiple of one it is in the same ray as.
-/
lemma nsmul_right (h : same_ray R x y) (n : ℕ) : same_ray R x (n • y) :=
h.trans (same_ray_nsmul_right y _) $ λ hy, or.inr $ by rw [hy, smul_zero]

/-- A nonnegative integer multiple of a vector is in the same ray as one it is in the same ray as.
-/
lemma nsmul_left (h : same_ray R x y) (n : ℕ) : same_ray R (n • x) y := (h.symm.nsmul_right _).symm

end same_ray
