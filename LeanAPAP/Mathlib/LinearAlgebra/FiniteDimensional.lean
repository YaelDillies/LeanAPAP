import Mathbin.LinearAlgebra.FiniteDimensional

#align_import mathlib.linear_algebra.finite_dimensional

variable {ι K V : Type _} [DivisionRing K] [AddCommGroup V] [Module K V]

--TODO: Rename `linear_independent.finite` to `linear_independent.set_finite`
theorem LinearIndependent.finite' [FiniteDimensional K V] {f : ι → V} (h : LinearIndependent K f) :
    Finite ι :=
  Cardinal.lt_aleph0_iff_finite.1 <| FiniteDimensional.lt_aleph0_of_linearIndependent h

