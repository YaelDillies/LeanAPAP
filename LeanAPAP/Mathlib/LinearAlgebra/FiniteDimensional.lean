import Mathlib.LinearAlgebra.FiniteDimensional

variable {ι K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

--TODO: Rename `linear_independent.finite` to `linear_independent.set_finite`
lemma LinearIndependent.finite' [FiniteDimensional K V] {f : ι → V} (h : LinearIndependent K f) :
    Finite ι :=
  Cardinal.lt_aleph0_iff_finite.1 $ FiniteDimensional.lt_aleph0_of_linearIndependent h
