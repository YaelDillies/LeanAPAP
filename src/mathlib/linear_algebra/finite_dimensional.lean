import linear_algebra.finite_dimensional

variables {ι K V : Type*} [division_ring K] [add_comm_group V] [module K V]

--TODO: Rename `linear_independent.finite` to `linear_independent.set_finite`
lemma linear_independent.finite' [finite_dimensional K V] {f : ι → V} (h : linear_independent K f) :
  finite ι :=
cardinal.lt_aleph_0_iff_finite.1 $ finite_dimensional.lt_aleph_0_of_linear_independent h
