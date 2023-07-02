import algebra.star.order
import group_theory.submonoid.operations

open set
open_locale complex_conjugate

variables {R : Type*}

section comm_semiring
variables [comm_semiring R] [partial_order R] [star_ordered_ring R] {x : R}

private lemma star_nonneg_of_nonneg (hx : 0 ≤ x) : 0 ≤ star x :=
begin
  rw [star_ordered_ring.nonneg_iff, add_submonoid.mem_closure] at ⊢ hx,
  rintro s hs,
  simpa only [star_ring_end_apply, star_involutive.eq_iff, add_submonoid.mem_map,
    exists_prop, exists_eq_right] using hx (s.map $ star_ring_end R) _,
  refine subset.trans _ (image_subset _ hs),
  simp [←range_comp, mul_comm, function.comp, star_ring_end_apply],
end

@[simp] lemma star_nonneg : 0 ≤ star x ↔ 0 ≤ x :=
⟨λ hx, by simpa only [star_star] using star_nonneg_of_nonneg hx, star_nonneg_of_nonneg⟩

@[simp] lemma star_pos : 0 < star x ↔ 0 < x :=
by simp_rw [lt_iff_le_and_ne, star_nonneg, @ne_comm R 0, star_ne_zero]

end comm_semiring

section comm_ring
variables [comm_ring R] [partial_order R] [star_ordered_ring R] {x : R}

@[simp] lemma star_nonpos : star x ≤ 0 ↔ x ≤ 0 := by simp_rw [←neg_nonneg, ←star_neg, star_nonneg]
@[simp] lemma star_neg' : star x < 0 ↔ x < 0 := by simp_rw [←neg_pos, ←star_neg, star_pos]

end comm_ring
