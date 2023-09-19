import Mathlib.Algebra.Star.Order
import Mathlib.GroupTheory.Submonoid.Operations
import LeanAPAP.Mathlib.Algebra.Star.Basic
import LeanAPAP.Mathlib.GroupTheory.Submonoid.Operations

open Set

open scoped ComplexConjugate

variable {R : Type*}

section CommSemiring
variable [CommSemiring R] [PartialOrder R] [StarOrderedRing R] {x : R}

private lemma star_nonneg_of_nonneg (hx : 0 ≤ x) : 0 ≤ star x := by
  rw [StarOrderedRing.nonneg_iff, AddSubmonoid.mem_closure] at hx ⊢
  rintro s hs
  have := hx (s.map $ starRingEnd R) (Subset.trans ?_ (image_subset _ hs))
  simpa only [starRingEnd_apply, star_involutive.eq_iff, AddSubmonoid.mem_map, exists_prop,
    exists_eq_right] using this
  simp [←range_comp, mul_comm, Function.comp, starRingEnd_apply, Subset.rfl]

@[simp] lemma star_nonneg : 0 ≤ star x ↔ 0 ≤ x :=
  ⟨λ hx ↦ by simpa only [star_star] using star_nonneg_of_nonneg hx, star_nonneg_of_nonneg⟩

@[simp] lemma star_pos : 0 < star x ↔ 0 < x := by
  simp_rw [lt_iff_le_and_ne, star_nonneg, @ne_comm R 0, star_ne_zero]

end CommSemiring

section CommRing
variable [CommRing R] [PartialOrder R] [StarOrderedRing R] {x : R}

@[simp] lemma star_nonpos : star x ≤ 0 ↔ x ≤ 0 := by simp_rw [←neg_nonneg, ←star_neg, star_nonneg]
@[simp] lemma star_neg' : star x < 0 ↔ x < 0 := by simp_rw [←neg_pos, ←star_neg, star_pos]

end CommRing

instance : StarOrderedRing ℕ where
  le_iff a b := by
    have : AddSubmonoid.closure (range λ x : ℕ ↦ x * x) = ⊤ :=
      eq_top_mono
        (AddSubmonoid.closure_mono $ singleton_subset_iff.2 $ mem_range.2 ⟨1, one_mul _⟩)
        Nat.addSubmonoid_closure_one
    simp [this, le_iff_exists_add]

instance : StarOrderedRing ℚ where
  le_iff a b := by
    have : AddSubmonoid.closure (range λ x : ℕ ↦ x * x) = ⊤ :=
      eq_top_mono
        (AddSubmonoid.closure_mono $ singleton_subset_iff.2 $ mem_range.2 ⟨1, one_mul _⟩)
        Nat.addSubmonoid_closure_one
    simp [this, le_iff_exists_nonneg_add a b]
