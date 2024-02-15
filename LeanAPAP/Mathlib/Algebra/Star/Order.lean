import Mathlib.Algebra.Star.Order
import LeanAPAP.Mathlib.GroupTheory.Submonoid.Operations

open Set

open scoped ComplexConjugate

variable {R : Type*}

instance : StarOrderedRing ℕ where
  le_iff a b := by
    have : AddSubmonoid.closure (range fun x : ℕ ↦ x * x) = ⊤ :=
      eq_top_mono
        (AddSubmonoid.closure_mono $ singleton_subset_iff.2 $ mem_range.2 ⟨1, one_mul _⟩)
        Nat.addSubmonoid_closure_one
    simp [this, le_iff_exists_add]

instance : StarOrderedRing ℚ where
  le_iff a b := by
    have : AddSubmonoid.closure (range fun x : ℕ ↦ x * x) = ⊤ :=
      eq_top_mono
        (AddSubmonoid.closure_mono $ singleton_subset_iff.2 $ mem_range.2 ⟨1, one_mul _⟩)
        Nat.addSubmonoid_closure_one
    simp [this, le_iff_exists_nonneg_add a b]
