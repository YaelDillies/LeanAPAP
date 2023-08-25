import Mathbin.Data.Real.Sqrt
import Project.Mathlib.Data.Real.Nnreal
import Project.Mathlib.Algebra.BigOperators.Order
import Project.Mathlib.GroupTheory.Submonoid.Basic

#align_import mathlib.data.real.sqrt

open NNReal Set

open scoped BigOperators NNReal

instance : StarOrderedRing ℝ≥0 :=
  { NNReal.orderedCommSemiring with
    le_iff := fun x y => by
      constructor; swap
      · rintro ⟨p, hp, rfl⟩
        exact le_self_add
      rw [← NNReal.coe_le_coe, StarOrderedRing.le_iff]
      rintro ⟨p, hp, h⟩
      refine'
        ⟨⟨p,
            (AddSubmonoid.closure_le.2 (range_subset_iff.2 fun x => _) hp :
              p ∈ AddSubmonoid.nonneg ℝ)⟩,
          _, NNReal.coe_injective h⟩
      · simp [mul_self_nonneg]
      ·
        exact
          AddSubmonoid.subset_closure
            ⟨NNReal.sqrt _, by dsimp <;> rw [star_trivial, ← sqrt_mul, sqrt_mul_self]⟩ }

namespace Finset

theorem cauchy_schwarz_sqrt {α : Type _} (s : Finset α) (f g : α → ℝ) :
    ∑ i in s, f i * g i ≤ (∑ i in s, f i ^ 2).sqrt * (∑ i in s, g i ^ 2).sqrt :=
  (Real.le_sqrt_of_sq_le <| sum_hMul_sq_le_sq_hMul_sq _ _ _).trans_eq <|
    Real.sqrt_mul (sum_nonneg fun _ _ => sq_nonneg _) _

end Finset

namespace NNReal

variable {x : ℝ≥0}

@[simp]
theorem one_le_sqrt : 1 ≤ x.sqrt ↔ 1 ≤ x := by rw [← sqrt_one, sqrt_le_sqrt_iff, sqrt_one]

end NNReal

namespace Real

variable {x y : ℝ}

theorem sqrt_le_sqrt_iff' (hx : 0 < x) : x.sqrt ≤ y.sqrt ↔ x ≤ y :=
  by
  obtain hy | hy := le_total y 0
  ·
    exact
      iff_of_false ((sqrt_eq_zero_of_nonpos hy).trans_lt <| sqrt_pos.2 hx).not_le
        (hy.trans_lt hx).not_le
  · exact sqrt_le_sqrt_iff hy

@[simp]
theorem one_le_sqrt : 1 ≤ x.sqrt ↔ 1 ≤ x := by
  rw [← sqrt_one, sqrt_le_sqrt_iff' zero_lt_one, sqrt_one]

end Real

