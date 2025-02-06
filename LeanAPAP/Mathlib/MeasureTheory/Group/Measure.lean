import Mathlib.Algebra.Group.Pointwise.Set.Card
import Mathlib.MeasureTheory.Group.Measure
import LeanAPAP.Mathlib.Data.Set.Card
import LeanAPAP.Mathlib.MeasureTheory.Measure.Count

open Set

namespace MeasureTheory.Measure
variable {G : Type*} [MeasurableSpace G] [Group G]

section MeasurableMul
variable [MeasurableMul G]

@[to_additive]
instance : (count : Measure G).IsMulLeftInvariant where
  map_mul_left_eq_self g := by
    ext s hs
    rw [count_apply' hs, map_apply (measurable_const_mul _) hs,
      count_apply' (measurable_const_mul _ hs),
      encard_preimage_of_bijective (Group.mulLeft_bijective _)]

@[to_additive]
instance : (count : Measure G).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    ext s hs
    rw [count_apply' hs, map_apply (measurable_mul_const _) hs,
      count_apply' (measurable_mul_const _ hs),
      encard_preimage_of_bijective (Group.mulRight_bijective _)]

end MeasurableMul

section MeasurableInv
variable [MeasurableInv G]

@[to_additive]
instance : (count : Measure G).IsInvInvariant where
  inv_eq_self := by ext s hs; rw [count_apply' hs, inv_apply, count_apply' hs.inv, encard_inv]

end MeasurableInv
end MeasureTheory.Measure
