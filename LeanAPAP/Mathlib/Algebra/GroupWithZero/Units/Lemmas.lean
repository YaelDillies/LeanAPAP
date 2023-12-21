import Mathlib.Algebra.GroupWithZero.Units.Lemmas

namespace IsUnit
variable {α : Type*} [DivisionMonoid α] {a b c d : α}

@[to_additive]
lemma div_eq_div_iff_of_commute (hbd : Commute b d) (hb : IsUnit b) (hd : IsUnit d) :
    a / b = c / d ↔ a * d = c * b := by
  rw [← (hb.mul hd).mul_left_inj, ← mul_assoc, hb.div_mul_cancel, ← mul_assoc, hbd.right_comm,
    hd.div_mul_cancel]

end IsUnit

namespace Commute
variable {α : Type*} [GroupWithZero α] {a b c d : α}

protected lemma div_eq_div_iff (hbd : Commute b d) (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b = c / d ↔ a * d = c * b := IsUnit.div_eq_div_iff_of_commute hbd hb.isUnit hd.isUnit

end Commute
