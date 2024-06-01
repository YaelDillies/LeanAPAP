import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Data.Real.Basic

open scoped Pointwise

namespace Finset
variable {α : Type*} [CommGroup α] [DecidableEq α] {A B C : Finset α}

/-- The **Plünnecke-Ruzsa inequality**. Multiplication version.

Note that this is genuinely harder than the division version because we cannot use a double counting
argument. -/
@[to_additive "The **Plünnecke-Ruzsa inequality**. Addition version.

Note that this is genuinely harder than the subtraction version because we cannot use a double
counting argument."]
theorem card_div_le (hA : A.Nonempty) (B : Finset α) :
    ((B / B).card) ≤ ((A * B).card / A.card : ℚ≥0) ^ 2 * A.card := by
  simpa using card_pow_div_pow_le hA B 1 1

/-- The **Plünnecke-Ruzsa inequality**. Multiplication version. Note that this is genuinely harder
than the division version because we cannot use a double counting argument. -/
@[to_additive "The **Plünnecke-Ruzsa inequality**. Addition version. Note that this is genuinely
harder than the subtraction version because we cannot use a double counting argument."]
theorem card_div_le' (hA : A.Nonempty) (B : Finset α) :
    ((B / B).card) ≤ ((A * B).card / A.card : ℝ) ^ 2 * A.card := by
  sorry

end Finset
