import Mathlib.Data.Complex.Order

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Complex
open scoped ComplexOrder

private alias ⟨_, ofReal_pos⟩ := zero_lt_real
private alias ⟨_, ofReal_nonneg⟩ := zero_le_real
private alias ⟨_, ofReal_ne_zero_of_ne_zero⟩ := ofReal_ne_zero

/-- Extension for the `positivity` tactic: `Complex.ofReal` is positive/nonnegative/nonzero if its
input is. -/
@[positivity Complex.ofReal' _]
def evalComplexOfReal : PositivityExt where eval {u α} _ _ e := do
  let zα : Q(Zero ℝ) := q(inferInstance)
  let pα : Q(PartialOrder ℝ) := q(inferInstance)
  if let 0 := u then -- lean4#3060 means we can't combine this with the match below
    match α, e with
    | ~q(ℂ), ~q(Complex.ofReal' $a) =>
      assumeInstancesCommute
      match ← core zα pα a with
      | .positive pa => return .positive q(ofReal_pos $pa)
      | .nonnegative pa => return .nonnegative q(ofReal_nonneg $pa)
      | .nonzero pa => return .nonzero q(ofReal_ne_zero_of_ne_zero $pa)
      | _ => return .none
    | _, _ => throwError "not Complex.ofReal'"
  else throwError "not Complex.ofReal'"

example (x : ℝ) (hx : 0 < x) : 0 < (x : ℂ) := by positivity
example (x : ℝ) (hx : 0 ≤ x) : 0 ≤ (x : ℂ) := by positivity
example (x : ℝ) (hx : x ≠ 0) : (x : ℂ) ≠ 0 := by positivity

end Mathlib.Meta.Positivity
