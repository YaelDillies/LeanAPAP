import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace Real
variable {x : ℝ}

@[simp] lemma sinh_eq_zero : sinh x = 0 ↔ x = 0 := by rw [← @sinh_inj x, sinh_zero]

lemma sinh_ne_zero : sinh x ≠ 0 ↔ x ≠ 0 := sinh_eq_zero.not

end Real

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

private alias ⟨_, sinh_pos_of_pos⟩ := Real.sinh_pos_iff
private alias ⟨_, sinh_nonneg_of_nonneg⟩ := Real.sinh_nonneg_iff
private alias ⟨_, sinh_ne_zero_of_ne_zero⟩ := Real.sinh_ne_zero

/-- Extension for the `positivity` tactic: `Real.sinh` is positive/nonnegative/nonzero if its input
is. -/
@[positivity Real.sinh _]
def evalSinh : PositivityExt where eval {u α} _ _ e := do
  let zα : Q(Zero ℝ) := q(inferInstance)
  let pα : Q(PartialOrder ℝ) := q(inferInstance)
  if let 0 := u then -- lean4#3060 means we can't combine this with the match below
    match α, e with
    | ~q(ℝ), ~q(Real.sinh $a) =>
      assumeInstancesCommute
      match ← core zα pα a with
      | .positive pa => return .positive q(sinh_pos_of_pos $pa)
      | .nonnegative pa => return .nonnegative q(sinh_nonneg_of_nonneg $pa)
      | .nonzero pa => return .nonzero q(sinh_ne_zero_of_ne_zero $pa)
      | _ => return .none
    | _, _ => throwError "not Real.sinh"
  else throwError "not Real.sinh"

example (x : ℝ) (hx : 0 < x) : 0 < x.sinh := by positivity
example (x : ℝ) (hx : 0 ≤ x) : 0 ≤ x.sinh := by positivity
example (x : ℝ) (hx : x ≠ 0) : x.sinh ≠ 0 := by positivity

end Mathlib.Meta.Positivity
