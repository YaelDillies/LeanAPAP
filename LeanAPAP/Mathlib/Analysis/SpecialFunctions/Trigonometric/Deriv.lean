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
def evalSinh : PositivityExt where eval zα pα e := do
  let (.app f (a : Q(ℝ))) ← withReducible (whnf e) | throwError "not Real.sinh"
  guard <|← withDefault <| withNewMCtxDepth <| isDefEq f q(Real.sinh)
  let ra ← core zα pα a
  match ra with
  | .positive pa =>
      have pa' : Q(0 < $a) := pa
      return .positive (q(sinh_pos_of_pos $pa') : Expr)
  | .nonnegative pa =>
      have pa' : Q(0 ≤ $a) := pa
      return .nonnegative (q(sinh_nonneg_of_nonneg $pa') : Expr)
  | .nonzero pa =>
      have pa' : Q($a ≠ 0) := pa
      return .nonzero (q(sinh_ne_zero_of_ne_zero $pa') : Expr)
  | _ => return .none

example (x : ℝ) (hx : 0 < x) : 0 < x.sinh := by positivity
example (x : ℝ) (hx : 0 ≤ x) : 0 ≤ x.sinh := by positivity
example (x : ℝ) (hx : x ≠ 0) : x.sinh ≠ 0 := by positivity

end Mathlib.Meta.Positivity
