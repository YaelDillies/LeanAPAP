import Mathlib.Data.Complex.Exponential

/-!
### TODO

Make `add_one_le_exp_of_nonneg` private
-/

open Finset
open scoped BigOperators Nat

namespace Real
variable {x : ℝ}

--TODO: Fix name in mathlib
alias add_one_lt_exp := add_one_lt_exp_of_nonzero

--TODO: Replace `one_sub_le_exp_minus_of_nonneg`
lemma one_sub_le_exp_neg (x : ℝ) : 1 - x ≤ exp (-x) :=
  (sub_eq_neg_add _ _).trans_le $ add_one_le_exp _

lemma one_sub_lt_exp_neg (hx : x ≠ 0) : 1 - x < exp (-x) :=
  (sub_eq_neg_add _ _).trans_lt $ add_one_lt_exp $ neg_ne_zero.2 hx

lemma exp_nonneg (x : ℝ) : 0 ≤ exp x := x.exp_pos.le

lemma exp_abs_le (x : ℝ) : exp |x| ≤ exp x + exp (-x) := by
  cases le_total x 0 <;> simp [abs_of_nonpos, abs_of_nonneg, exp_nonneg, *]

lemma pow_div_factorial_le_exp (hx : 0 ≤ x) (n : ℕ) : x ^ n / n ! ≤ exp x :=
  calc
    x ^ n / n ! ≤ ∑ k in range (n + 1), x ^ k / k !
      := single_le_sum (f := fun k ↦ x ^ k / k !) (fun k _ ↦ by positivity) (self_mem_range_succ n)
    _ ≤ exp x := sum_le_exp_of_nonneg hx _

end Real

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

/-- Extension for the `positivity` tactic: `Real.cosh` is always positive. -/
@[positivity Real.cosh _]
def evalCosh : PositivityExt where eval {u α} _ _ e := do
  if let 0 := u then -- lean4#3060 means we can't combine this with the match below
    match α, e with
    | ~q(ℝ), ~q(Real.cosh $a) =>
      assumeInstancesCommute
      return .positive q(Real.cosh_pos $a)
    | _, _ => throwError "not Real.cosh"
  else throwError "not Real.cosh"

example (x : ℝ) : 0 < x.cosh := by positivity

end Mathlib.Meta.Positivity
