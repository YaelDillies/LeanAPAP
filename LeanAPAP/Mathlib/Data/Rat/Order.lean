import Mathlib.Data.Rat.Order
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.NormNum.Basic

namespace Rat
variable {q : ℚ}

@[simp] alias num_nonneg := num_nonneg_iff_zero_le
@[simp] alias num_pos := num_pos_iff_pos

end Rat

open Rat

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function

private alias ⟨_, num_pos_of_pos⟩ := num_pos
private alias ⟨_, num_nonneg_of_nonneg⟩ := num_nonneg
private alias ⟨_, num_ne_zero_of_ne_zero⟩ := num_ne_zero

/-- The `positivity` extension which identifies expressions of the form `Rat.num a`,
such that `positivity` successfully recognises `a`. -/
@[positivity Rat.num _]
def evalRatnum : PositivityExt where eval {u α} _ _ e := do
  if let 0 := u then -- lean4#3060 means we can't combine this with the match below
    match α, e with
    | ~q(ℤ), ~q(Rat.num $a) =>
      let pα : Q(PartialOrder ℚ) := q(inferInstance)
      assumeInstancesCommute
      match ← core (q(inferInstance)) pα a with
      | .positive pa => return .positive q(num_pos_of_pos $pa)
      | .nonnegative pa => return .nonnegative q(num_nonneg_of_nonneg $pa)
      | .nonzero pa => return .nonzero q(num_ne_zero_of_ne_zero $pa)
      | .none => return .none
    | _, _ => throwError "not Rat.num"
  else throwError "not Rat.num"

/-- The `positivity` extension which identifies expressions of the form `Rat.den a`. -/
@[positivity Rat.den _]
def evalRatden : PositivityExt where eval {u α} _ _ e := do
  if let 0 := u then -- lean4#3060 means we can't combine this with the match below
    match α, e with
    | ~q(ℕ), ~q(Rat.den $a) =>
      assumeInstancesCommute
      return .positive q(den_pos $a)
    | _, _ => throwError "not Rat.num"
  else throwError "not Rat.num"

variable {q : ℚ}

example (hq : 0 < q) : 0 < q.num := by positivity
example (hq : 0 ≤ q) : 0 ≤ q.num := by positivity
example (hq : q ≠ 0) : q.num ≠ 0 := by positivity
example : 0 < q.den := by positivity

end Mathlib.Meta.Positivity
