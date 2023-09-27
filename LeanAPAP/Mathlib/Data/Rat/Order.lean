import Mathlib.Data.Rat.Order
import Mathlib.Tactic.Positivity

namespace Rat
variable {q : ℚ}

alias num_nonneg := num_nonneg_iff_zero_le
alias num_pos := num_pos_iff_pos

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
def evalRatnum : PositivityExt where eval _zα _pα (e : Q(ℤ)) := do
  let ~q(Rat.num $a) := e | throwError "not Rat.num"
  let zα' : Q(Zero ℚ) := q(inferInstance)
  let pα' : Q(PartialOrder ℚ) := q(inferInstance)
  -- TODO: what's the right way to write these `: Expr`s?
  match ← core zα' pα' a with
  | .positive pa =>
    return .positive (q(num_pos_of_pos $pa) : Expr)
  | .nonnegative pa =>
    return .nonnegative (q(num_nonneg_of_nonneg $pa) : Expr)
  | .nonzero pa =>
    return .nonzero (q(num_ne_zero_of_ne_zero $pa) : Expr)
  | .none =>
    return .none

/-- The `positivity` extension which identifies expressions of the form `Rat.den a`. -/
@[positivity Rat.den _]
def evalRatden : PositivityExt where eval _zα _pα (e : Q(ℕ)) := do
  let ~q(Rat.den $a) := e | throwError "not Rat.den"
  return .positive (q(den_pos $a) :)

variable {q : ℚ}

example (hq : 0 < q) : 0 < q.num := by positivity
example (hq : 0 ≤ q) : 0 ≤ q.num := by positivity
example (hq : q ≠ 0) : q.num ≠ 0 := by positivity
example : 0 < q.den := by positivity

end Mathlib.Meta.Positivity
