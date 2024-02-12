import Mathlib.Data.NNRat.Defs
import Mathlib.Tactic.Positivity.Core

namespace Mathlib.Meta.Positivity
open Lean Meta Qq NNRat

private alias ⟨_, num_pos_of_pos⟩ := num_pos
private alias ⟨_, num_ne_zero_of_ne_zero⟩ := num_ne_zero

/-- The `positivity` extension which identifies expressions of the form `NNRat.num q`,
such that `positivity` successfully recognises `q`. -/
@[positivity NNRat.num _]
def evalNNRatNum : PositivityExt where eval {u α} _ _ e := do
  if let 0 := u then -- lean4#3060 means we can't combine this with the match below
    match α, e with
    | ~q(ℕ), ~q(NNRat.num $a) =>
      let zα : Q(Zero ℚ≥0) := q(inferInstance)
      let pα : Q(PartialOrder ℚ≥0) := q(inferInstance)
      assumeInstancesCommute
      match ← core zα pα a with
      | .positive pa => return .positive q(num_pos_of_pos $pa)
      | .nonzero pa => return .nonzero q(num_ne_zero_of_ne_zero $pa)
      | _ => return .none
    | _, _ => throwError "not NNRat.num"
  else throwError "not NNRat.num"

/-- The `positivity` extension which identifies expressions of the form `Rat.den a`. -/
@[positivity NNRat.den _]
def evalNNRatDen : PositivityExt where eval {u α} _ _ e := do
  if let 0 := u then -- lean4#3060 means we can't combine this with the match below
    match α, e with
    | ~q(ℕ), ~q(NNRat.den $a) =>
      assumeInstancesCommute
      return .positive q(den_pos $a)
    | _, _ => throwError "not NNRat.num"
  else throwError "not NNRat.num"

variable {q : ℚ≥0}

example (hq : 0 < q) : 0 < q.num := by positivity
example (hq : q ≠ 0) : q.num ≠ 0 := by positivity
example : 0 < q.den := by positivity

end Mathlib.Meta.Positivity
