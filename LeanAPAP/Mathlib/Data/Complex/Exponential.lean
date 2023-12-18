import Mathlib.Data.Complex.Exponential

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
