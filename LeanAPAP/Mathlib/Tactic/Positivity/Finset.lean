import Mathlib.Tactic.Positivity.Finset
import LeanAPAP.Prereqs.Density

namespace Mathlib.Meta.Positivity
open Qq Lean Meta Finset

/-- Extension for `Finset.dens`. `s.card` is positive if `s` is nonempty.
It calls `Mathlib.Meta.proveFinsetNonempty` to attempt proving that the finset is nonempty. -/
@[positivity Finset.dens _]
def evalFinsetDens : PositivityExt where eval {u 𝕜} _ _ e := do
  match u, 𝕜, e with
  | 0, ~q(ℚ≥0), ~q(@Finset.dens $α $instα $s) =>
    let some ps ← proveFinsetNonempty s | return .none
    assumeInstancesCommute
    return .positive q(@Nonempty.dens_pos $α $instα $s $ps)
  | _, _, _ => throwError "not Finset.dens"

variable {α : Type*} {s : Finset α}

example : 0 ≤ s.card := by positivity
example (hs : s.Nonempty) : 0 < s.card := by positivity

variable [Fintype α]

example : 0 ≤ Fintype.card α := by positivity
example : 0 ≤ dens s := by positivity
example (hs : s.Nonempty) : 0 < dens s := by positivity
example (hs : s.Nonempty) : dens s ≠ 0 := by positivity
example [Nonempty α] : 0 < (univ : Finset α).card := by positivity
example [Nonempty α] : 0 < Fintype.card α := by positivity
example [Nonempty α] : 0 < dens (univ : Finset α) := by positivity
example [Nonempty α] : dens (univ : Finset α) ≠ 0 := by positivity

end Mathlib.Meta.Positivity
