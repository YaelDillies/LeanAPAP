import Mathlib.Data.ENNReal.Basic

namespace ENNReal

@[simp] lemma ofNat_pos {n : ℕ} [n.AtLeastTwo] : 0 < (no_index OfNat.ofNat n : ℝ≥0∞) :=
  Nat.cast_pos.2 Fin.size_pos'

end ENNReal

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function ENNReal

private lemma ennreal_one_pos : (0 : ℝ≥0∞) < 1 := zero_lt_one

/-- The `positivity` extension which identifies expressions of the form `‖f‖_[p]`. -/
@[positivity OfNat.ofNat _] def evalOfNatENNReal : PositivityExt where eval {u} α _z _p e := do
  match u, α, e with
  | 0, ~q(ℝ≥0∞), ~q(@OfNat.ofNat _ $n $instn) =>
    try
      let instn ← synthInstanceQ q(Nat.AtLeastTwo $n)
      return Strictness.positive (q(@ofNat_pos $n $instn) : Expr)
    catch _ => do
      match n with
      | ~q(1) => return .positive (q(ennreal_one_pos) : Expr)
      | _ => throwError "not positive"
  | _ => throwError "not `ENNReal`-valued `ofNat`"

end Mathlib.Meta.Positivity

open scoped ENNReal

example : (0 : ℝ≥0∞) < 1 := by positivity
