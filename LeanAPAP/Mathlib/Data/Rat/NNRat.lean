import Mathlib.Data.Rat.NNRat

attribute [simp] Int.natAbs_pos
attribute [-simp] NNRat.natAbs_num_coe -- Tagging that lemma wasn't such a great idea

open scoped NNRat

namespace Rat

-- TODO: Add `no_index` to `Rat.ofNat_num`/`Rat.ofNat_den`
-- See note [no_index around OfNat.ofNat]
@[simp] lemma num_ofNat (n : ℕ) : num (no_index (OfNat.ofNat n)) = OfNat.ofNat n := rfl
@[simp] lemma den_ofNat (n : ℕ) : den (no_index (OfNat.ofNat n)) = 1 := rfl

end Rat

namespace NNRat
variable {q : ℚ≥0}

attribute [pp_dot] num den

instance {n : ℕ} : OfNat ℚ≥0 n := ⟨n⟩

@[simp] lemma num_ne_zero : q.num ≠ 0 ↔ q ≠ 0 := by simp [num]
@[simp] lemma num_pos : 0 < q.num ↔ 0 < q := by simp [pos_iff_ne_zero]
@[simp] lemma den_pos (q : ℚ≥0) : 0 < q.den := Rat.den_pos _

-- TODO: Rename `Rat.coe_nat_num`, `Rat.intCast_den`, `Rat.ofNat_num`, `Rat.ofNat_den`
@[simp, norm_cast] lemma num_natCast (n : ℕ) : num n = n := rfl
@[simp, norm_cast] lemma den_natCast (n : ℕ) : den n = 1 := rfl

-- See note [no_index around OfNat.ofNat]
@[simp] lemma num_ofNat (n : ℕ) : num (no_index (OfNat.ofNat n)) = OfNat.ofNat n := rfl
@[simp] lemma den_ofNat (n : ℕ) : den (no_index (OfNat.ofNat n)) = 1 := rfl

@[simp, norm_cast] lemma num_coe (q : ℚ≥0) : (q : ℚ).num = q.num := by
  simp [num, abs_of_nonneg, Rat.num_nonneg_iff_zero_le.2 q.2]

end NNRat

namespace Mathlib.Meta.Positivity
open Lean Meta Qq NNRat

private alias ⟨_, num_pos_of_pos⟩ := num_pos
private alias ⟨_, num_ne_zero_of_ne_zero⟩ := num_ne_zero

/-- The `positivity` extension which identifies expressions of the form `NNRat.num q`,
such that `positivity` successfully recognises `q`. -/
@[positivity NNRat.num _]
def evalNNRatnum : PositivityExt where eval {u α} _ _ e := do
  if let 0 := u then -- lean4#3060 means we can't combine this with the match below
    match α, e with
    | ~q(ℕ), ~q(NNRat.num $a) =>
      let pα : Q(PartialOrder ℚ≥0) := q(inferInstance)
      assumeInstancesCommute
      match ← core (q(inferInstance)) pα a with
      | .positive pa => return .positive q(num_pos_of_pos $pa)
      | .nonzero pa => return .nonzero q(num_ne_zero_of_ne_zero $pa)
      | _ => return .none
    | _, _ => throwError "not NNRat.num"
  else throwError "not NNRat.num"

/-- The `positivity` extension which identifies expressions of the form `Rat.den a`. -/
@[positivity NNRat.den _]
def evalNNRatden : PositivityExt where eval {u α} _ _ e := do
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
