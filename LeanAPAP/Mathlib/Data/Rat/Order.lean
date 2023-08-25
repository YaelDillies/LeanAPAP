import Mathlib.Data.Rat.Order
import Mathlib.Tactic.Positivity

#align_import mathlib.data.rat.order

namespace Rat
variable {q : ℚ}

#print Rat.num_eq_zero /-
@[simp]
lemma num_eq_zero : q.num = 0 ↔ q = 0 :=
  zero_iff_num_zero.symm
-/

lemma num_ne_zero : q.num ≠ 0 ↔ q ≠ 0 :=
  num_eq_zero.Not

alias num_nonneg := num_nonneg_iff_zero_le

alias num_pos := num_pos_iff_pos

#print Rat.den_pos /-
@[simp]
lemma den_pos (q : ℚ) : 0 < q.den :=
  pos_iff_ne_zero.2 q.den_nz
-/

end Rat

open Rat

namespace Tactic
open Positivity

/- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:87:10: unsupported modifiers in user command -/
alias ⟨_, num_pos_of_pos⟩ := num_pos

/- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:87:10: unsupported modifiers in user command -/
alias ⟨_, num_nonneg_of_nonneg⟩ := num_nonneg

/- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:87:10: unsupported modifiers in user command -/
alias ⟨_, num_ne_zero_of_ne_zero⟩ := num_ne_zero

/-- Extension for the `positivity` tactic: `int.floor` is nonnegative if its input is. -/
@[positivity]
unsafe def positivity_num_denom : expr → tactic strictness
  | q(Rat.num $(a)) => do
    let strictness_a ← core a
    match strictness_a with
      | positive p => positive <$> mk_app `` num_pos_of_pos [p]
      | nonnegative p => nonnegative <$> mk_app `` num_nonneg_of_nonneg [p]
      | nonzero p => nonzero <$> mk_mapp `` num_ne_zero_of_ne_zero [none, p]
  | q(Rat.den $(a)) => positive <$> mk_app `` denom_pos [a]
  | e =>
    pp e >>=
      fail ∘ format.bracket "The expression `" "` is not of the form `rat.num q` or `rat.denom q`"

variable {q : ℚ}

example (hq : 0 < q) : 0 < q.num := by positivity

example (hq : 0 ≤ q) : 0 ≤ q.num := by positivity

example (hq : q ≠ 0) : q.num ≠ 0 := by positivity

example : 0 < q.den := by positivity

end Tactic
