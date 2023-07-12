import data.rat.order
import tactic.positivity

namespace rat
variables {q : ℚ}

@[simp] lemma num_eq_zero : q.num = 0 ↔ q = 0 := zero_iff_num_zero.symm
lemma num_ne_zero : q.num ≠ 0 ↔ q ≠ 0 := num_eq_zero.not

alias num_nonneg_iff_zero_le ← num_nonneg
alias num_pos_iff_pos ← num_pos

@[simp] lemma denom_pos (q : ℚ) : 0 < q.denom := pos_iff_ne_zero.2 q.denom_ne_zero

end rat

open rat

namespace tactic
open positivity

private alias num_pos ↔ _ num_pos_of_pos
private alias num_nonneg ↔ _ num_nonneg_of_nonneg
private alias num_ne_zero ↔ _ num_ne_zero_of_ne_zero

/-- Extension for the `positivity` tactic: `int.floor` is nonnegative if its input is. -/
@[positivity]
meta def positivity_num_denom : expr → tactic strictness
| `(rat.num %%a) := do
      strictness_a ← core a,
      match strictness_a with
      | positive p := positive <$> mk_app ``num_pos_of_pos [p]
      | nonnegative p := nonnegative <$> mk_app ``num_nonneg_of_nonneg [p]
      | nonzero p := nonzero <$> mk_mapp ``num_ne_zero_of_ne_zero [none, p]
      end
| `(rat.denom %%a) := positive <$> mk_app ``denom_pos [a]
| e := pp e >>= fail ∘ format.bracket "The expression `"
    "` is not of the form `rat.num q` or `rat.denom q`"

variables {q : ℚ}

example (hq : 0 < q) : 0 < q.num := by positivity
example (hq : 0 ≤ q) : 0 ≤ q.num := by positivity
example (hq : q ≠ 0) : q.num ≠ 0 := by positivity
example : 0 < q.denom := by positivity

end tactic
