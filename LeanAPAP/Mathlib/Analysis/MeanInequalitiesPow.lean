import Mathlib.Analysis.MeanInequalitiesPow

/-!
## TODO

Generalise to (linearly) ordered semirings?
-/

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open Finset

namespace Real
variable {a b : ℝ}

lemma add_pow_le (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    (a + b) ^ n ≤ (2 : ℝ) ^ (n - 1) * (a ^ n + b ^ n) := by
  obtain _ | n := n
  · simp
  rw [Nat.succ_sub_one, ←div_le_iff' (by positivity)]
  simpa [one_add_one_eq_two]
    using @Real.pow_sum_div_card_le_sum_pow _ univ ![a, b] n (by simp [Fin.forall_fin_two, *])

end Real
