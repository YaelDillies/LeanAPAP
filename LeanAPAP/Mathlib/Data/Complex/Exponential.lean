import Mathlib.Data.Complex.Exponential

#align_import mathlib.data.complex.exponential

namespace Real
variable {x : ℝ}

--TODO: Fix name in mathlib
alias add_one_lt_exp := add_one_lt_exp_of_nonzero

--TODO: Replace `one_sub_le_exp_minus_of_nonneg`
lemma one_sub_le_exp_neg (x : ℝ) : 1 - x ≤ Real.exp (-x) :=
  (sub_eq_neg_add _ _).trans_le <| add_one_le_exp _

lemma one_sub_lt_exp_neg (hx : x ≠ 0) : 1 - x < Real.exp (-x) :=
  (sub_eq_neg_add _ _).trans_lt <| add_one_lt_exp <| neg_ne_zero.2 hx

end Real
