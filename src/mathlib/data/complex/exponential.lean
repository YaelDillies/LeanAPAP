import data.complex.exponential

namespace real
variables {x : ℝ}

--TODO: Fix name in mathlib
alias add_one_lt_exp_of_nonzero ← add_one_lt_exp

--TODO: Replace `one_sub_le_exp_minus_of_nonneg`
lemma one_sub_le_exp_neg (x : ℝ) : 1 - x ≤ real.exp (-x) :=
(sub_eq_neg_add _ _).trans_le $ add_one_le_exp _

lemma one_sub_lt_exp_neg (hx : x ≠ 0) : 1 - x < real.exp (-x) :=
(sub_eq_neg_add _ _).trans_lt $ add_one_lt_exp $ neg_ne_zero.2 hx

end real
