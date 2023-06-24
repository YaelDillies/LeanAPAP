import analysis.special_functions.log.basic

namespace real
variables {x y : ℝ}

lemma log_le_log_of_le (hx : 0 < x) (hxy : x ≤ y) : log x ≤ log y :=
(log_le_log hx (hx.trans_le hxy)).2 hxy

end real
