import analysis.special_functions.pow.real

namespace real
variables {x y z : ℝ}

@[simp] lemma rpow_rpow_inv (hx : 0 ≤ x) (hy : y ≠ 0) : (x ^ y) ^ (y⁻¹ : ℝ) = x :=
by rw [←rpow_mul hx, mul_inv_cancel hy, rpow_one]

@[simp] lemma rpow_inv_rpow (hx : 0 ≤ x) (hy : y ≠ 0) : (x ^ y⁻¹) ^ (y : ℝ) = x :=
by rw [←rpow_mul hx, inv_mul_cancel hy, rpow_one]

lemma rpow_add_int' (hx : 0 ≤ x) {n : ℤ} (h : y + n ≠ 0) : x ^ (y + n) = x ^ y * x ^ n :=
by rw [rpow_add' hx h, rpow_int_cast]

lemma rpow_add_nat' (hx : 0 ≤ x) {n : ℕ} (h : y + n ≠ 0) : x ^ (y + n) = x ^ y * x ^ n :=
by rw [rpow_add' hx h, rpow_nat_cast]

lemma rpow_sub_int' (hx : 0 ≤ x) {n : ℤ} (h : y - n ≠ 0) : x ^ (y - n) = x ^ y / x ^ n :=
by rw [rpow_sub' hx h, rpow_int_cast]

lemma rpow_sub_nat' (hx : 0 ≤ x) {n : ℕ} (h : y - n ≠ 0) : x ^ (y - n) = x ^ y / x ^ n :=
by rw [rpow_sub' hx h, rpow_nat_cast]

lemma rpow_add_one' (hx : 0 ≤ x) (h : y + 1 ≠ 0) : x ^ (y + 1) = x ^ y * x :=
by rw [rpow_add' hx h, rpow_one]

lemma rpow_one_add' (hx : 0 ≤ x) (h : 1 + y ≠ 0) : x ^ (1 + y) = x * x ^ y :=
by rw [rpow_add' hx h, rpow_one]

lemma rpow_sub_one' (hx : 0 ≤ x) (h : y - 1 ≠ 0) : x ^ (y - 1) = x ^ y / x :=
by rw [rpow_sub' hx h, rpow_one]

lemma rpow_one_sub' (hx : 0 ≤ x) (h : 1 - y ≠ 0) : x ^ (1 - y) = x / x ^ y :=
by rw [rpow_sub' hx h, rpow_one]

lemma le_rpow_inv_iff_of_pos (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) : x ≤ y ^ z⁻¹ ↔ x ^ z ≤ y :=
by rw [←rpow_le_rpow_iff hx _ hz, ←rpow_mul hy, inv_mul_cancel hz.ne', rpow_one]; positivity

lemma rpow_inv_le_iff_of_pos (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) : x ^ z⁻¹ ≤ y ↔ x ≤ y ^ z :=
by rw [←rpow_le_rpow_iff _ hy hz, ←rpow_mul hx, inv_mul_cancel hz.ne', rpow_one]; positivity

lemma lt_rpow_inv_iff_of_pos (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) : x < y ^ z⁻¹ ↔ x ^ z < y :=
lt_iff_lt_of_le_iff_le $ rpow_inv_le_iff_of_pos hy hx hz

lemma rpow_inv_lt_iff_of_pos (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 < z) : x ^ z⁻¹ < y ↔ x < y ^ z :=
lt_iff_lt_of_le_iff_le $ le_rpow_inv_iff_of_pos hy hx hz

end real
