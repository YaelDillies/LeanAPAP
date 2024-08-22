import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import LeanAPAP.Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# TODO

Turn `ENNReal.coe_rpow_of_nonneg` and `ENNReal.coe_rpow_of_ne_zero` around
-/

namespace ENNReal

-- TODO: Replace `toNNReal_rpow`
@[simp] lemma toNNReal_rpow' (x : ℝ≥0∞) (z : ℝ) : (x ^ z).toNNReal = x.toNNReal ^ z :=
  (toNNReal_rpow ..).symm

end ENNReal

namespace NNReal
variable {x : ℝ≥0} {y : ℝ}

lemma rpow_eq_zero (hy : y ≠ 0) : x ^ y = 0 ↔ x = 0 := by simp [hy]

lemma rpow_natCast_mul (x : ℝ≥0) (n : ℕ) (z : ℝ) : x ^ (n * z) = (x ^ n) ^ z := by
  rw [rpow_mul, rpow_natCast]

lemma rpow_mul_natCast (x : ℝ≥0) (y : ℝ) (n : ℕ) : x ^ (y * n) = (x ^ y) ^ n := by
  rw [rpow_mul, rpow_natCast]

lemma rpow_intCast_mul (x : ℝ≥0) (n : ℤ) (z : ℝ) : x ^ (n * z) = (x ^ n) ^ z := by
  rw [rpow_mul, rpow_intCast]

lemma rpow_mul_intCast (x : ℝ≥0) (y : ℝ) (n : ℤ) : x ^ (y * n) = (x ^ y) ^ n := by
  rw [rpow_mul, rpow_intCast]

lemma rpow_add_intCast (hx : x ≠ 0) (y : ℝ) (n : ℤ) : x ^ (y + n) = x ^ y * x ^ n := by
  ext; exact Real.rpow_add_intCast (mod_cast hx) _ _

lemma rpow_add_natCast (hx : x ≠ 0) (y : ℝ) (n : ℕ) : x ^ (y + n) = x ^ y * x ^ n := by
  ext; exact Real.rpow_add_natCast (mod_cast hx) _ _

lemma rpow_sub_intCast (hx : x ≠ 0) (y : ℝ) (n : ℕ) : x ^ (y - n) = x ^ y / x ^ n := by
  ext; exact Real.rpow_sub_intCast (mod_cast hx) _ _

lemma rpow_sub_natCast (hx : x ≠ 0) (y : ℝ) (n : ℕ) : x ^ (y - n) = x ^ y / x ^ n := by
  ext; exact Real.rpow_sub_natCast (mod_cast hx) _ _

lemma rpow_add_intCast' {n : ℤ} (h : y + n ≠ 0) (x : ℝ≥0) : x ^ (y + n) = x ^ y * x ^ n := by
  ext; exact Real.rpow_add_intCast' (mod_cast x.2) h

lemma rpow_add_natCast' {n : ℕ} (h : y + n ≠ 0) (x : ℝ≥0) : x ^ (y + n) = x ^ y * x ^ n := by
  ext; exact Real.rpow_add_natCast' (mod_cast x.2) h

lemma rpow_sub_intCast' {n : ℤ} (h : y - n ≠ 0) (x : ℝ≥0) : x ^ (y - n) = x ^ y / x ^ n := by
  ext; exact Real.rpow_sub_intCast' (mod_cast x.2) h

lemma rpow_sub_natCast' {n : ℕ} (h : y - n ≠ 0) (x : ℝ≥0) : x ^ (y - n) = x ^ y / x ^ n := by
  ext; exact Real.rpow_sub_natCast' (mod_cast x.2) h

lemma rpow_add_one (hx : x ≠ 0) (y : ℝ) : x ^ (y + 1) = x ^ y * x := by
  simpa using rpow_add_natCast hx y 1

lemma rpow_sub_one (hx : x ≠ 0) (y : ℝ) : x ^ (y - 1) = x ^ y / x := by
  simpa using rpow_sub_natCast hx y 1

-- TODO: Swap argument order to `rpow_add'`/`rpow_sub'`
lemma rpow_add_one' (h : y + 1 ≠ 0) (x : ℝ≥0) : x ^ (y + 1) = x ^ y * x := by
  rw [rpow_add' x h, rpow_one]

lemma rpow_one_add' (h : 1 + y ≠ 0) (x : ℝ≥0) : x ^ (1 + y) = x * x ^ y := by
  rw [rpow_add' x h, rpow_one]

lemma rpow_sub_one' (h : y - 1 ≠ 0) (x : ℝ≥0) : x ^ (y - 1) = x ^ y / x := by
  rw [rpow_sub' x h, rpow_one]

lemma rpow_one_sub' (h : 1 - y ≠ 0) (x : ℝ≥0) : x ^ (1 - y) = x / x ^ y := by
  rw [rpow_sub' x h, rpow_one]

variable {x y : ℝ≥0} {z : ℝ}

lemma rpow_lt_rpow_of_neg (hx : 0 < x) (hxy : x < y) (hz : z < 0) : y ^ z < x ^ z :=
  Real.rpow_lt_rpow_of_neg hx hxy hz

lemma rpow_le_rpow_of_nonpos (hx : 0 < x) (hxy : x ≤ y) (hz : z ≤ 0) : y ^ z ≤ x ^ z :=
  Real.rpow_le_rpow_of_nonpos hx hxy hz

lemma rpow_lt_rpow_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z < y ^ z ↔ y < x :=
  Real.rpow_lt_rpow_iff_of_neg hx hy hz

lemma rpow_le_rpow_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z ≤ y ^ z ↔ y ≤ x :=
  Real.rpow_le_rpow_iff_of_neg hx hy hz

lemma le_rpow_inv_iff_of_pos (hy : 0 ≤ y) (hz : 0 < z) (x : ℝ≥0) : x ≤ y ^ z⁻¹ ↔ x ^ z ≤ y :=
  Real.le_rpow_inv_iff_of_pos x.2 hy hz

lemma rpow_inv_le_iff_of_pos (hy : 0 ≤ y) (hz : 0 < z) (x : ℝ≥0) : x ^ z⁻¹ ≤ y ↔ x ≤ y ^ z :=
  Real.rpow_inv_le_iff_of_pos x.2 hy hz

lemma lt_rpow_inv_iff_of_pos (hy : 0 ≤ y) (hz : 0 < z) (x : ℝ≥0) : x < y ^ z⁻¹ ↔ x ^ z < y :=
  Real.lt_rpow_inv_iff_of_pos x.2 hy hz

lemma rpow_inv_lt_iff_of_pos (hy : 0 ≤ y) (hz : 0 < z) (x : ℝ≥0) : x ^ z⁻¹ < y ↔ x < y ^ z :=
  Real.rpow_inv_lt_iff_of_pos x.2 hy hz

lemma le_rpow_inv_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ≤ y ^ z⁻¹ ↔ y ≤ x ^ z :=
  Real.le_rpow_inv_iff_of_neg hx hy hz

lemma lt_rpow_inv_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x < y ^ z⁻¹ ↔ y < x ^ z :=
  Real.lt_rpow_inv_iff_of_neg hx hy hz

lemma rpow_inv_lt_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z⁻¹ < y ↔ y ^ z < x :=
  Real.rpow_inv_lt_iff_of_neg hx hy hz

lemma rpow_inv_le_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z⁻¹ ≤ y ↔ y ^ z ≤ x :=
  Real.rpow_inv_le_iff_of_neg hx hy hz

end NNReal
