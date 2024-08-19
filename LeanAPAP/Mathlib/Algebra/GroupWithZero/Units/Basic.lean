import Mathlib.Algebra.GroupWithZero.Units.Basic

variable {G₀ : Type*} [GroupWithZero G₀] {a : G₀}

lemma zpow_natCast_sub_natCast₀ (ha : a ≠ 0) (m n : ℕ) : a ^ (m - n : ℤ) = a ^ m / a ^ n := by
  rw [zpow_sub₀ ha, zpow_natCast, zpow_natCast]

lemma zpow_natCast_sub_one₀ (ha : a ≠ 0) (n : ℕ) : a ^ (n - 1 : ℤ) = a ^ n / a := by
  simpa using zpow_natCast_sub_natCast₀ ha n 1

lemma zpow_one_sub_natCast₀ (ha : a ≠ 0) (n : ℕ) : a ^ (1 - n : ℤ) = a / a ^ n := by
  simpa using zpow_natCast_sub_natCast₀ ha 1 n
