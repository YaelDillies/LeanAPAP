import Mathlib.Algebra.GroupPower.Order

variable {α : Type*}

section OrderedSemiring
variable [OrderedSemiring α] {a b : α} {n : ℕ}

lemma pow_add_pow_le' (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ n + b ^ n ≤ 2 * (a + b) ^ n := by
  rw [two_mul]
  exact
    add_le_add (pow_le_pow_of_le_left ha (le_add_of_nonneg_right hb) _)
      (pow_le_pow_of_le_left hb (le_add_of_nonneg_left ha) _)

end OrderedSemiring

section StrictOrderedSemiring
variable {α : Type*} [StrictOrderedSemiring α] {a b : α} {n : ℕ}

-- TODO: Fix the name mess around `pow_strictMono_left`, `pow_strictMono_right`,
-- ``pow_strictMono_right'`
lemma pow_strictMonoOn_left (hn : n ≠ 0) : StrictMonoOn (· ^ n : α → α) {a | 0 ≤ a} :=
  fun _a ha _b _ hab ↦ pow_lt_pow_of_lt_left hab ha hn.bot_lt

end StrictOrderedSemiring

section LinearOrderedSemiring
variable [LinearOrderedSemiring α] {a b : α} {n : ℕ}

lemma pow_eq_one_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : a ^ n = 1 ↔ a = 1 := by
  simp only [le_antisymm_iff, pow_le_one_iff_of_nonneg ha hn, one_le_pow_iff_of_nonneg ha hn]

lemma pow_le_pow_iff_left (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : n ≠ 0) : a ^ n ≤ b ^ n ↔ a ≤ b :=
  (pow_strictMonoOn_left hn).le_iff_le ha hb

lemma pow_lt_pow_iff_left (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : n ≠ 0) : a ^ n < b ^ n ↔ a < b :=
  (pow_strictMonoOn_left hn).lt_iff_lt ha hb

end LinearOrderedSemiring
