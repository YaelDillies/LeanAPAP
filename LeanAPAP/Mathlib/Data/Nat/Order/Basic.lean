import Mathbin.Data.Nat.Order.Basic

#align_import mathlib.data.nat.order.basic

variable {α : Type _} [Monoid α] {n : ℕ}

@[to_additive]
theorem hMul_pow_sub_one (hn : n ≠ 0) (a : α) : a * a ^ (n - 1) = a ^ n := by
  rw [← pow_succ, tsub_add_cancel_of_le (Nat.succ_le_iff.2 <| pos_iff_ne_zero.2 hn)]

@[to_additive]
theorem pow_sub_one_hMul (hn : n ≠ 0) (a : α) : a ^ (n - 1) * a = a ^ n := by
  rw [← pow_succ', tsub_add_cancel_of_le (Nat.succ_le_iff.2 <| pos_iff_ne_zero.2 hn)]

