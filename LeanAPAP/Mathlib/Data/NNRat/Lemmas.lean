import Mathlib.Data.NNRat.Lemmas

namespace NNRat

lemma mul_den_eq_num (q : ℚ≥0) : q * q.den = q.num := by
  rw [← eq_div_iff (Nat.cast_ne_zero.2 q.den_pos.ne'), num_div_den]

lemma den_mul_eq_num (q : ℚ≥0) : q.den * q = q.num := by
  rw [mul_comm, ← eq_div_iff (Nat.cast_ne_zero.2 q.den_pos.ne'), num_div_den]

end NNRat
