import Mathlib.Algebra.Support

namespace Function
variable {α R M : Type*} {n : ℕ}

@[simp] lemma support_mul' [MulZeroClass R] [NoZeroDivisors R] (f g : α → R) :
    support (f * g) = support f ∩ support g :=
  support_mul f g

@[simp] lemma support_pow [MonoidWithZero M] [NoZeroDivisors M] (f : α → M) (hn : n ≠ 0) :
    support (f ^ n) = support f := by ext; exact (pow_eq_zero_iff hn.bot_lt).not

end Function
