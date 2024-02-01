import Mathlib.Algebra.Function.Support
import Mathlib.Algebra.Module.Basic

namespace Function
variable {α R M : Type*} {n : ℕ}

lemma support_smul' [Zero R] [Zero M] [SMulWithZero R M] [NoZeroSMulDivisors R M]
    {a : R} (ha : a ≠ 0) (g : α → M) : support (a • g) = support g :=
  Set.ext fun _ ↦ smul_ne_zero_iff_right ha

end Function
