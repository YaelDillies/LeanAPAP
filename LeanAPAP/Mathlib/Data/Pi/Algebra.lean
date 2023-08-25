import Mathbin.Data.Pi.Algebra

#align_import mathlib.data.pi.algebra

/-!
### TODO

Replace the `pi.const_...` lemmas.
-/


variable {α β : Type _}

namespace Function

@[to_additive]
theorem const_hMul [Mul β] (a b : β) : const α (a * b) = const α a * const α b :=
  rfl

end Function

