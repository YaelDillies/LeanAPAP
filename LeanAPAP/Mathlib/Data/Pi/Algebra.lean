import Mathlib.Data.Pi.Algebra

#align_import mathlib.data.pi.algebra

/-!
### TODO

Replace the `pi.const_...` lemmas.
-/

variable {α β : Type*}

namespace Function

@[to_additive]
lemma const_mul [Mul β] (a b : β) : const α (a * b) = const α a * const α b := rfl

end Function
