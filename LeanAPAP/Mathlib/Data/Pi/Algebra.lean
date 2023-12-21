import Mathlib.Data.Pi.Algebra

/-!
### TODO

Replace the `Pi.const_...` lemmas.
-/

variable {α β : Type*}

namespace Function

@[to_additive] lemma const_mul [Mul β] (a b : β) : const α (a * b) = const α a * const α b := rfl
@[to_additive] lemma const_div [Div β] (a b : β) : const α (a / b) = const α a / const α b := rfl
@[to_additive const_neg'] lemma const_inv [Inv β] (a : β) : const α a⁻¹ = (const α a)⁻¹ := rfl

end Function

