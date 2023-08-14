import data.pi.algebra

/-!
### TODO

Replace the `pi.const_...` lemmas.
-/

variables {α β : Type*}

namespace function

@[to_additive] lemma const_mul [has_mul β] (a b : β) :
  const α (a * b) = const α a * const α b := rfl

end function
