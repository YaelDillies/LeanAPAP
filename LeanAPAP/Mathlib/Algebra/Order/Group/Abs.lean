import Mathlib.Algebra.Order.Group.Abs

namespace Pi
variable {ι : Type*} {α : ι → Type*}

@[simp]
lemma abs_apply [∀ i, AddGroup (α i)] [∀ i, Sup (α i)] (f : ∀ i, α i) (i : ι) : |f| i = |f i| := rfl

lemma abs_def [∀ i, Neg (α i)] [∀ i, Sup (α i)] (f : ∀ i, α i) : |f| = fun i ↦ |f i| := rfl

end Pi
