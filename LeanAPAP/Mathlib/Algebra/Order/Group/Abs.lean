import Mathlib.Algebra.Group.Pi
import Mathlib.Algebra.Order.Group.Abs

namespace Pi
variable {ι : Type*} {α : ι → Type*} [∀ i, AddGroup (α i)] [∀ i, Lattice (α i)]

@[simp]
lemma abs_apply (f : ∀ i, α i) (i : ι) : |f| i = |f i| := rfl

lemma abs_def [∀ i, Neg (α i)] [∀ i, Sup (α i)] (f : ∀ i, α i) : |f| = fun i ↦ |f i| := rfl

end Pi
