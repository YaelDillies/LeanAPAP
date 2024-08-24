import Mathlib.Order.Filter.Basic

namespace Filter
variable {α β : Type*} {f g : α → β}

@[simp] lemma eventuallyEq_top : f =ᶠ[⊤] g ↔ f = g := by simp [EventuallyEq, funext_iff]

end Filter
