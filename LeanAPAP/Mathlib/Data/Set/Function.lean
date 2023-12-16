import Mathlib.Data.Set.Function

namespace Set
variable {α β : Type*} {f : α → β} {s : Set α} {a b : α}

@[simp] lemma injOn_pair : InjOn f {a, b} ↔ f a = f b → a = b := by unfold InjOn; aesop

end Set
