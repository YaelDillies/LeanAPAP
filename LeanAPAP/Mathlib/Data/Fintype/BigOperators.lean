import Mathlib.Data.Fintype.BigOperators

open scoped BigOperators

namespace Finset
variable {α β γ : Type*} [DecidableEq β] [Fintype β] [CommMonoid γ]

@[to_additive]
lemma prod_fiberwise' (s : Finset α) (f : α → β) (g : β → γ) :
    ∏ b, ∏ _a in s.filter (fun a ↦ f a = b), g b = ∏ a in s, g (f a) :=
  calc
    _ = ∏ b, ∏ a in s.filter (fun a ↦ f a = b), g (f a) := by
        congr with b; exact prod_congr rfl (fun a ha ↦ by rw [← (mem_filter.1 ha).2])
    _ = _ := prod_fiberwise _ _ _

end Finset
