import Mathlib.Data.Complex.Basic

namespace Complex

@[simp] lemma coe_comp_sub {α : Type*} (f g : α → ℝ) :
    ofReal' ∘ (f - g) = ofReal' ∘ f - ofReal' ∘ g := map_comp_sub ofReal _ _

end Complex
