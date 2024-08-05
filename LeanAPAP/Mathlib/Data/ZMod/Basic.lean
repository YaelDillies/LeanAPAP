import Mathlib.Data.ZMod.Basic

namespace ZMod
variable {n : ℕ} {P : ZMod n → Prop}

lemma «forall» : (∀ x, P x) ↔ ∀ x : ℤ, P x := intCast_surjective.forall
lemma «exists» : (∃ x, P x) ↔ ∃x : ℤ, P x := intCast_surjective.exists

end ZMod
