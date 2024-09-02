import Mathlib.Data.Finset.Preimage

namespace Finset
variable {α β : Type*} {f : α → β} {s : Finset β}

lemma card_preimage (s : Finset β) (f : α → β) (hf) [DecidablePred (· ∈ Set.range f)] :
    (s.preimage f hf).card = {x ∈ s | x ∈ Set.range f}.card :=
  card_nbij f (by simp) (by simpa) (fun b hb ↦ by aesop)

end Finset
