import data.finset.image

open finset function

variables {α β : Type*} [decidable_eq β] {f : α → β}

lemma function.injective.finset_image (hf : injective f) : injective (image f) :=
λ s t h, coe_injective $ hf.image_injective $ by simp_rw [←coe_image, h]
