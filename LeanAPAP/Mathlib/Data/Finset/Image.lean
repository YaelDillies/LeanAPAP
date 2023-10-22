import Mathlib.Data.Finset.Image

open Finset Function

variable {α β : Type*} [DecidableEq β] {f : α → β}

lemma Function.Injective.finset_image (hf : Injective f) : Injective (image f) := fun s t h ↦
  coe_injective $ hf.image_injective $ by simp_rw [←coe_image, h]
