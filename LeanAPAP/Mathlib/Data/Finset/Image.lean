import Mathbin.Data.Finset.Image

#align_import mathlib.data.finset.image

open Finset Function

variable {α β : Type _} [DecidableEq β] {f : α → β}

theorem Function.Injective.finset_image (hf : Injective f) : Injective (image f) := fun s t h =>
  coe_injective <| hf.image_injective <| by simp_rw [← coe_image, h]

