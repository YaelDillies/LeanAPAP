import Mathlib.Data.Finset.Density

open Function

namespace Finset
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] {f : α → β}

lemma dens_image (hf : Bijective f) (s : Finset α) : (s.image f).dens = s.dens := by
  simpa [map_eq_image, -dens_map_equiv] using dens_map_equiv (.ofBijective f hf)

end Finset
