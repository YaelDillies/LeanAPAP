import Mathlib.Data.Finset.Density
import LeanAPAP.Mathlib.Data.Rat.Cast.Lemmas

open Fintype

namespace Finset
variable {α 𝕜 : Type*} [Fintype α] {s : Finset α}

@[simp] lemma dens_le_one : s.dens ≤ 1 := by
  cases isEmpty_or_nonempty α
  · simp [Subsingleton.elim s ∅]
  · simpa using dens_le_dens s.subset_univ

lemma cast_dens [Semifield 𝕜] [CharZero 𝕜] (s : Finset α) :
    (s.dens : 𝕜) = s.card / Fintype.card α := by simp [dens]

end Finset
