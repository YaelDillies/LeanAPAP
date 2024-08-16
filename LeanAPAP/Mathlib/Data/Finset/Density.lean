import Mathlib.Data.Finset.Density
import Mathlib.Data.Rat.Cast.CharZero

open Fintype

namespace Finset
variable {α β 𝕜 : Type*} [Fintype α][Fintype β] {s : Finset α}

@[simp] lemma dens_le_one : s.dens ≤ 1 := by
  cases isEmpty_or_nonempty α
  · simp [Subsingleton.elim s ∅]
  · simpa using dens_le_dens s.subset_univ

lemma cast_dens [Semifield 𝕜] [CharZero 𝕜] (s : Finset α) :
    (s.dens : 𝕜) = s.card / Fintype.card α := by simp [dens]

@[simp] lemma dens_map_equiv (e : α ≃ β) : (Finset.map e.toEmbedding s).dens = s.dens := by
  simp [dens, Fintype.card_congr e]

end Finset
