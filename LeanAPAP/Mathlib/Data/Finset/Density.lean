import Mathlib.Data.Finset.Density
import Mathlib.Data.Rat.Cast.CharZero

open Fintype

namespace Finset
variable {α β 𝕜 : Type*} [Fintype α] [Fintype β] {s : Finset α}

lemma card_mul_dens (s : Finset α) : Fintype.card α * s.dens = s.card := by
  cases isEmpty_or_nonempty α
  · simp [Subsingleton.elim s ∅]
  rw [dens, mul_div_cancel₀]
  exact mod_cast Fintype.card_ne_zero

lemma dens_mul_card (s : Finset α) : s.dens * Fintype.card α = s.card := by
  rw [mul_comm, card_mul_dens]

@[simp] lemma dens_le_one : s.dens ≤ 1 := by
  cases isEmpty_or_nonempty α
  · simp [Subsingleton.elim s ∅]
  · simpa using dens_le_dens s.subset_univ

@[simp] lemma dens_map_equiv (e : α ≃ β) : (Finset.map e.toEmbedding s).dens = s.dens := by
  simp [dens, Fintype.card_congr e]

section Semifield
variable [Semifield 𝕜] [CharZero 𝕜]

lemma natCast_card_mul_nnratCast_dens (s : Finset α) : (Fintype.card α * s.dens : 𝕜) = s.card :=
  mod_cast s.card_mul_dens

lemma nnratCast_dens_mul_natCast_card (s : Finset α) : s.dens * Fintype.card α = s.card :=
  mod_cast s.dens_mul_card

@[norm_cast] lemma nnratCast_dens (s : Finset α) : (s.dens : 𝕜) = s.card / Fintype.card α := by
  simp [dens]

end Semifield
end Finset
