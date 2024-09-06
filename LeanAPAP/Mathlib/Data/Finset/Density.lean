import Mathlib.Data.Finset.Density

namespace Finset

attribute [simp] card_mul_dens dens_mul_card natCast_card_mul_nnratCast_dens
  nnratCast_dens_mul_natCast_card

@[simp] lemma nnratCast_dens_mul_natCast_card' {𝕜 α : Type*} [Fintype α] [Semifield 𝕜] [CharZero 𝕜]
    (s : Finset α) : (s.dens * Fintype.card α : 𝕜) = s.card := mod_cast s.dens_mul_card
