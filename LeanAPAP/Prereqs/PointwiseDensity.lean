import Mathlib.Data.Finset.Density
import Mathlib.Data.Finset.Pointwise.Basic

open scoped Pointwise

namespace Finset
variable {α : Type*} [DecidableEq α] [InvolutiveInv α] [Fintype α]

@[to_additive (attr := simp)] lemma dens_inv (s : Finset α) : s⁻¹.dens = s.dens := by simp [dens]

end Finset
