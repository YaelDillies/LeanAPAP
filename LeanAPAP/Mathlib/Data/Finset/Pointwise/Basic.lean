import Mathlib.Data.Finset.Density
import Mathlib.Data.Finset.Pointwise.Basic

open scoped Pointwise

namespace Finset
variable {α β : Type*} [Group α] [Fintype β] [DecidableEq β] [MulAction α β]

@[to_additive (attr := simp)]
lemma dens_smul_finset (a : α) (s : Finset β) : (a • s).dens = s.dens := by simp [dens]

end Finset
