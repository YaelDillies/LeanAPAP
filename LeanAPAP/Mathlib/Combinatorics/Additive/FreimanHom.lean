import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.Combinatorics.Additive.FreimanHom

open Set

variable {α β S : Type*} [CommMonoid α] [CommMonoid β] [SetLike S α] [SubmonoidClass S α] {n : ℕ}

@[to_additive]
lemma IsMulFreimanHom.subtypeVal {s : S} : IsMulFreimanHom n (univ : Set s) univ Subtype.val :=
  MonoidHomClass.isMulFreimanHom (SubmonoidClass.subtype s) (mapsTo_univ ..)
