import data.finset.pointwise
import mathlib.data.fintype.pi
import group_theory.group_action.pi

open finset
open_locale pointwise

namespace fintype
variables {ι : Type*} {α β : ι → Type*} [fintype ι] [decidable_eq ι]

@[to_additive]
lemma pi_finset_mul [Π i, decidable_eq (α i)] [Π i, has_mul (α i)] (s t : Π i, finset (α i)) :
  pi_finset (s * t) = fintype.pi_finset s * fintype.pi_finset t :=
fintype.pi_finset_image₂ _ _ _

@[to_additive]
lemma pi_finset_div [Π i, decidable_eq (α i)] [Π i, has_div (α i)] (s t : Π i, finset (α i)) :
  pi_finset (s / t) = fintype.pi_finset s / fintype.pi_finset t :=
fintype.pi_finset_image₂ _ _ _

@[to_additive]
lemma pi_finset_smul [Π i, decidable_eq (β i)] [Π i, has_smul (α i) (β i)] (s : Π i, finset (α i))
  (t : Π i, finset (β i)) :
  pi_finset (s • t) = fintype.pi_finset s • fintype.pi_finset t :=
fintype.pi_finset_image₂ _ _ _

@[to_additive]
lemma pi_finset_smul_finset [Π i, decidable_eq (β i)] [Π i, has_smul (α i) (β i)] (a : Π i, α i)
  (s : Π i, finset (β i)) :
  pi_finset (a • s) = a • fintype.pi_finset s :=
fintype.pi_finset_image _ _

end fintype
