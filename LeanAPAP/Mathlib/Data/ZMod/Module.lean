import Mathlib.Data.ZMod.Module

namespace AddSubgroup
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module (ZMod n) M] {S : AddSubgroup M} {x : M}

@[simp] lemma mem_toZModSubmodule : x ∈ toZModSubmodule n S ↔ x ∈ S := .rfl

end AddSubgroup
