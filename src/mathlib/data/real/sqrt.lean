import data.real.sqrt
import mathlib.data.real.nnreal

open set

namespace submonoid
variables (α : Type*) [ordered_comm_monoid α] {a : α}

@[to_additive, simps] def one_le : submonoid α :=
{ carrier := {a | 1 ≤ a},
  mul_mem' := λ _ _, one_le_mul,
  one_mem' := le_rfl }

variables {α}

@[simp, to_additive] lemma mem_one_le : a ∈ one_le α ↔ 1 ≤ a := iff.rfl

end submonoid

open nnreal
open_locale nnreal

instance : star_ordered_ring ℝ≥0 :=
{ le_iff := λ x y, begin
    split, swap,
    { rintro ⟨p, hp, rfl⟩,
      exact le_self_add },
    rw [←nnreal.coe_le_coe, star_ordered_ring.le_iff],
    rintro ⟨p, hp, h⟩,
    refine ⟨⟨p, (add_submonoid.closure_le.2 (range_subset_iff.2 $ λ x, _)
      hp : p ∈ add_submonoid.nonneg ℝ)⟩, _, nnreal.coe_injective h⟩,
    { simp [mul_self_nonneg] },
    { exact add_submonoid.subset_closure
        ⟨nnreal.sqrt _, by dsimp; rw [star_trivial, ←sqrt_mul, sqrt_mul_self]⟩ }
  end,
  ..nnreal.ordered_comm_semiring }
