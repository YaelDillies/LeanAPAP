import data.real.sqrt
import mathlib.data.real.nnreal
import mathlib.group_theory.submonoid.basic

open nnreal set
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
