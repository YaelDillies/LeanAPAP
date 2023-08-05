import data.real.sqrt
import mathlib.data.real.nnreal
import mathlib.algebra.big_operators.order
import mathlib.group_theory.submonoid.basic

open nnreal set
open_locale big_operators nnreal

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

namespace finset

lemma cauchy_schwarz_sqrt {α : Type*} (s : finset α) (f g : α → ℝ) :
  ∑ i in s, f i * g i ≤ (∑ i in s, f i ^ 2).sqrt * (∑ i in s, g i ^ 2).sqrt :=
(real.le_sqrt_of_sq_le $ sum_mul_sq_le_sq_mul_sq _ _ _).trans_eq $
  real.sqrt_mul (sum_nonneg $ λ _ _, sq_nonneg _) _

end finset

namespace nnreal
variables {x : ℝ≥0}

@[simp] lemma one_le_sqrt : 1 ≤ x.sqrt ↔ 1 ≤ x := by rw [←sqrt_one, sqrt_le_sqrt_iff, sqrt_one]

end nnreal

namespace real
variables {x y : ℝ}

lemma sqrt_le_sqrt_iff' (hx : 0 < x) : x.sqrt ≤ y.sqrt ↔ x ≤ y :=
begin
  obtain hy | hy := le_total y 0,
  { exact iff_of_false ((sqrt_eq_zero_of_nonpos hy).trans_lt $ sqrt_pos.2 hx).not_le
      (hy.trans_lt hx).not_le },
  { exact sqrt_le_sqrt_iff hy }
end

@[simp] lemma one_le_sqrt : 1 ≤ x.sqrt ↔ 1 ≤ x :=
by rw [←sqrt_one, sqrt_le_sqrt_iff' zero_lt_one, sqrt_one]

end real
