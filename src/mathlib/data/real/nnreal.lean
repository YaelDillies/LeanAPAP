import data.real.nnreal

open_locale nnreal

namespace nnreal
variables {x : ℝ≥0}

instance {M : Type*} [ordered_add_comm_monoid M] [module ℝ M] [ordered_smul ℝ M] :
  ordered_smul ℝ≥0 M :=
{ smul_lt_smul_of_pos := λ a b c hab hc, (smul_lt_smul_of_pos hab (nnreal.coe_pos.2 hc) : _),
  lt_of_smul_lt_smul_of_pos := λ a b c hab hc,
    lt_of_smul_lt_smul_of_nonneg (by exact hab) (nnreal.coe_nonneg c) }

@[simp] lemma mk_le_mk {x y : ℝ} {hx : 0 ≤ x} {hy : 0 ≤ y} : (⟨x, hx⟩ : ℝ≥0) ≤ ⟨y, hy⟩ ↔ x ≤ y :=
iff.rfl

@[simp, norm_cast] lemma one_le_coe : 1 ≤ (x : ℝ) ↔ 1 ≤ x :=
by rw [←nnreal.coe_le_coe, nnreal.coe_one]

@[simp, norm_cast] lemma one_lt_coe : 1 < (x : ℝ) ↔ 1 < x :=
by rw [←nnreal.coe_lt_coe, nnreal.coe_one]

lemma coe_ne_one : (x : ℝ) ≠ 1 ↔ x ≠ 1 := x.coe_eq_one.not

instance : star_ring ℝ≥0 := star_ring_of_comm
instance : has_trivial_star ℝ≥0 := ⟨λ _, rfl⟩

end nnreal
