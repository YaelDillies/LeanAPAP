import group_theory.order_of_element
import mathlib.algebra.group_power.order

section monoid
variables {α : Type*} [monoid α] {a : α}

lemma is_of_fin_order.pow {n : ℕ} : is_of_fin_order a → is_of_fin_order (a ^ n) :=
begin
  simp_rw is_of_fin_order_iff_pow_eq_one,
  rintro ⟨m, hm, ha⟩,
  exact ⟨m, hm, by simp [pow_right_comm _ n, ha]⟩,
end

end monoid

section linear_ordered_semiring
variables {α : Type*} [linear_ordered_semiring α] {a : α}

protected lemma is_of_fin_order.eq_one (ha₀ : 0 ≤ a) : is_of_fin_order a → a = 1 :=
begin
  rw is_of_fin_order_iff_pow_eq_one,
  rintro ⟨n, hn, ha⟩,
  exact (pow_eq_one_iff_of_nonneg ha₀ hn.ne').1 ha,
end

end linear_ordered_semiring

section linear_ordered_ring
variables {α : Type*} [linear_ordered_ring α] {a : α}

protected lemma is_of_fin_order.eq_neg_one (ha₀ : a ≤ 0) (ha : is_of_fin_order a) : a = -1 :=
(sq_eq_one_iff.1 $ ha.pow.eq_one $ sq_nonneg a).resolve_left $
  by rintro rfl; exact one_pos.not_le ha₀

end linear_ordered_ring
