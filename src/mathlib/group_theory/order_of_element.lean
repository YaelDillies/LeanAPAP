import group_theory.order_of_element
import mathlib.algebra.group_power.order

/-!
### TODO

Rename `exists_pow_eq_one` to `is_of_fin_order_of_finite`
-/

open fintype function

section monoid
variables {α : Type*} [monoid α] {a : α}

lemma is_of_fin_order.pow {n : ℕ} : is_of_fin_order a → is_of_fin_order (a ^ n) :=
begin
  simp_rw is_of_fin_order_iff_pow_eq_one,
  rintro ⟨m, hm, ha⟩,
  exact ⟨m, hm, by simp [pow_right_comm _ n, ha]⟩,
end

end monoid

section group
variables {α : Type*} [group α] [fintype α] {n : ℕ}

@[simp, to_additive mod_card_nsmul] lemma pow_mod_card (a : α) (n : ℕ) : a ^ (n % card α) = a ^ n :=
mul_left_injective (a ^ (card α * (n / card α))) $
  by simp_rw [←pow_add, nat.mod_add_div, pow_add, pow_mul, pow_card_eq_one, one_pow, mul_one]

@[to_additive]
lemma nat.coprime.pow_bijective (hn : n.coprime (card α)) : bijective (λ a : α, a ^ n) :=
begin
  refine (bijective_iff_injective_and_card _).2 ⟨_, rfl⟩,
  casesI subsingleton_or_nontrivial α,
  { exact injective_of_subsingleton _ },
  obtain ⟨m, hm⟩ := nat.exists_mul_mod_eq_one_of_coprime hn fintype.one_lt_card,
  refine left_inverse.injective (λ a, _),
  { exact λ a, a ^ m },
  rw [←pow_mul, ←pow_mod_card, hm, pow_one],
end

end group

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
