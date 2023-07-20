import analysis.normed.field.basic
import mathlib.group_theory.order_of_element

section
variables {α : Type*} [normed_division_ring α] {a : α}

protected lemma is_of_fin_order.norm_eq_one (ha : is_of_fin_order a) : ‖a‖ = 1 :=
((norm_hom : α →*₀ ℝ).to_monoid_hom.is_of_fin_order ha).eq_one $ norm_nonneg _

end
