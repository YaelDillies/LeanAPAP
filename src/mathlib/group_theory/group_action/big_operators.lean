import algebra.module.basic
import group_theory.group_action.big_operators
import mathlib.algebra.big_operators.pi

open finset fintype
open_locale big_operators

namespace fintype
variables {α β γ : Type*} [decidable_eq α] [fintype α] [add_comm_monoid γ]

lemma sum_fintype_apply (f : β → γ) (s : finset β) (a : α) :
  ∑ g in pi_finset (λ _ : α, s), f (g a) = s.card ^ (card α - 1) • ∑ b in s, f b :=
begin
  classical,
  rw sum_comp,
  simp only [image_pi_finset_const, filter_pi_finset_const_card s, ite_smul, zero_smul, smul_sum,
    sum_ite_mem, inter_self],
end

end fintype
