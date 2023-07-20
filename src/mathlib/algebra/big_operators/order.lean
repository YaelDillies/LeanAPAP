import algebra.big_operators.order
import algebra.big_operators.ring

open_locale big_operators

namespace finset
variables {α 𝕜 : Type*} [linear_ordered_comm_ring 𝕜]

lemma sum_mul_sq_le_sq_mul_sq (s : finset α) (f g : α → 𝕜) :
  (∑ i in s, f i * g i)^2 ≤ (∑ i in s, (f i)^2) * ∑ i in s, (g i)^2 :=
begin
  have h : 0 ≤ ∑ i in s, (f i * ∑ j in s, (g j)^2 - g i * ∑ j in s, f j * g j)^2 :=
    sum_nonneg (λ i hi, sq_nonneg _),
  simp_rw [sub_sq, sum_add_distrib, finset.sum_sub_distrib, mul_pow, mul_assoc, ←mul_sum, ←sum_mul,
    mul_left_comm, ←mul_assoc, ←sum_mul, mul_right_comm, ←sq, mul_comm, sub_add, two_mul,
    add_sub_cancel, mul_comm (∑ j in s, (g j)^2), sq (∑ j in s, (g j)^2),
    ←mul_assoc, ←mul_sub_right_distrib] at h,
  obtain h' | h' := (sum_nonneg (λ i (hi : i ∈ s), sq_nonneg (g i))).eq_or_lt,
  { have h'' : ∀ i ∈ s, g i = 0 :=
      λ i hi, by simpa using (sum_eq_zero_iff_of_nonneg (λ i _, sq_nonneg (g i))).1 h'.symm i hi,
    rw [←h', sum_congr rfl (show ∀ i ∈ s, f i * g i = 0, from λ i hi, by simp [h'' i hi])],
    simp },
  { rw ←sub_nonneg,
    exact nonneg_of_mul_nonneg_left h h' }
end

end finset
