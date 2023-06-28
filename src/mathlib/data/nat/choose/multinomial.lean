import data.nat.choose.multinomial

open finset
open_locale big_operators nat

variables {α : Type*} {s : finset α} {f : α → ℕ} {a b : α} {n : ℕ}

namespace nat

lemma multinomial_cons (ha : a ∉ s) :
  multinomial (s.cons a ha) f = (f a + ∑ i in s, f i).choose (f a) * multinomial s f :=
begin
  rw [multinomial, nat.div_eq_iff_eq_mul_left _ (prod_factorial_dvd_factorial_sum _ _), prod_cons,
    multinomial, mul_assoc, mul_left_comm _ (f a)!,
    nat.div_mul_cancel (prod_factorial_dvd_factorial_sum _ _), ←mul_assoc, nat.choose_symm_add,
    nat.add_choose_mul_factorial_mul_factorial, sum_cons],
  exact prod_pos (λ i hi, by positivity),
end

-- TODO: Fix implicitness to `nat.multinomial_insert`
lemma multinomial_insert' [decidable_eq α] (ha : a ∉ s) :
  multinomial (insert a s) f = (f a + ∑ i in s, f i).choose (f a) * multinomial s f :=
by rw [←cons_eq_insert _ _ ha, multinomial_cons]

end nat
