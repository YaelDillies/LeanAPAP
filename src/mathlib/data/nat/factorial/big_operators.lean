import data.nat.factorial.big_operators

open finset
open_locale nat big_operators

namespace nat

variables {α : Type*} (s : finset α) (f : α → ℕ)

--TODO: Golf mathlib proof
private lemma prod_factorial_dvd_factorial_sum : ∏ i in s, (f i)! ∣ (∑ i in s, f i)! :=
begin
  induction s using finset.cons_induction_on with a s has ih,
  { simp },
  rw [prod_cons, sum_cons],
  exact (mul_dvd_mul_left _ ih).trans (nat.factorial_mul_factorial_dvd_factorial_add _ _),
end

end nat
