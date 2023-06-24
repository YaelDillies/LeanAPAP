import data.nat.choose.basic
import algebra.big_operators.order
import data.finset.powerset
import data.fin.tuple.nat_antidiagonal

open_locale big_operators nat
open finset

variables {K : Type*} [fintype K] (f : K → ℕ)

def multinomial (s : finset K) (f : K → ℕ) : ℕ := (∑ i in s, f i)! / ∏ i in s, (f i)!

lemma multinomial_dvd {α : Type*} (s : finset α) (f : α → ℕ) :
  ∏ i in s, (f i)! ∣ (∑ i in s, f i)! :=
begin
  induction s using finset.cons_induction_on with a s has ih,
  { simp },
  rw [prod_cons, sum_cons],
  exact (mul_dvd_mul_left _ ih).trans (nat.factorial_mul_factorial_dvd_factorial_add _ _),
end

lemma multinomial_cons {a : K} {s : finset K} (has : a ∉ s) :
  multinomial (finset.cons a s has) f = nat.choose (f a + ∑ i in s, f i) (f a) * multinomial s f :=
begin
  rw [multinomial, nat.div_eq_iff_eq_mul_left _ (multinomial_dvd _ _), prod_cons, multinomial,
    mul_assoc, mul_left_comm _ (f a)!, nat.div_mul_cancel (multinomial_dvd _ _), ←mul_assoc,
    nat.choose_symm_add, nat.add_choose_mul_factorial_mul_factorial, sum_cons],
  exact prod_pos (λ i hi, by positivity),
end

lemma multinomial_expansion {α β : Type*} [comm_semiring β] {x : α → β} {s : finset α} {n : ℕ} :
  (∑ i in s, x i) ^ n = ∑ p in fintype.pi_finset (λ _, s), ∏ i : fin n, x (p i) :=
begin

end
