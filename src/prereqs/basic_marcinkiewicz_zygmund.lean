import algebra.big_operators.order
import analysis.mean_inequalities_pow
import data.complex.basic
import data.fin.tuple.nat_antidiagonal
import data.fintype.big_operators

variables {G : Type*} {k m : ℕ}
open_locale big_operators

open finset fintype

lemma step_one {A : finset G} (hA : A.nonempty) (f : G → ℂ) (a : fin k → G)
  (hf : ∀ i : fin k, ∑ a in pi_finset (λ i : fin k, A), f (a i) = 0) :
  (∑ i, f (a i)).abs ^ (m + 1) ≤
    ∑ b in pi_finset (λ _, A), (∑ i, (f (a i) - f (b i))).abs ^ (m + 1) / A.card ^ k :=
let Ak := pi_finset (λ _ : fin k, A) in
calc
  (∑ i, f (a i)).abs ^ (m + 1) =
    (∑ i, (f (a i) - (∑ b in Ak, f (b i)) / Ak.card)).abs ^ (m + 1) :
      by simp only [hf, sub_zero, zero_div]
  ... = ((∑ b in Ak, ∑ i, (f (a i) - f (b i))) / Ak.card).abs ^ (m + 1) :
    begin
      simp only [sum_sub_distrib],
      rw [sum_const, sub_div, sum_comm, sum_div, nsmul_eq_mul, card_pi_finset, prod_const,
        finset.card_fin, nat.cast_pow, mul_div_cancel_left],
      exact pow_ne_zero _ (nat.cast_ne_zero.2 (finset.card_pos.2 hA).ne'),
    end
  ... = (∑ b in Ak, ∑ i, (f (a i) - f (b i))).abs ^ (m + 1) / Ak.card ^ (m + 1) :
    by rw [map_div₀, div_pow, complex.abs_cast_nat]
  ... ≤ (∑ b in Ak, (∑ i, (f (a i) - f (b i))).abs) ^ (m + 1) / Ak.card ^ (m + 1) :
    div_le_div_of_le (by positivity) (pow_le_pow_of_le_left (by positivity)
      (abv_sum_le_sum_abv _ _) _)
  ... = (∑ b in Ak, (∑ i, (f (a i) - f (b i))).abs) ^ (m + 1) / Ak.card ^ m / Ak.card :
    by rw [div_div, ←pow_succ']
  ... ≤ _ :
  begin
    refine (div_le_div_of_le (by positivity) (real.pow_sum_div_card_le_sum_pow Ak m _)).trans _,
    { intros i hi,
      positivity },
    rw [card_pi_finset, prod_const, finset.card_fin, nat.cast_pow, sum_div],
  end

lemma basic_marcinkiewicz_zygmund {A : finset G} (f : G → ℂ)
  (hf : ∀ i : fin k, ∑ a in pi_finset (λ _, A), f (a i) = 0) :
  ∑ a in pi_finset (λ _, A), (∑ i : fin k, f (a i)).abs ^ (2 * m) ≤
    A.card ^ m * (4 * m) ^ m * (∑ a in pi_finset (λ _, A),
      ∑ i : fin k, (f (a i)).abs ^ 2) ^ m :=
begin
  sorry,
end
