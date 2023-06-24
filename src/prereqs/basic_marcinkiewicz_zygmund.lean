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

lemma without_fucking_about_with_factorials_binary {m : ℕ} {x y : ℝ} :
  ∑ i in range (m + 1), (x ^ (2 * i) * y ^ (2 * (m - i)) * (2 * m).choose (2 * i)) ≤
    (x ^ 2 + y ^ 2) ^ m * m ^ m :=
begin
  rw [add_pow, sum_mul],
  refine sum_le_sum (λ i hi, _),
  simp only [mem_range_succ_iff] at hi,
  rw [pow_mul, pow_mul, mul_assoc (_ * _)],
  refine mul_le_mul_of_nonneg_left _ (by positivity),
  norm_cast,
end

-- 2m C 2i / (m C i) ^ 2 =  2m! i!^2 (m-i)!^2 / 2i! (2m-2i)! m!^2
--                       = 2m C m / (2i C i) (2 (m-i) C (m-i))
-- ?≤? m ^ m / (m C i)

-- 2m C 2i ≤ 2m C m ≤ 4 ^ m
-- 2m C 2i / m C i ≤ 2m C m / m C i ≤ 2m C m ≤ 4 ^ m ?≤? m ^ m

-- 2m C m ≤ (2m)^m / m!
-- 2m C 2i / m C i ≤ 2m C m / m C i ≤ (2m)^m / (m! * mCi) = m^m * 2^m / (m! * mCi)

-- 2m C 2i ≤ (m ^ m) * (m C i)
-- 2m! / (2i! (2 (m-i))!) ≤ m ^ m * m! / (i! * (m - i)!)
-- (2m! / m!) / ((2i! / i!) * (2(m-i)! / (m-i)!)) ≤ m ^ m
-- (2m C m) * m! / ((2i C i) * i! * (2 (m-i) C (m-i) * (m-i)!) ≤ m ^ m

-- (4^m / sqrt(pi * (m + 1/4)) * m!) /
--    (4^i / sqrt(pi * (i + 1/3)) * i!) * (4^(m - i) / sqrt(pi * ((m - i) + 1/3)) * (m - i)!)
-- ≤ sqrt((i + 1/3) * pi * (m - i + 1/3) / (m + 1/4)) * m choose i


-- begin
--   cases m,
--   sorry { simp,
--     sorry },
--   refine sum_le_sum _,
--   intros g hg,
--   simp only [fintype.mem_pi_finset] at hg,
--   refine (real.pow_sum_div_card_le_sum_pow _ m _).trans' _,
--   { intros i hi,
--     exact complex.abs.nonneg _ },
--   simp only [sum_sub_distrib, fintype.card_pi_finset, prod_const, card_fin, nat.cast_pow],
-- end

-- #exit

lemma basic_marcinkiewicz_zygmund {A : finset G} (f : G → ℂ)
  (hf : ∀ i : fin k, ∑ a in fintype.pi_finset (λ _, A), f (a i) = 0) :
  ∑ a in fintype.pi_finset (λ _, A), (∑ i : fin k, f (a i)).abs ^ (2 * m) ≤
    A.card ^ m * (4 * m) ^ m * (∑ a in fintype.pi_finset (λ _, A), ∑ i : fin k, (f (a i)).abs ^ 2) ^ m :=
begin

end
