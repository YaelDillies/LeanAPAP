import algebra.big_operators.order
import analysis.mean_inequalities_pow
import data.complex.basic
import data.fin.tuple.nat_antidiagonal
import data.fintype.big_operators
import prereqs.multinomial

variables {G : Type*} {n m : ℕ}
open_locale big_operators

open finset fintype

@[reducible] def pi_finset_const (A : finset G) (n : ℕ) := fintype.pi_finset (λ _ : fin n, A)

local infix `^^`:70 := pi_finset_const

lemma step_one {A : finset G} (hA : A.nonempty) (f : G → ℂ) (a : fin n → G)
  (hf : ∀ i : fin n, ∑ a in A^^n, f (a i) = 0) :
  (∑ i, f (a i)).abs ^ (m + 1) ≤
    (∑ b in A^^n, (∑ i, (f (a i) - f (b i))).abs ^ (m + 1)) / A.card ^ n :=
calc
  (∑ i, f (a i)).abs ^ (m + 1) =
    (∑ i, (f (a i) - (∑ b in A^^n, f (b i)) / (A^^n).card)).abs ^ (m + 1) :
      by simp only [hf, sub_zero, zero_div]
  ... = ((∑ b in A^^n, ∑ i, (f (a i) - f (b i))) / (A^^n).card).abs ^ (m + 1) :
    begin
      simp only [sum_sub_distrib],
      rw [sum_const, sub_div, sum_comm, sum_div, nsmul_eq_mul, card_pi_finset, prod_const,
        finset.card_fin, nat.cast_pow, mul_div_cancel_left],
      exact pow_ne_zero _ (nat.cast_ne_zero.2 (finset.card_pos.2 hA).ne'),
    end
  ... = (∑ b in A^^n, ∑ i, (f (a i) - f (b i))).abs ^ (m + 1) / (A^^n).card ^ (m + 1) :
    by rw [map_div₀, div_pow, complex.abs_cast_nat]
  ... ≤ (∑ b in A^^n, (∑ i, (f (a i) - f (b i))).abs) ^ (m + 1) / (A^^n).card ^ (m + 1) :
    div_le_div_of_le (by positivity) (pow_le_pow_of_le_left (by positivity)
      (abv_sum_le_sum_abv _ _) _)
  ... = (∑ b in A^^n, (∑ i, (f (a i) - f (b i))).abs) ^ (m + 1) / (A^^n).card ^ m / (A^^n).card :
    by rw [div_div, ←pow_succ']
  ... ≤ _ :
  begin
    rw sum_div,
    refine (div_le_div_of_le (by positivity) (real.pow_sum_div_card_le_sum_pow (A^^n) m _)).trans _,
    { intros i hi,
      positivity },
    rw [card_pi_finset, prod_const, finset.card_fin, nat.cast_pow, sum_div],
  end

lemma step_one' {A : finset G} (hA : A.nonempty) (f : G → ℂ) (a : fin n → G)
  (hf : ∀ i : fin n, ∑ a in A^^n, f (a i) = 0) :
  (∑ i, f (a i)).abs ^ m ≤
    (∑ b in A^^n, (∑ i, (f (a i) - f (b i))).abs ^ m) / A.card ^ n :=
begin
  cases m,
  { simp only [pow_zero, sum_const, prod_const, nat.smul_one_eq_coe, finset.card_fin,
      card_pi_finset, ←nat.cast_pow],
    rw div_self,
    rw [nat.cast_ne_zero, ←pos_iff_ne_zero],
    exact pow_pos (finset.card_pos.2 hA) _ },
  exact step_one hA f a hf
end

lemma sum_nbij {α β γ : Type*} [add_comm_monoid β] {s : finset α} {t : finset γ}
  {f : α → β} {g : γ → β} (i : α → γ) (hi : ∀ a ∈ s, i a ∈ t) (h : ∀ a ∈ s, f a = g (i a))
  (i_inj : ∀ a₁ a₂, a₁ ∈ s → a₂ ∈ s → i a₁ = i a₂ → a₁ = a₂) (i_surj : ∀ b ∈ t, ∃ a ∈ s, b = i a) :
  (∑ x in s, f x) = (∑ x in t, g x) :=
sum_bij (λ a _, i a) hi h i_inj i_surj

lemma sum_nbij' {α β γ : Type*} [add_comm_monoid β] {s : finset α} {t : finset γ}
  {f : α → β} {g : γ → β}
  (i : α → γ) (hi : ∀ a ∈ s, i a ∈ t) (h : ∀ a ∈ s, f a = g (i a))
  (j : γ → α) (hj : ∀ a ∈ t, j a ∈ s) (left_inv : ∀ a ∈ s, j (i a) = a)
  (right_inv : ∀ a ∈ t, i (j a) = a) :
  (∑ x in s, f x) = (∑ x in t, g x) :=
sum_bij' (λ a _, i a) hi h (λ b _, j b) hj left_inv right_inv

-- works with this
-- lemma step_two_aux' {β γ : Type*} [add_comm_monoid β] [comm_ring γ] {A : finset G}
--   (f : (fin n → G) → (fin n → γ)) (ε : fin n → γ)
--   (hε : ∀ i : fin n, ε i = -1 ∨ ε i = 1) (g : (fin n → γ) → β) :
--   ∑ a b in A^^n, g (ε * (f a - f b)) = ∑ a b in A^^n, g (f a - f b) :=
-- feels like could generalise more...
-- the key point is that you combine the double sums into a single sum, and do a pair swap
-- when the corresponding ε is -1
-- but the order here is a bit subtle (ie this explanation is an oversimplification)

lemma step_two_aux (A : finset G) (f : G → ℂ) (ε : fin n → ℂ)
  (hε : ε ∈ ({-1, 1} : finset ℂ)^^n) (g : (fin n → ℂ) → ℝ) :
  ∑ a b in A^^n, g (ε * (f ∘ a - f ∘ b)) = ∑ a b in A^^n, g (f ∘ a - f ∘ b) :=
begin
  rw [←sum_product', ←sum_product'],
  let swapper : (fin n → G) × (fin n → G) → (fin n → G) × (fin n → G),
  { intros xy,
    exact (λ i, if ε i = 1 then xy.1 i else xy.2 i, λ i, if ε i = 1 then xy.2 i else xy.1 i) },
  have h₁ : ∀ a ∈ (A^^n) ×ˢ (A^^n), swapper a ∈ (A^^n) ×ˢ (A^^n),
  { intros a,
    simp only [mem_product, and_imp, mem_pi_finset, ←forall_and_distrib],
    intros h i,
    split_ifs,
    { exact h i },
    exact (h i).symm },
  have h₂ : ∀ a ∈ (A^^n) ×ˢ (A^^n), swapper (swapper a) = a,
  { intros a ha,
    ext,
    { simp only, split_ifs; refl },
    { simp only, split_ifs; refl } },
  refine sum_nbij' swapper h₁ _ swapper h₁ h₂ h₂,
  { rintro ⟨a, b⟩ _,
    congr' with i : 1,
    simp only [pi.mul_apply, pi.sub_apply, function.comp_apply],
    simp only [mem_pi_finset, mem_insert, mem_singleton] at hε,
    split_ifs,
    { simp [h] },
    rw (hε i).resolve_right h,
    ring },
end

lemma step_two {A : finset G} (hA : A.nonempty) (f : G → ℂ) (g : G → G → ℂ) :
  ∑ a b in A^^n, (∑ i, (f (a i) - f (b i))).abs ^ (2 * m) =
    1 / 2 ^ n * ∑ ε in ({-1, 1} : finset ℂ)^^n,
      ∑ a b in A^^n, (∑ i, ε i * (f (a i) - f (b i))).abs ^ (2 * m) :=
begin
  have : ∀ (ε : fin n → ℂ), ε ∈ ({-1, 1} : finset ℂ)^^n →
    ∑ a b in A^^n, (∑ i, ε i * (f (a i) - f (b i))).abs ^ (2 * m) =
      ∑ a b in A^^n, (∑ i, (f (a i) - f (b i))).abs ^ (2 * m),
  { intros ε hε,
    exact step_two_aux A f _ hε (λ z : fin n → ℂ, (univ.sum z).abs ^ (2 * m)) },
  rw [sum_congr rfl this, sum_const, card_pi_finset, prod_const, finset.card_fin,
    card_insert_of_not_mem, card_singleton, ←bit0, nsmul_eq_mul, nat.cast_pow, nat.cast_two,
    one_div, inv_mul_cancel_left₀],
  { positivity },
  norm_num
end

lemma step_three {A : finset G} (hA : A.nonempty) (f : G → ℂ) (g : G → G → ℂ) :
  ∑ ε in ({-1, 1} : finset ℂ)^^n, ∑ a b in A^^n, (∑ i, ε i * (f (a i) - f (b i))).abs ^ (2 * m)
    ≤ ∑ a b in A^^n, ∑ ε in ({-1, 1} : finset ℂ)^^n,
      ∑ k in cut (univ : finset (fin n)) (2 * m), sorry :=
begin
  simp only [@sum_comm _ _ (fin n → ℂ) _ _ (A^^n), ←complex.abs_pow, multinomial_expansion'],
  refine sum_le_sum (λ a ha, _),
  refine sum_le_sum (λ b hb, _),
  refine sum_le_sum (λ ε hε, _),


  -- change ∑ x in _, (∑ p in (univ : finset (fin n))^^(2 * m), _) ≤ _,
end

lemma basic_marcinkiewicz_zygmund {A : finset G} (f : G → ℂ)
  (hf : ∀ i : fin n, ∑ a in pi_finset (λ _, A), f (a i) = 0) :
  ∑ a in pi_finset (λ _, A), (∑ i : fin n, f (a i)).abs ^ (2 * m) ≤
    A.card ^ m * (4 * m) ^ m * (∑ a in pi_finset (λ _, A),
      ∑ i : fin n, (f (a i)).abs ^ 2) ^ m :=
begin
  sorry,
end
