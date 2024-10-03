/-
Copyright (c) 2023 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Positivity.Finset

/-!
# The Marcinkiewicz-Zygmund inequality

This file proves the Marcinkiewicz-Zygmund inequality.
-/

open Finset Fintype Nat Real
variable {ι : Type*} {A : Finset ι} {m n : ℕ}

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

private lemma step_one (hA : A.Nonempty) (f : ι → ℝ) (a : Fin n → ι)
    (hf : ∀ i, ∑ a in A ^^ n, f (a i) = 0) :
    |∑ i, f (a i)| ^ (m + 1) ≤
      (∑ b in A ^^ n, |∑ i, (f (a i) - f (b i))| ^ (m + 1)) / A.card ^ n := by
  let B := A ^^ n
  calc
    |∑ i, f (a i)| ^ (m + 1)
      = |∑ i, (f (a i) - (∑ b in B, f (b i)) / B.card)| ^ (m + 1) := by
      simp only [hf, sub_zero, zero_div]
    _ = |(∑ b in B, ∑ i, (f (a i) - f (b i))) / B.card| ^ (m + 1) := by
      simp only [sum_sub_distrib]
      rw [sum_const, sub_div, sum_comm, sum_div, nsmul_eq_mul, card_piFinset, prod_const,
        Finset.card_univ, Fintype.card_fin, Nat.cast_pow, mul_div_cancel_left₀]
      positivity
    _ = |∑ b in B, ∑ i, (f (a i) - f (b i))| ^ (m + 1) / B.card ^ (m + 1) := by
      rw [abs_div, div_pow, Nat.abs_cast]
    _ ≤ (∑ b in B, |∑ i, (f (a i) - f (b i))|) ^ (m + 1) / B.card ^ (m + 1) := by
      gcongr; exact IsAbsoluteValue.abv_sum _ _ _
    _ = (∑ b in B, |∑ i, (f (a i) - f (b i))|) ^ (m + 1) / B.card ^ m / B.card := by
      rw [div_div, ← _root_.pow_succ]
    _ ≤ (∑ b in B, |∑ i, (f (a i) - f (b i))| ^ (m + 1)) / B.card := by
      gcongr; exact pow_sum_div_card_le_sum_pow (fun _ _ ↦ abs_nonneg _) _
    _ = _ := by simp [B]

private lemma step_one' (hA : A.Nonempty) (f : ι → ℝ) (hf : ∀ i, ∑ a in A ^^ n, f (a i) = 0) (m : ℕ)
    (a : Fin n → ι) :
    |∑ i, f (a i)| ^ m ≤ (∑ b in A ^^ n, |∑ i, (f (a i) - f (b i))| ^ m) / A.card ^ n := by
  cases m
  · simp only [_root_.pow_zero, sum_const, prod_const, Nat.smul_one_eq_cast, Finset.card_fin,
      card_piFinset, ← Nat.cast_pow]
    rw [div_self]
    rw [Nat.cast_ne_zero, ← pos_iff_ne_zero]
    exact pow_pos (Finset.card_pos.2 hA) _
  exact step_one hA f a hf

-- works with this
-- private lemma step_two_aux' {β γ : Type*} [AddCommMonoid β] [CommRing γ]
--   (f : (Fin n → ι) → (Fin n → γ)) (ε : Fin n → γ)
--   (hε : ∀ i, ε i = -1 ∨ ε i = 1) (g : (Fin n → γ) → β) :
--   ∑ a b in A ^^ n, g (ε * (f a - f b)) = ∑ a b in A ^^ n, g (f a - f b) :=
-- feels like could generalise more...
-- the key point is that you combine the double sums into a single sum, and do a pair swap
-- when the corresponding ε is -1
-- but the order here is a bit subtle (ie this explanation is an oversimplification)
private lemma step_two_aux (A : Finset ι) (f : ι → ℝ) (ε : Fin n → ℝ)
    (hε : ε ∈ ({-1, 1} : Finset ℝ)^^n) (g : (Fin n → ℝ) → ℝ) :
    ∑ a in A ^^ n, ∑ b in A ^^ n, g (ε * (f ∘ a - f ∘ b)) =
      ∑ a in A ^^ n, ∑ b in A ^^ n, g (f ∘ a - f ∘ b) := by
  rw [← sum_product', ← sum_product']
  let swapper : (Fin n → ι) × (Fin n → ι) → (Fin n → ι) × (Fin n → ι) := by
    intro xy
    exact (fun i ↦ if ε i = 1 then xy.1 i else xy.2 i, fun i ↦ if ε i = 1 then xy.2 i else xy.1 i)
  have h₁ : ∀ a ∈ (A ^^ n) ×ˢ (A ^^ n), swapper a ∈ (A ^^ n) ×ˢ (A ^^ n) := by
    simp only [mem_product, and_imp, mem_piFinset, ← forall_and]
    intro a h i
    split_ifs
    · exact h i
    · exact (h i).symm
  have h₂ : ∀ a ∈ (A ^^ n) ×ˢ (A ^^ n), swapper (swapper a) = a := fun a _ ↦ by
    ext <;> simp only <;> split_ifs <;> rfl
  refine sum_nbij' swapper swapper h₁ h₁ h₂ h₂ ?_
  · rintro ⟨a, b⟩ _
    congr with i : 1
    simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply]
    simp only [mem_piFinset, mem_insert, mem_singleton] at hε
    split_ifs with h
    · simp [h]
    rw [(hε i).resolve_right h]
    ring

private lemma step_two (f : ι → ℝ) :
    ∑ a in A ^^ n, ∑ b in A ^^ n, (∑ i, (f (a i) - f (b i))) ^ (2 * m) =
      2⁻¹ ^ n * ∑ ε in ({-1, 1} : Finset ℝ)^^n,
        ∑ a in A ^^ n, ∑ b in A ^^ n, (∑ i, ε i * (f (a i) - f (b i))) ^ (2 * m) := by
  let B := A ^^ n
  have : ∀ ε ∈ ({-1, 1} : Finset ℝ)^^n,
    ∑ a in B, ∑ b in B, (∑ i, ε i * (f (a i) - f (b i))) ^ (2 * m) =
      ∑ a in B, ∑ b in B, (∑ i, (f (a i) - f (b i))) ^ (2 * m) :=
    fun ε hε ↦ step_two_aux A f _ hε fun z : Fin n → ℝ ↦ univ.sum z ^ (2 * m)
  rw [Finset.sum_congr rfl this, sum_const, card_piFinset_const, card_pair, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_two, inv_pow, inv_mul_cancel_left₀]
  · positivity
  · norm_num

private lemma step_three (f : ι → ℝ) :
    ∑ ε in ({-1, 1} : Finset ℝ)^^n,
      ∑ a in A ^^ n, ∑ b in A ^^ n, (∑ i, ε i * (f (a i) - f (b i))) ^ (2 * m) =
      ∑ a in A ^^ n, ∑ b in A ^^ n, ∑ k in piAntidiag univ (2 * m),
          (multinomial univ k * ∏ t, (f (a t) - f (b t)) ^ k t) *
            ∑ ε in ({-1, 1} : Finset ℝ)^^n, ∏ t, ε t ^ k t := by
  simp only [@sum_comm _ _ (Fin n → ℝ) _ _ (A ^^ n), ← Complex.abs_pow, sum_pow_eq_sum_piAntidiag]
  refine sum_congr rfl fun a _ ↦ ?_
  refine sum_congr rfl fun b _ ↦ ?_
  simp only [mul_pow, prod_mul_distrib, @sum_comm _ _ (Fin n → ℝ), ← mul_sum, ← sum_mul]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [← mul_assoc, mul_right_comm]

private lemma step_four {k : Fin n → ℕ} :
    ∑ ε in ({-1, 1} : Finset ℝ)^^n, ∏ t, ε t ^ k t = 2 ^ n * ite (∀ i, Even (k i)) 1 0 := by
  have := sum_prod_piFinset ({-1, 1} : Finset ℝ) fun i fi ↦ fi ^ k i
  rw [this, ← Fintype.prod_boole]
  have : (2 : ℝ) ^ n = ∏ i : Fin n, 2 := by simp
  rw [this, ← prod_mul_distrib]
  refine prod_congr rfl fun t _ ↦ ?_
  rw [sum_pair, one_pow, mul_boole]
  swap
  · norm_num
  split_ifs with h
  · rw [h.neg_one_pow, one_add_one_eq_two]
  rw [Nat.not_even_iff_odd] at h
  simp [h.neg_one_pow]

-- double_multinomial
private lemma step_six {f : ι → ℝ} {a b : Fin n → ι} :
    ∑ k : Fin n → ℕ in piAntidiag univ m,
        (multinomial univ fun a ↦ 2 * k a : ℝ) * ∏ i, (f (a i) - f (b i)) ^ (2 * k i) ≤
      m ^ m * (∑ i, (f (a i) - f (b i)) ^ 2) ^ m := by
  rw [sum_pow_eq_sum_piAntidiag, mul_sum]
  convert sum_le_sum fun k hk ↦ _
  rw [mem_piAntidiag] at hk
  simp only [← mul_assoc, pow_mul]
  gcongr
  norm_cast
  refine multinomial_two_mul_le_mul_multinomial.trans ?_
  rw [hk.1]

private lemma step_seven {f : ι → ℝ} {a b : Fin n → ι} :
    m ^ m * (∑ i, (f (a i) - f (b i)) ^ 2 : ℝ) ^ m ≤
      m ^ m * 2 ^ m * (∑ i, (f (a i) ^ 2 + f (b i) ^ 2)) ^ m := by
  rw [← mul_pow, ← mul_pow, ← mul_pow, mul_assoc, mul_sum _ _ (2 : ℝ)]
  gcongr with i
  exact add_sq_le.trans_eq (by simp)

private lemma step_eight {f : ι → ℝ} {a b : Fin n → ι} :
    m ^ m * 2 ^ m * (∑ i, (f (a i) ^ 2 + f (b i) ^ 2)) ^ m ≤
      m ^ m * 2 ^ (m + (m - 1)) *
        ((∑ i, f (a i) ^ 2) ^ m + (∑ i, f (b i) ^ 2) ^ m) := by
  rw [pow_add, ← mul_assoc _ _ (2 ^ _), mul_assoc _ (2 ^ (m - 1)), sum_add_distrib]
  gcongr
  refine add_pow_le ?_ ?_ m <;> positivity

private lemma end_step {f : ι → ℝ} (hm : 1 ≤ m) (hA : A.Nonempty) :
    (∑ a in A ^^ n, ∑ b in A ^^ n, ∑ k in piAntidiag univ m,
      ↑(multinomial univ fun i ↦ 2 * k i) * ∏ t, (f (a t) - f (b t)) ^ (2 * k t)) / A.card ^ n
        ≤ (4 * m) ^ m * ∑ a in A ^^ n, (∑ i, f (a i) ^ 2) ^ m := by
  let B := A ^^ n
  calc
    (∑ a in B, ∑ b in B, ∑ k : Fin n → ℕ in piAntidiag univ m,
      (multinomial univ fun i ↦ 2 * k i : ℝ) * ∏ t, (f (a t) - f (b t)) ^ (2 * k t)) / A.card ^ n
    _ ≤ (∑ a in B, ∑ b in B, m ^ m * 2 ^ (m + (m - 1)) *
          ((∑ i, f (a i) ^ 2) ^ m + (∑ i, f (b i) ^ 2) ^ m) : ℝ) / A.card ^ n := by
      gcongr; exact step_six.trans $ step_seven.trans step_eight
    _ = _ := by
      simp only [mul_add, sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
      rw [← mul_add, ← two_mul, ← mul_assoc 2, ← mul_assoc 2, mul_right_comm 2, ← _root_.pow_succ',
        add_assoc, Nat.sub_add_cancel hm, pow_add, ← mul_pow, ← mul_pow, card_piFinset, prod_const,
        Finset.card_univ, Fintype.card_fin, Nat.cast_pow, mul_div_cancel_left₀]
      norm_num
      positivity

namespace Real

/-- The **Marcinkiewicz-Zygmund inequality** for real-valued functions, with a slightly better
constant than `Real.marcinkiewicz_zygmund`. -/
theorem marcinkiewicz_zygmund' (m : ℕ) (f : ι → ℝ) (hf : ∀ i, ∑ a in A ^^ n, f (a i) = 0) :
    ∑ a in A ^^ n, (∑ i, f (a i)) ^ (2 * m) ≤
      (4 * m) ^ m * ∑ a in A ^^ n, (∑ i, f (a i) ^ 2) ^ m := by
  obtain rfl | hm := m.eq_zero_or_pos
  · simp
  have hm' : 1 ≤ m := by rwa [Nat.succ_le_iff]
  obtain rfl | hA := A.eq_empty_or_nonempty
  · cases n <;> cases m <;> simp
  let B := A ^^ n
  calc
    ∑ a in B, (∑ i, f (a i)) ^ (2 * m)
      ≤ ∑ a in A ^^ n, (∑ b in B, |∑ i, (f (a i) - f (b i))| ^ (2 * m))/ A.card ^ n := by
      gcongr; simpa [pow_mul, sq_abs] using step_one' hA f hf (2 * m) _
    _ ≤ _ := ?_
  rw [← sum_div]
  simp only [pow_mul, sq_abs]
  simp only [← pow_mul]
  rw [step_two, step_three, mul_comm, inv_pow, ← div_eq_mul_inv, div_div]
  simp only [step_four, mul_ite, mul_zero, mul_one, ← sum_filter, ← sum_mul]
  rw [mul_comm, mul_div_mul_left]
  swap; · positivity
  simpa only [even_iff_two_dvd, ← map_nsmul_piAntidiag_univ _ two_ne_zero, sum_map,
    Function.Embedding.coeFn_mk] using end_step hm' hA

/-- The **Marcinkiewicz-Zygmund inequality** for real-valued functions, with a slightly easier to
bound constant than `Real.marcinkiewicz_zygmund'`.

Note that `RCLike.marcinkiewicz_zygmund` is another version that works for both `ℝ` and `ℂ` at the
expense of a slightly worse constant. -/
theorem marcinkiewicz_zygmund (hm : m ≠ 0) (f : ι → ℝ) (hf : ∀ i, ∑ a in A ^^ n, f (a i) = 0) :
    ∑ a in A ^^ n, (∑ i, f (a i)) ^ (2 * m) ≤
      (4 * m) ^ m * n ^ (m - 1) * ∑ a in A ^^ n, ∑ i, f (a i) ^ (2 * m) := by
  obtain _ | m := m
  · simp at hm
  obtain rfl | hn := n.eq_zero_or_pos
  · simp
  calc
    ∑ a in A ^^ n, (∑ i, f (a i)) ^ (2 * (m + 1))
      ≤ (4 * ↑(m + 1)) ^ (m + 1) * ∑ a in A ^^ n, (∑ i, f (a i) ^ 2) ^ (m + 1) :=
      marcinkiewicz_zygmund' _ f hf
    _ ≤ (4 * ↑(m + 1)) ^ (m + 1) * (∑ a in A ^^ n, n ^ m * ∑ i, f (a i) ^ (2 * (m + 1))) := ?_
    _ ≤ (4 * ↑(m + 1)) ^ (m + 1) * n ^ m * ∑ a in A ^^ n, ∑ i, f (a i) ^ (2 * (m + 1)) := by
      simp_rw [mul_assoc, mul_sum]; rfl
  gcongr with a
  rw [← div_le_iff₀']
  have := pow_sum_div_card_le_sum_pow (f := fun i ↦ f (a i) ^ 2) (s := univ) (fun i _ ↦ ?_) m
  simpa only [Finset.card_fin, pow_mul] using this
  all_goals { positivity }

end Real

namespace RCLike
variable {𝕜 : Type*} [RCLike 𝕜]

/-- The **Marcinkiewicz-Zygmund inequality** for real- or complex-valued functions. -/
lemma marcinkiewicz_zygmund (hm : m ≠ 0) (f : ι → 𝕜) (hf : ∀ i, ∑ a in A ^^ n, f (a i) = 0) :
    ∑ a in A ^^ n, ‖∑ i, f (a i)‖ ^ (2 * m) ≤
      (8 * m) ^ m * n ^ (m - 1) * ∑ a in A ^^ n, ∑ i, ‖f (a i)‖ ^ (2 * m) := by
  let f₁ x : ℝ := re (f x)
  let f₂ x : ℝ := im (f x)
  let B := A ^^ n
  have hf₁ i : ∑ a in B, f₁ (a i) = 0 := by rw [← map_sum, hf, map_zero]
  have hf₂ i : ∑ a in B, f₂ (a i) = 0 := by rw [← map_sum, hf, map_zero]
  have h₁ := Real.marcinkiewicz_zygmund hm _ hf₁
  have h₂ := Real.marcinkiewicz_zygmund hm _ hf₂
  simp only [pow_mul, RCLike.norm_sq_eq_def]
  simp only [← sq, map_sum, map_sum]
  calc
    ∑ a in B, ((∑ i, re (f (a i))) ^ 2 + (∑ i, im (f (a i))) ^ 2) ^ m ≤
        ∑ a in B,
          2 ^ (m - 1) * (((∑ i, re (f (a i))) ^ 2) ^ m + ((∑ i, im (f (a i))) ^ 2) ^ m) := by
      gcongr with a; apply add_pow_le <;> positivity
    _ = 2 ^ (m - 1) * (∑ a in B, (∑ i, re (f (a i))) ^ (2 * m) +
          ∑ a in B, (∑ i, im (f (a i))) ^ (2 * m)) := by
      simp only [← sum_add_distrib, mul_sum, pow_mul]
    _ ≤ 2 ^ (m - 1) * ((4 * m) ^ m * n ^ (m - 1) *
          ∑ a in B, ∑ i, re (f (a i)) ^ (2 * m) + (4 * m) ^ m * n ^ (m - 1) *
          ∑ a in B, ∑ i, im (f (a i)) ^ (2 * m)) := by gcongr
    _ = 2 ^ (m - 1) * ((4 * m) ^ m * n ^ (m - 1) *
          ∑ a in B, ∑ i, (re (f (a i)) ^ (2 * m) + im (f (a i)) ^ (2 * m))) := by
      simp_rw [sum_add_distrib, mul_add]
    _ ≤ 2 ^ (m - 1) * ((4 * m) ^ m * n ^ (m - 1) *
          ∑ a in B, ∑ i, 2 * (re (f (a i)) ^ 2 + im (f (a i)) ^ 2) ^ m) := by
      simp_rw [pow_mul]; gcongr; apply pow_add_pow_le' <;> positivity
    _ = (8 * m) ^ m * n ^ (m - 1) * ∑ a in B, ∑ i, (re (f (a i)) ^ 2 + im (f (a i)) ^ 2) ^ m := by
      simp_rw [← mul_sum, show (8 : ℝ) = 2 * 4 by norm_num, mul_pow, ← pow_sub_one_mul hm (2 : ℝ)]
      ring

end RCLike
