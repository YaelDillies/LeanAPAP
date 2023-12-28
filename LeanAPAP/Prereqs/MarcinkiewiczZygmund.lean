import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Data.Fintype.BigOperators
import LeanAPAP.Mathlib.Algebra.BigOperators.Basic
import LeanAPAP.Mathlib.Algebra.BigOperators.Order
import LeanAPAP.Mathlib.Algebra.GroupPower.Order
import LeanAPAP.Mathlib.Analysis.MeanInequalitiesPow
import LeanAPAP.Mathlib.GroupTheory.GroupAction.BigOperators
import LeanAPAP.Prereqs.Multinomial

open Finset Fintype Nat Real
open scoped BigOperators

variable {G : Type*} {A : Finset G} {m n : ℕ}

private lemma step_one (hA : A.Nonempty) (f : G → ℝ) (a : Fin n → G)
    (hf : ∀ i : Fin n, ∑ a in A^^n, f (a i) = 0) :
    |∑ i, f (a i)| ^ (m + 1) ≤ (∑ b in A^^n, |∑ i, (f (a i) - f (b i))| ^ (m + 1)) / A.card ^ n :=
  calc
    |∑ i, f (a i)| ^ (m + 1)
      = |∑ i, (f (a i) - (∑ b in A^^n, f (b i)) / (A^^n).card)| ^ (m + 1) := by
        simp only [hf, sub_zero, zero_div]
    _ = |(∑ b in A^^n, ∑ i, (f (a i) - f (b i))) / (A^^n).card| ^ (m + 1) := by
        simp only [sum_sub_distrib]
        rw [sum_const, sub_div, sum_comm, sum_div, nsmul_eq_mul, card_piFinsetConst, Nat.cast_pow,
          mul_div_cancel_left]
        exact pow_ne_zero _ $ Nat.cast_ne_zero.2 hA.card_pos.ne'
    _ = |∑ b in A^^n, ∑ i, (f (a i) - f (b i))| ^ (m + 1) / (A^^n).card ^ (m + 1) := by
      rw [abs_div, div_pow, Nat.abs_cast]
    _ ≤ (∑ b in A^^n, |∑ i, (f (a i) - f (b i))|) ^ (m + 1) / (A^^n).card ^ (m + 1) :=
      (div_le_div_of_le (by positivity)
        (pow_le_pow_left (by positivity) (abv_sum_le_sum_abv _ _) _))
    _ = (∑ b in A^^n, |∑ i, (f (a i) - f (b i))|) ^ (m + 1) / (A^^n).card ^ m / (A^^n).card := by
      rw [div_div, ←_root_.pow_succ']
    _ ≤ _ := by simpa using div_le_div_of_le (by positivity)
                  (Real.pow_sum_div_card_le_sum_pow (A^^n) m fun i _ ↦ by positivity)

private lemma step_one' (hA : A.Nonempty) (f : G → ℝ) (hf : ∀ i : Fin n, ∑ a in A^^n, f (a i) = 0)
    (a : Fin n → G) :
    |∑ i, f (a i)| ^ m ≤ (∑ b in A^^n, |∑ i, (f (a i) - f (b i))| ^ m) / A.card ^ n := by
  cases m
  · simp only [_root_.pow_zero, sum_const, prod_const, Nat.smul_one_eq_coe, Finset.card_fin,
      card_piFinset, ←Nat.cast_pow]
    rw [div_self]
    rw [Nat.cast_ne_zero, ←pos_iff_ne_zero]
    exact pow_pos (Finset.card_pos.2 hA) _
  exact step_one hA f a hf

-- works with this
-- lemma step_two_aux' {β γ : Type*} [AddCommMonoid β] [CommRing γ]
--   (f : (Fin n → G) → (Fin n → γ)) (ε : Fin n → γ)
--   (hε : ∀ i : Fin n, ε i = -1 ∨ ε i = 1) (g : (Fin n → γ) → β) :
--   ∑ a b in A^^n, g (ε * (f a - f b)) = ∑ a b in A^^n, g (f a - f b) :=
-- feels like could generalise more...
-- the key point is that you combine the double sums into a single sum, and do a pair swap
-- when the corresponding ε is -1
-- but the order here is a bit subtle (ie this explanation is an oversimplification)
private lemma step_two_aux (A : Finset G) (f : G → ℝ) (ε : Fin n → ℝ)
    (hε : ε ∈ ({-1, 1} : Finset ℝ)^^n) (g : (Fin n → ℝ) → ℝ) :
    ∑ a in A^^n, ∑ b in A^^n, g (ε * (f ∘ a - f ∘ b)) =
      ∑ a in A^^n, ∑ b in A^^n, g (f ∘ a - f ∘ b) := by
  rw [←sum_product', ←sum_product']
  let swapper : (Fin n → G) × (Fin n → G) → (Fin n → G) × (Fin n → G) := by
    intro xy
    exact (fun i ↦ if ε i = 1 then xy.1 i else xy.2 i, fun i ↦ if ε i = 1 then xy.2 i else xy.1 i)
  have h₁ : ∀ a ∈ (A^^n) ×ˢ (A^^n), swapper a ∈ (A^^n) ×ˢ (A^^n) := by
    intro a
    simp only [mem_product, and_imp, mem_piFinset, ←forall_and]
    intro h i
    split_ifs
    · exact h i
    exact (h i).symm
  have h₂ : ∀ a ∈ (A^^n) ×ˢ (A^^n), swapper (swapper a) = a := fun a _ ↦ by
    ext <;> simp only <;> split_ifs <;> rfl
  refine' sum_nbij' swapper swapper h₁ h₁ h₂ h₂ _
  · rintro ⟨a, b⟩ _
    congr with i : 1
    simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply]
    simp only [mem_piFinset, mem_insert, mem_singleton] at hε
    split_ifs with h
    · simp [h]
    rw [(hε i).resolve_right h]
    ring

private lemma step_two (f : G → ℝ) :
    ∑ a in A^^n, ∑ b in A^^n, (∑ i, (f (a i) - f (b i))) ^ (2 * m) =
      2⁻¹ ^ n * ∑ ε in ({-1, 1} : Finset ℝ)^^n,
        ∑ a in A^^n, ∑ b in A^^n, (∑ i, ε i * (f (a i) - f (b i))) ^ (2 * m) := by
  have : ∀ ε ∈ ({-1, 1} : Finset ℝ)^^n,
    ∑ a in A^^n, ∑ b in A^^n, (∑ i, ε i * (f (a i) - f (b i))) ^ (2 * m) =
      ∑ a in A^^n, ∑ b in A^^n, (∑ i, (f (a i) - f (b i))) ^ (2 * m) :=
    fun ε hε ↦ step_two_aux A f _ hε fun z : Fin n → ℝ ↦ univ.sum z ^ (2 * m)
  rw [Finset.sum_congr rfl this, sum_const, card_piFinsetConst, card_doubleton, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_two, inv_pow, inv_mul_cancel_left₀]
  · positivity
  · norm_num

private lemma step_three (f : G → ℝ) :
    ∑ ε in ({-1, 1} : Finset ℝ)^^n,
      ∑ a in A^^n, ∑ b in A^^n, (∑ i, ε i * (f (a i) - f (b i))) ^ (2 * m) =
      ∑ a in A^^n, ∑ b in A^^n, ∑ k in cut univ (2 * m),
          (multinomial univ k * ∏ t, (f (a t) - f (b t)) ^ k t) *
            ∑ ε in ({-1, 1} : Finset ℝ)^^n, ∏ t, ε t ^ k t := by
  simp only [@sum_comm _ _ (Fin n → ℝ) _ _ (A^^n), ←Complex.abs_pow, multinomial_expansion']
  refine' sum_congr rfl fun a _ ↦ _
  refine' sum_congr rfl fun b _ ↦ _
  simp only [mul_pow, prod_mul_distrib, @sum_comm _ _ (Fin n → ℝ), ←mul_sum, ←sum_mul]
  refine' sum_congr rfl fun k _ ↦ _
  rw [←mul_assoc, mul_right_comm]

private lemma step_four {k : Fin n → ℕ} :
    ∑ ε in ({-1, 1} : Finset ℝ)^^n, ∏ t, ε t ^ k t = 2 ^ n * ite (∀ i, Even (k i)) 1 0 := by
  have := sum_prod_piFinset ({-1, 1} : Finset ℝ) fun i fi ↦ fi ^ k i
  rw [piFinsetConst, this, ←Fintype.prod_boole]
  have : (2 : ℝ) ^ n = ∏ i : Fin n, 2 := by simp
  rw [this, ←prod_mul_distrib]
  refine' prod_congr rfl fun t _ ↦ _
  rw [sum_pair, one_pow, mul_boole]
  swap
  · norm_num
  split_ifs with h
  · rw [h.neg_one_pow, one_add_one_eq_two]
  rw [←Nat.odd_iff_not_even] at h
  rw [h.neg_one_pow]
  simp

-- double_multinomial
private lemma step_six {f : G → ℝ} {a b : Fin n → G} :
    ∑ k : Fin n → ℕ in cut univ m,
        (multinomial univ fun a ↦ 2 * k a : ℝ) * ∏ i : Fin n, (f (a i) - f (b i)) ^ (2 * k i) ≤
      m ^ m * (∑ i : Fin n, (f (a i) - f (b i)) ^ 2) ^ m := by
  rw [multinomial_expansion', mul_sum]
  convert sum_le_sum fun k hk ↦ _
  rw [mem_cut] at hk
  simp only [←mul_assoc, pow_mul]
  refine' mul_le_mul_of_nonneg_right _ (prod_nonneg fun i _ ↦ by positivity)
  norm_cast
  refine' double_multinomial.trans _
  rw [hk.1]

private lemma step_seven {f : G → ℝ} {a b : Fin n → G} :
    m ^ m * (∑ i : Fin n, (f (a i) - f (b i)) ^ 2 : ℝ) ^ m ≤
      m ^ m * 2 ^ m * (∑ i : Fin n, (f (a i) ^ 2 + f (b i) ^ 2)) ^ m := by
  rw [←mul_pow, ←mul_pow, ←mul_pow]
  refine' pow_le_pow_left _ _ _
  · positivity
  rw [mul_assoc]
  refine' mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [mul_sum]
  refine' sum_le_sum fun i _ ↦ _
  rw [sub_eq_add_neg]
  refine' add_sq_le.trans_eq _
  simp

private lemma step_eight {f : G → ℝ} {a b : Fin n → G} :
    m ^ m * 2 ^ m * (∑ i : Fin n, (f (a i) ^ 2 + f (b i) ^ 2) : ℝ) ^ m ≤
      m ^ m * 2 ^ (m + (m - 1)) *
        ((∑ i : Fin n, f (a i) ^ 2) ^ m + (∑ i : Fin n, f (b i) ^ 2) ^ m) := by
  rw [pow_add, ←mul_assoc _ _ (2 ^ _), mul_assoc _ (2 ^ (m - 1))]
  refine' mul_le_mul_of_nonneg_left _ (by positivity)
  rw [sum_add_distrib]
  refine' add_pow_le _ _ m <;> positivity

private lemma end_step {f : G → ℝ} (hm : 1 ≤ m) (hA : A.Nonempty) :
    (∑ a in A^^n, ∑ b in A^^n, ∑ k : Fin n → ℕ in cut univ m,
      ↑(multinomial univ fun i ↦ 2 * k i) * ∏ t : Fin n, (f (a t) - f (b t)) ^ (2 * k t)) /
        A.card ^ n ≤ (4 * m) ^ m * ∑ a in A^^n, (∑ i, f (a i) ^ 2) ^ m :=
  calc
    (∑ a in A^^n, ∑ b in A^^n,
            ∑ k : Fin n → ℕ in cut univ m,
              (multinomial univ fun i ↦ 2 * k i : ℝ) * ∏ t, (f (a t) - f (b t)) ^ (2 * k t)) /
          A.card ^ n
      ≤ (∑ a in A^^n, ∑ b in A^^n, m ^ m *
          2 ^ m * (∑ i : Fin n, (f (a i) ^ 2 + f (b i) ^ 2)) ^ m : ℝ) / A.card ^ n :=
        div_le_div_of_le (by positivity) $ sum_le_sum fun a _ ↦ sum_le_sum fun b _ ↦
          step_six.trans step_seven
    _ ≤ (∑ a in A^^n, ∑ b in A^^n, m ^ m * 2 ^ (m + (m - 1)) *
          ((∑ i : Fin n, f (a i) ^ 2) ^ m + (∑ i : Fin n, f (b i) ^ 2) ^ m) : ℝ) / A.card ^ n :=
        div_le_div_of_le (by positivity) $ sum_le_sum fun a _ ↦ sum_le_sum fun b _ ↦ step_eight
    _ = _ := by
      simp only [mul_add, sum_add_distrib, sum_const, nsmul_eq_mul, ←mul_sum]
      rw [←mul_add, ←two_mul, ←mul_assoc 2, ←mul_assoc 2, mul_right_comm 2, ←_root_.pow_succ,
        add_assoc, Nat.sub_add_cancel hm, pow_add, ←mul_pow, ←mul_pow, card_piFinsetConst,
        Nat.cast_pow, mul_div_cancel_left]
      norm_num
      · have := hA.card_pos
        positivity

lemma basic_marcinkiewicz_zygmund (f : G → ℝ) (hf : ∀ i : Fin n, ∑ a in A^^n, f (a i) = 0) :
    ∑ a in A^^n, |∑ i, f (a i)| ^ (2 * m) ≤
      (4 * m) ^ m * ∑ a in A^^n, (∑ i, |f (a i)| ^ 2) ^ m := by
  obtain rfl | hm := m.eq_zero_or_pos
  · simp
  have hm' : 1 ≤ m := by rwa [Nat.succ_le_iff]
  rcases A.eq_empty_or_nonempty with (rfl | hA)
  · cases n
    · cases m <;> simp
    · rw [piFinsetConst, piFinset_empty, Finset.sum_empty]
      cases m <;> simp
  refine' (sum_le_sum fun a (_ : a ∈ A^^n) ↦ @step_one' _ _ _ _ hA f hf a).trans _
  rw [←sum_div]
  simp only [pow_mul, sq_abs]
  simp only [←pow_mul]
  rw [step_two, step_three, mul_comm, inv_pow, ←div_eq_mul_inv, div_div]
  simp only [step_four, mul_ite, mul_zero, mul_one]
  simp only [←sum_filter, ←sum_mul]
  rw [mul_comm, mul_div_mul_left]
  swap; · positivity
  simp only [even_iff_two_dvd, ←map_nsmul_cut_univ _ two_ne_zero, sum_map,
    Function.Embedding.coeFn_mk]
  exact end_step hm' hA

-- works for m = 0 but the statement is weird, and there might be a useful statement for that case
lemma other_marcinkiewicz_zygmund (f : G → ℝ) (hm : m ≠ 0)
    (hf : ∀ i : Fin n, ∑ a in A^^n, f (a i) = 0) :
    ∑ a in A^^n, |∑ i, f (a i)| ^ (2 * m) ≤
      (4 * m) ^ m * (n : ℝ) ^ (m - 1) * ∑ a in A^^n, ∑ i, |f (a i)| ^ (2 * m) := by
  obtain _ | m := m
  · simp at hm
  obtain rfl | hn := n.eq_zero_or_pos
  · simp
  refine' (basic_marcinkiewicz_zygmund f hf).trans _
  rw [mul_assoc]
  refine' mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Nat.succ_sub_one]
  simp only [pow_mul, mul_sum]
  refine' sum_le_sum fun a _ ↦ _
  rw [←mul_sum, ←div_le_iff']
  have := Real.pow_sum_div_card_le_sum_pow (f := fun i ↦ |f (a i)| ^ 2) univ m fun i _ ↦ ?_
  simpa only [Finset.card_fin] using this
  all_goals { positivity }

lemma other_marcinkiewicz_zygmund' (f : G → ℝ) (hm : m ≠ 0)
    (hf : ∀ i : Fin n, ∑ a in A^^n, f (a i) = 0) :
    ∑ a in A^^n, (∑ i, f (a i)) ^ (2 * m) ≤
      (4 * m) ^ m * (n : ℝ) ^ (m - 1) * ∑ a in A^^n, ∑ i, f (a i) ^ (2 * m) := by
  simpa only [pow_mul, sq_abs] using other_marcinkiewicz_zygmund f hm hf

lemma complex_marcinkiewicz_zygmund (f : G → ℂ) (hm : m ≠ 0)
    (hf : ∀ i : Fin n, ∑ a in A^^n, f (a i) = 0) :
    ∑ a in A^^n, ‖∑ i, f (a i)‖ ^ (2 * m) ≤
      (8 * m) ^ m * n ^ (m - 1) * ∑ a in A^^n, ∑ i, ‖f (a i)‖ ^ (2 * m) := by
  let f₁ : G → ℝ := fun x ↦ (f x).re
  let f₂ : G → ℝ := fun x ↦ (f x).im
  have hf₁ : ∀ i, ∑ a in A^^n, f₁ (a i) = 0 := fun i ↦ by rw [←Complex.re_sum, hf, Complex.zero_re]
  have hf₂ : ∀ i, ∑ a in A^^n, f₂ (a i) = 0 := fun i ↦ by rw [←Complex.im_sum, hf, Complex.zero_im]
  have h₁ := other_marcinkiewicz_zygmund' _ hm hf₁
  have h₂ := other_marcinkiewicz_zygmund' _ hm hf₂
  simp only [pow_mul, Complex.norm_eq_abs, Complex.sq_abs, Complex.normSq_apply]
  simp only [←sq, Complex.re_sum, Complex.im_sum]
  calc
    ∑ a in A^^n, ((∑ i, (f (a i)).re) ^ 2 + (∑ i, (f (a i)).im) ^ 2) ^ m ≤
        ∑ a in A^^n,
          2 ^ (m - 1) * (((∑ i, (f (a i)).re) ^ 2) ^ m + ((∑ i, (f (a i)).im) ^ 2) ^ m) := ?_
    _ = 2 ^ (m - 1) *
          ∑ a in A^^n, ((∑ i, (f (a i)).re) ^ (2 * m) + (∑ i, (f (a i)).im) ^ (2 * m)) := ?_
    _ ≤ 2 ^ (m - 1) * (4 * m) ^ m * n ^ (m - 1) *
          ∑ a in A^^n, ∑ i, ((f (a i)).re ^ (2 * m) + (f (a i)).im ^ (2 * m)) := ?_
    _ ≤ (8 * m) ^ m * n ^ (m - 1) * ∑ a in A^^n, ∑ i, ((f (a i)).re ^ 2 + (f (a i)).im ^ 2) ^ m :=
        ?_
  · exact sum_le_sum fun a _ ↦ add_pow_le (sq_nonneg _) (sq_nonneg _) m
  · simp only [mul_sum, pow_mul]
  · rw [mul_assoc, mul_assoc, sum_add_distrib]
    refine' mul_le_mul_of_nonneg_left _ _
    swap
    · positivity
    simp only [sum_add_distrib, mul_add, ←mul_assoc]
    exact add_le_add h₁ h₂
  simp only [mul_sum]
  refine' sum_le_sum fun a _ ↦ _
  refine' sum_le_sum fun i _ ↦ _
  rw [pow_mul, pow_mul]
  refine' (mul_le_mul_of_nonneg_left (pow_add_pow_le' (sq_nonneg (f (a i)).re) $
    sq_nonneg (f (a i)).im) _).trans_eq _
  · positivity
  rw [mul_assoc (2 ^ _ : ℝ), mul_mul_mul_comm, ←_root_.pow_succ', Nat.sub_add_cancel, ←mul_assoc,
    ←mul_assoc, ←mul_pow, ←mul_assoc]
  norm_num
  rwa [succ_le_iff, pos_iff_ne_zero]
