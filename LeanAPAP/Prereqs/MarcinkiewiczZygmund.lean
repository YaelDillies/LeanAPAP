import Mathbin.Algebra.BigOperators.Order
import Mathbin.Analysis.MeanInequalitiesPow
import Mathbin.Data.Fin.Tuple.NatAntidiagonal
import Mathbin.Data.Fintype.BigOperators
import Project.Mathlib.Algebra.BigOperators.Basic
import Project.Mathlib.Algebra.GroupPower.Order
import Project.Mathlib.Analysis.MeanInequalitiesPow
import Project.Mathlib.GroupTheory.GroupAction.BigOperators
import Project.Prereqs.Multinomial

#align_import prereqs.marcinkiewicz_zygmund

open Finset Fintype Nat Real

open scoped BigOperators

variable {G : Type _} {A : Finset G} {m n : ℕ}

private theorem step_one (hA : A.Nonempty) (f : G → ℝ) (a : Fin n → G)
    (hf : ∀ i : Fin n, ∑ a in A^^n, f (a i) = 0) :
    |∑ i, f (a i)| ^ (m + 1) ≤ (∑ b in A^^n, |∑ i, (f (a i) - f (b i))| ^ (m + 1)) / A.card ^ n :=
  calc
    |∑ i, f (a i)| ^ (m + 1) = |∑ i, (f (a i) - (∑ b in A^^n, f (b i)) / (A^^n).card)| ^ (m + 1) :=
      by simp only [hf, sub_zero, zero_div]
    _ = |(∑ b in A^^n, ∑ i, (f (a i) - f (b i))) / (A^^n).card| ^ (m + 1) :=
      by
      simp only [sum_sub_distrib]
      rw [sum_const, sub_div, sum_comm, sum_div, nsmul_eq_mul, card_pi_finset, prod_const,
        Finset.card_fin, Nat.cast_pow, mul_div_cancel_left]
      exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Finset.card_pos.2 hA).ne')
    _ = |∑ b in A^^n, ∑ i, (f (a i) - f (b i))| ^ (m + 1) / (A^^n).card ^ (m + 1) := by
      rw [abs_div, div_pow, Nat.abs_cast]
    _ ≤ (∑ b in A^^n, |∑ i, (f (a i) - f (b i))|) ^ (m + 1) / (A^^n).card ^ (m + 1) :=
      (div_le_div_of_le (by positivity)
        (pow_le_pow_of_le_left (by positivity) (abv_sum_le_sum_abv _ _) _))
    _ = (∑ b in A^^n, |∑ i, (f (a i) - f (b i))|) ^ (m + 1) / (A^^n).card ^ m / (A^^n).card := by
      rw [div_div, ← pow_succ']
    _ ≤ _ := by
      rw [sum_div]
      refine'
        (div_le_div_of_le (by positivity) (Real.pow_sum_div_card_le_sum_pow (A^^n) m _)).trans _
      · intro i hi
        positivity
      rw [card_pi_finset, prod_const, Finset.card_fin, Nat.cast_pow, sum_div]

private theorem step_one' (hA : A.Nonempty) (f : G → ℝ) (hf : ∀ i : Fin n, ∑ a in A^^n, f (a i) = 0)
    (a : Fin n → G) :
    |∑ i, f (a i)| ^ m ≤ (∑ b in A^^n, |∑ i, (f (a i) - f (b i))| ^ m) / A.card ^ n :=
  by
  cases m
  · simp only [pow_zero, sum_const, prod_const, Nat.smul_one_eq_coe, Finset.card_fin,
      card_pi_finset, ← Nat.cast_pow]
    rw [div_self]
    rw [Nat.cast_ne_zero, ← pos_iff_ne_zero]
    exact pow_pos (Finset.card_pos.2 hA) _
  exact step_one hA f a hf

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
-- works with this
-- lemma step_two_aux' {β γ : Type*} [add_comm_monoid β] [comm_ring γ]
--   (f : (fin n → G) → (fin n → γ)) (ε : fin n → γ)
--   (hε : ∀ i : fin n, ε i = -1 ∨ ε i = 1) (g : (fin n → γ) → β) :
--   ∑ a b in A^^n, g (ε * (f a - f b)) = ∑ a b in A^^n, g (f a - f b) :=
-- feels like could generalise more...
-- the key point is that you combine the double sums into a single sum, and do a pair swap
-- when the corresponding ε is -1
-- but the order here is a bit subtle (ie this explanation is an oversimplification)
private theorem step_two_aux (A : Finset G) (f : G → ℝ) (ε : Fin n → ℝ)
    (hε : ε ∈ ({-1, 1} : Finset ℝ)^^n) (g : (Fin n → ℝ) → ℝ) :
    ∑ (a) (b) in A^^n, g (ε * (f ∘ a - f ∘ b)) = ∑ (a) (b) in A^^n, g (f ∘ a - f ∘ b) :=
  by
  rw [← sum_product', ← sum_product']
  let swapper : (Fin n → G) × (Fin n → G) → (Fin n → G) × (Fin n → G) :=
    by
    intro xy
    exact (fun i => if ε i = 1 then xy.1 i else xy.2 i, fun i => if ε i = 1 then xy.2 i else xy.1 i)
  have h₁ : ∀ a ∈ (A^^n) ×ˢ (A^^n), swapper a ∈ (A^^n) ×ˢ (A^^n) :=
    by
    intro a
    simp only [mem_product, and_imp, mem_pi_finset, ← forall_and]
    intro h i
    split_ifs
    · exact h i
    exact (h i).symm
  have h₂ : ∀ a ∈ (A^^n) ×ˢ (A^^n), swapper (swapper a) = a :=
    by
    intro a ha
    ext
    · simp only; split_ifs <;> rfl
    · simp only; split_ifs <;> rfl
  refine' sum_nbij' swapper h₁ _ swapper h₁ h₂ h₂
  · rintro ⟨a, b⟩ _
    congr with i : 1
    simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply]
    simp only [mem_pi_finset, mem_insert, mem_singleton] at hε 
    split_ifs
    · simp [h]
    rw [(hε i).resolve_right h]
    ring

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
private theorem step_two (hA : A.Nonempty) (f : G → ℝ) :
    ∑ (a) (b) in A^^n, (∑ i, (f (a i) - f (b i))) ^ (2 * m) =
      1 / 2 ^ n *
        ∑ ε in ({-1, 1} : Finset ℝ)^^n,
          ∑ (a) (b) in A^^n, (∑ i, ε i * (f (a i) - f (b i))) ^ (2 * m) :=
  by
  have :
    ∀ ε : Fin n → ℝ,
      ε ∈ ({-1, 1} : Finset ℝ)^^n →
        ∑ (a) (b) in A^^n, (∑ i, ε i * (f (a i) - f (b i))) ^ (2 * m) =
          ∑ (a) (b) in A^^n, (∑ i, (f (a i) - f (b i))) ^ (2 * m) :=
    by
    intro ε hε
    exact step_two_aux A f _ hε fun z : Fin n → ℝ => univ.sum z ^ (2 * m)
  rw [sum_congr rfl this, sum_const, card_pi_finset, prod_const, Finset.card_fin,
    card_insert_of_not_mem, card_singleton, ← bit0, nsmul_eq_mul, Nat.cast_pow, Nat.cast_two,
    one_div, inv_mul_cancel_left₀]
  · positivity
  norm_num

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
private theorem step_three (f : G → ℝ) :
    ∑ ε in ({-1, 1} : Finset ℝ)^^n, ∑ (a) (b) in A^^n, (∑ i, ε i * (f (a i) - f (b i))) ^ (2 * m) =
      ∑ (a) (b) in A^^n,
        ∑ k in cut (univ : Finset (Fin n)) (2 * m),
          (multinomial univ k * ∏ t, (f (a t) - f (b t)) ^ k t) *
            ∑ ε in ({-1, 1} : Finset ℝ)^^n, ∏ t, ε t ^ k t :=
  by
  simp only [@sum_comm _ _ (Fin n → ℝ) _ _ (A^^n), ← Complex.abs_pow, multinomial_expansion']
  refine' sum_congr rfl fun a ha => _
  refine' sum_congr rfl fun b hb => _
  simp only [mul_pow, prod_mul_distrib, @sum_comm _ _ (Fin n → ℝ), ← mul_sum, ← sum_mul]
  refine' sum_congr rfl fun k hk => _
  rw [← mul_assoc, mul_right_comm]

private theorem step_four {k : Fin n → ℕ} :
    ∑ ε in ({-1, 1} : Finset ℝ)^^n, ∏ t, ε t ^ k t = 2 ^ n * ite (∀ i, Even (k i)) 1 0 :=
  by
  have := sum_prod_pi_finset ({-1, 1} : Finset ℝ) fun i fi => fi ^ k i
  dsimp at this 
  rw [pi_finset_const, this, ← Fintype.prod_boole]
  have : (2 : ℝ) ^ n = ∏ i : Fin n, 2 := by simp
  rw [this, ← prod_mul_distrib]
  refine' prod_congr rfl fun t ht => _
  rw [sum_pair, one_pow, mul_boole]
  swap
  · norm_num
  split_ifs
  · rw [h.neg_one_pow, bit0]
  rw [← Nat.odd_iff_not_even] at h 
  rw [h.neg_one_pow]
  simp

-- double_multinomial
private theorem step_six {f : G → ℝ} {a b : Fin n → G} :
    ∑ k : Fin n → ℕ in cut univ m,
        (multinomial univ fun a => 2 * k a : ℝ) * ∏ i : Fin n, (f (a i) - f (b i)) ^ (2 * k i) ≤
      m ^ m * (∑ i : Fin n, (f (a i) - f (b i)) ^ 2) ^ m :=
  by
  rw [multinomial_expansion', mul_sum]
  convert sum_le_sum fun k hk => _
  rw [mem_cut] at hk 
  simp only [← mul_assoc, pow_mul]
  refine' mul_le_mul_of_nonneg_right _ (prod_nonneg fun i hi => by positivity)
  norm_cast
  refine' double_multinomial.trans _
  rw [hk.1]

private theorem step_seven {f : G → ℝ} {a b : Fin n → G} :
    ↑m ^ m * (∑ i : Fin n, (f (a i) - f (b i)) ^ 2) ^ m ≤
      m ^ m * 2 ^ m * (∑ i : Fin n, (f (a i) ^ 2 + f (b i) ^ 2)) ^ m :=
  by
  rw [← mul_pow, ← mul_pow, ← mul_pow]
  refine' pow_le_pow_of_le_left _ _ _
  · exact mul_nonneg (Nat.cast_nonneg _) (sum_nonneg fun i hi => by positivity)
  rw [mul_assoc]
  refine' mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [mul_sum]
  refine' sum_le_sum fun i hi => _
  rw [sub_eq_add_neg]
  refine' add_sq_le.trans_eq _
  simp

private theorem step_eight {f : G → ℝ} {a b : Fin n → G} :
    (m : ℝ) ^ m * 2 ^ m * (∑ i : Fin n, (f (a i) ^ 2 + f (b i) ^ 2)) ^ m ≤
      (m : ℝ) ^ m * 2 ^ (m + (m - 1)) *
        ((∑ i : Fin n, f (a i) ^ 2) ^ m + (∑ i : Fin n, f (b i) ^ 2) ^ m) :=
  by
  rw [pow_add, ← mul_assoc _ _ ((2 : ℝ) ^ _), mul_assoc _ ((2 : ℝ) ^ (m - 1))]
  refine' mul_le_mul_of_nonneg_left _ (by positivity)
  rw [sum_add_distrib]
  refine' add_pow_le _ _ m <;> exact sum_nonneg fun i hi => by positivity

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (a b) -/
private theorem end_step {f : G → ℝ} (hm : 1 ≤ m) (hA : A.Nonempty) :
    (∑ (a) (b) in A^^n,
          ∑ k : Fin n → ℕ in cut univ m,
            ↑(multinomial univ fun i => 2 * k i) * ∏ t : Fin n, (f (a t) - f (b t)) ^ (2 * k t)) /
        A.card ^ n ≤
      (4 * m) ^ m * ∑ a in A^^n, (∑ i, f (a i) ^ 2) ^ m :=
  calc
    (∑ (a) (b) in A^^n,
            ∑ k : Fin n → ℕ in cut univ m,
              (multinomial univ fun i => 2 * k i : ℝ) * ∏ t, (f (a t) - f (b t)) ^ (2 * k t)) /
          A.card ^ n ≤
        (∑ (a) (b) in A^^n, (m : ℝ) ^ m * 2 ^ m * (∑ i : Fin n, (f (a i) ^ 2 + f (b i) ^ 2)) ^ m) /
          A.card ^ n :=
      div_le_div_of_le (pow_nonneg (Nat.cast_nonneg _) _)
        (by
          refine' sum_le_sum fun a ha => _
          refine' sum_le_sum fun b hb => _
          exact step_six.trans step_seven)
    _ ≤
        (∑ (a) (b) in A^^n,
            (m : ℝ) ^ m * 2 ^ (m + (m - 1)) *
              ((∑ i : Fin n, f (a i) ^ 2) ^ m + (∑ i : Fin n, f (b i) ^ 2) ^ m)) /
          A.card ^ n :=
      (div_le_div_of_le (pow_nonneg (Nat.cast_nonneg _) _)
        (by
          refine' sum_le_sum fun a ha => _
          refine' sum_le_sum fun b hb => _
          refine' step_eight))
    _ = _ := by
      simp only [mul_add, sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
      rw [← mul_add, ← two_mul, ← mul_assoc, mul_assoc _ (2 ^ _ : ℝ), ← pow_succ', add_assoc,
        Nat.sub_add_cancel hm, card_pi_finset, prod_const, Finset.card_fin, mul_div_assoc, ←
        Nat.cast_pow A.card, mul_div_cancel_left]
      swap
      · rw [Nat.cast_ne_zero, ← pos_iff_ne_zero]
        exact pow_pos (Finset.card_pos.2 hA) _
      rw [← two_mul, pow_mul, ← mul_pow, mul_comm (m : ℝ), sq, ← bit0_eq_two_mul]

theorem basic_marcinkiewicz_zygmund (f : G → ℝ) (hf : ∀ i : Fin n, ∑ a in A^^n, f (a i) = 0) :
    ∑ a in A^^n, |∑ i, f (a i)| ^ (2 * m) ≤ (4 * m) ^ m * ∑ a in A^^n, (∑ i, |f (a i)| ^ 2) ^ m :=
  by
  rcases m.eq_zero_or_pos with (rfl | hm)
  · simp
  have hm' : 1 ≤ m := by rwa [Nat.succ_le_iff]
  rcases A.eq_empty_or_nonempty with (rfl | hA)
  · cases n
    · cases m <;> simp
    · rw [pi_finset_const, pi_finset_empty, Finset.sum_empty]
      cases m <;> simp
  refine' (sum_le_sum fun a (_ : a ∈ A^^n) => @step_one' _ _ _ _ hA f hf a).trans _
  rw [← sum_div]
  simp only [pow_mul, sq_abs]
  simp only [← pow_mul]
  rw [step_two hA, step_three, mul_comm, mul_one_div, div_div]
  simp only [step_four, mul_ite, MulZeroClass.mul_zero, mul_one]
  simp only [← sum_filter, ← sum_mul]
  rw [mul_comm, mul_div_mul_left]
  swap; · positivity
  simp only [even_iff_two_dvd, ← map_nsmul_cut_univ _ two_ne_zero, sum_map,
    Function.Embedding.coeFn_mk]
  exact end_step hm' hA

-- works for m = 0 but the statement is weird, and there might be a useful statement for that case
theorem other_marcinkiewicz_zygmund (f : G → ℝ) (hm : m ≠ 0)
    (hf : ∀ i : Fin n, ∑ a in A^^n, f (a i) = 0) :
    ∑ a in A^^n, |∑ i, f (a i)| ^ (2 * m) ≤
      (4 * m) ^ m * n ^ (m - 1) * ∑ a in A^^n, ∑ i, |f (a i)| ^ (2 * m) :=
  by
  cases m
  · simpa using hm
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  refine' (basic_marcinkiewicz_zygmund f hf).trans _
  rw [mul_assoc]
  refine' mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Nat.succ_sub_one]
  simp only [pow_mul, mul_sum]
  refine' sum_le_sum fun a ha => _
  rw [← mul_sum]
  refine' (mul_le_mul_of_nonneg_left (Real.pow_sum_div_card_le_sum_pow _ _ _) _).trans' _
  · intro i hi
    positivity
  · positivity
  rw [Finset.card_fin, mul_div_cancel']
  positivity

theorem other_marcinkiewicz_zygmund' (f : G → ℝ) (hm : m ≠ 0)
    (hf : ∀ i : Fin n, ∑ a in A^^n, f (a i) = 0) :
    ∑ a in A^^n, (∑ i, f (a i)) ^ (2 * m) ≤
      (4 * m) ^ m * n ^ (m - 1) * ∑ a in A^^n, ∑ i, f (a i) ^ (2 * m) :=
  by simpa only [pow_mul, sq_abs] using other_marcinkiewicz_zygmund f hm hf

theorem complex_marcinkiewicz_zygmund (f : G → ℂ) (hm : m ≠ 0)
    (hf : ∀ i : Fin n, ∑ a in A^^n, f (a i) = 0) :
    ∑ a in A^^n, ‖∑ i, f (a i)‖ ^ (2 * m) ≤
      (8 * m) ^ m * n ^ (m - 1) * ∑ a in A^^n, ∑ i, ‖f (a i)‖ ^ (2 * m) :=
  by
  let f₁ : G → ℝ := fun x => (f x).re
  let f₂ : G → ℝ := fun x => (f x).im
  have hf₁ : ∀ i, ∑ a in A^^n, f₁ (a i) = 0 := by intro i;
    rw [← Complex.re_sum, hf, Complex.zero_re]
  have hf₂ : ∀ i, ∑ a in A^^n, f₂ (a i) = 0 := by intro i;
    rw [← Complex.im_sum, hf, Complex.zero_im]
  have h₁ := other_marcinkiewicz_zygmund' _ hm hf₁
  have h₂ := other_marcinkiewicz_zygmund' _ hm hf₂
  simp only [pow_mul, Complex.norm_eq_abs, Complex.sq_abs, Complex.normSq_apply]
  simp only [← sq, Complex.re_sum, Complex.im_sum]
  calc
    ∑ a in A^^n, ((∑ i, (f (a i)).re) ^ 2 + (∑ i, (f (a i)).im) ^ 2) ^ m ≤
        ∑ a in A^^n,
          2 ^ (m - 1) * (((∑ i, (f (a i)).re) ^ 2) ^ m + ((∑ i, (f (a i)).im) ^ 2) ^ m) :=
      _
    _ =
        2 ^ (m - 1) *
          ∑ a in A^^n, ((∑ i, (f (a i)).re) ^ (2 * m) + (∑ i, (f (a i)).im) ^ (2 * m)) :=
      _
    _ ≤
        2 ^ (m - 1) * (4 * m) ^ m * n ^ (m - 1) *
          ∑ a in A^^n, ∑ i, ((f (a i)).re ^ (2 * m) + (f (a i)).im ^ (2 * m)) :=
      _
    _ ≤ (8 * m) ^ m * n ^ (m - 1) * ∑ a in A^^n, ∑ i, ((f (a i)).re ^ 2 + (f (a i)).im ^ 2) ^ m := _
  · exact sum_le_sum fun a ha => add_pow_le (sq_nonneg _) (sq_nonneg _) m
  · simp only [mul_sum, pow_mul]
  · rw [mul_assoc, mul_assoc, sum_add_distrib]
    refine' mul_le_mul_of_nonneg_left _ _
    swap
    · positivity
    simp only [sum_add_distrib, mul_add, ← mul_assoc]
    exact add_le_add h₁ h₂
  simp only [mul_sum]
  refine' sum_le_sum fun a ha => _
  refine' sum_le_sum fun i hi => _
  rw [pow_mul, pow_mul]
  refine'
    (mul_le_mul_of_nonneg_left (pow_add_pow_le' (sq_nonneg (f (a i)).re) <| sq_nonneg (f (a i)).im)
          _).trans_eq
      _
  · positivity
  rw [mul_assoc (2 ^ _ : ℝ), mul_mul_mul_comm, ← pow_succ', Nat.sub_add_cancel, ← mul_assoc, ←
    mul_assoc, ← mul_pow, ← mul_assoc, ← bit0_eq_two_mul]
  rwa [succ_le_iff, pos_iff_ne_zero]

