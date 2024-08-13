import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Data.Real.StarOrdered
import LeanAPAP.Prereqs.Convolution.Order

open BigOperators Finset
open scoped ComplexConjugate Pointwise Combinatorics.Additive

section
variable {α : Type*} [DecidableEq α] {H : Finset (α × α)} {A B X : Finset α} {x : α}

private noncomputable def oneOfPair (H : Finset (α × α)) (X : Finset α) : Finset α :=
  X.filter fun x ↦ (3 / 4 : ℝ) * X.card ≤ (H.filter fun yz ↦ yz.1 = x).card

private lemma oneOfPair_mem :
    x ∈ oneOfPair H X ↔ x ∈ X ∧ (3 / 4 : ℝ) * X.card ≤ (H.filter fun yz ↦ yz.1 = x).card :=
  mem_filter

private lemma oneOfPair_mem' (hH : H ⊆ X ×ˢ X) :
    (H.filter fun yz ↦ yz.1 = x).card = (X.filter fun c ↦ (x, c) ∈ H).card := by
  refine card_nbij' Prod.snd (fun c ↦ (x, c)) ?_ (by simp) (by aesop) (by simp)
  simp (config := { contextual := true }) only [eq_comm, Prod.forall, mem_filter, and_imp, and_true]
  exact fun a b hab _ ↦ (mem_product.1 (hH hab)).2

private lemma oneOfPair_bound_one :
    ∑ x in X \ oneOfPair H X, ((H.filter (fun xy ↦ xy.1 = x)).card : ℝ) ≤ (3 / 4) * X.card ^ 2 :=
  calc _ ≤ ∑ _x in X \ oneOfPair H X, (3 / 4 : ℝ) * X.card := sum_le_sum fun i hi ↦ by
          simp only [oneOfPair, ←filter_not, Prod.forall, not_le, not_lt, mem_filter] at hi
          exact hi.2.le
       _ = (X \ oneOfPair H X).card * ((3 / 4 : ℝ) * X.card) := by simp
       _ ≤ X.card * ((3 / 4 : ℝ) * X.card) := by gcongr; exact sdiff_subset
       _ = _ := by ring

private lemma oneOfPair_bound_two (hH : H ⊆ X ×ˢ X) (Hcard : (7 / 8 : ℝ) * X.card ^ 2 ≤ H.card) :
    (1 / 8 : ℝ) * X.card ^ 2 ≤ X.card * (oneOfPair H X).card :=
  calc _ = (7 / 8 : ℝ) * X.card ^ 2 - 3 / 4 * X.card ^ 2 := by ring
       _ ≤ H.card - (3 / 4 : ℝ) * X.card ^ 2 := by linarith
       _ ≤ H.card - ∑ x in X \ oneOfPair H X, ↑(H.filter (fun xy ↦ xy.1 = x)).card :=
          sub_le_sub_left oneOfPair_bound_one _
       _ = (H.card - ∑ x in X, ↑(H.filter (fun xy ↦ xy.1 = x)).card) +
              ∑ x in oneOfPair H X, ↑(H.filter (fun xy ↦ xy.1 = x)).card := by
          rw [sum_sdiff_eq_sub, sub_add]
          exact filter_subset _ _
       _ = ∑ x in oneOfPair H X, ↑(H.filter (fun xy ↦ xy.1 = x)).card := by
          rw [add_left_eq_self, sub_eq_zero, ←Nat.cast_sum, Nat.cast_inj,
            ←card_eq_sum_card_fiberwise]
          intro x hx
          exact (mem_product.1 (hH hx)).1
       _ ≤ ∑ _x in oneOfPair H X, ↑X.card := sum_le_sum <| fun i hi ↦ Nat.cast_le.2 <| by
          rw [oneOfPair_mem' hH]
          exact card_le_card (filter_subset _ _)
       _ = X.card * (oneOfPair H X).card := by simp [mul_comm]

private lemma oneOfPair_bound {K : ℝ} (hH : H ⊆ X ×ˢ X) (hX : (0 : ℝ) < X.card)
    (Hcard : (7 / 8 : ℝ) * X.card ^ 2 ≤ H.card) (h : A.card / (2 * K) ≤ X.card) :
    A.card / (2 ^ 4 * K) ≤ (oneOfPair H X).card := -- by
  calc _ = (A.card / (2 * K)) / 8 := by ring
       _ ≤ (X.card / 8 : ℝ) := by gcongr
       _ ≤ (oneOfPair H X).card :=
            le_of_mul_le_mul_left ((oneOfPair_bound_two hH Hcard).trans_eq' (by ring)) hX

lemma quadruple_bound_c {a b : α} {H : Finset (α × α)} (ha : a ∈ oneOfPair H X)
    (hb : b ∈ oneOfPair H X) (hH : H ⊆ X ×ˢ X) :
    (X.card : ℝ) / 2 ≤ (X.filter fun c ↦ (a, c) ∈ H ∧ (b, c) ∈ H).card := by
  rw [oneOfPair_mem, oneOfPair_mem' hH] at ha hb
  rw [filter_and, cast_card_inter, ←filter_or]
  have : ((X.filter fun c ↦ (a, c) ∈ H ∨ (b, c) ∈ H).card : ℝ) ≤ X.card := by
    rw [Nat.cast_le]
    exact card_le_card (filter_subset _ _)
  linarith [ha.2, hb.2, this]

variable [AddCommGroup α]

lemma quadruple_bound_right {a b : α} (H : Finset (α × α)) (X : Finset α) (h : x = a - b) :
    (((X.filter fun c ↦ (a, c) ∈ H ∧ (b, c) ∈ H).sigma fun c ↦
      ((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦
        a₁ - a₂ = a - c ∧ a₃ - a₄ = b - c).card : ℝ) ≤
      (((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦
        (a₁ - a₂) - (a₃ - a₄) = a - b).card := by
  rw [←h, Nat.cast_le]
  refine card_le_card_of_injOn Sigma.snd ?_ ?_
  · simp only [not_and, mem_product, and_imp, Prod.forall, mem_sigma, mem_filter, Sigma.forall]
    intro c a₁ a₂ a₃ a₄ _ _ _ ha₁ ha₂ ha₃ ha₄ h₁ h₂
    simp [*]
  simp only [Set.InjOn, not_and, mem_product, and_imp, Prod.forall, mem_sigma, mem_filter,
    Sigma.forall, Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq]
  simp (config := {contextual := true})
  aesop

end

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable {R : Type*} [CommSemiring R] [StarRing R]
variable {A B : Finset G} {x : G}

lemma thing_one : (𝟭_[R] B ○ 𝟭 A) x = ∑ y, 𝟭 A y * 𝟭 B (x + y) := by
  simp only [dconv_eq_sum_add, conj_indicate_apply, mul_comm]

lemma thing_one_right : (𝟭_[R] A ○ 𝟭 B) x = (A ∩ (x +ᵥ B)).card := by
  rw [indicate_dconv_indicate_apply]
  congr 1
  apply card_nbij' Prod.fst (fun a ↦ (a, a - x)) <;> aesop (add simp [mem_vadd_finset])

lemma thing_two : ∑ s, (𝟭_[R] A ○ 𝟭 B) s = A.card * B.card := by
  simp only [sum_dconv, conj_indicate_apply, sum_indicate]

lemma thing_three : ∑ s, ((𝟭 A ○ 𝟭 B) s ^ 2 : R) = E[A, B] := by
  simp only [indicate_dconv_indicate_apply, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, sum_mul,
    sum_filter, Nat.cast_ite, Nat.cast_zero, sum_product, sq, addEnergy, mul_sum]
  simp only [mul_boole, sum_comm (s := univ), sum_ite_eq, mem_univ, ite_true]
  simp only [sum_comm (s := B) (t := A), sub_eq_sub_iff_add_eq_add]
  exact sum_comm

section lemma1

lemma claim_one : ∑ s, (𝟭_[R] A ○ 𝟭 B) s * (A ∩ (s +ᵥ B)).card = E[A, B] := by
  simp only [←thing_three, ←thing_one_right, sq]

lemma claim_two :
    (E[A, B]) ^ 2 / (A.card * B.card) ≤ ∑ s, (𝟭_[ℝ] A ○ 𝟭 B) s * (A ∩ (s +ᵥ B)).card ^ 2 := by
  let f := fun s ↦ ((𝟭_[ℝ] A ○ 𝟭 B) s).sqrt
  have hf : ∀ s, f s ^ 2 = (𝟭_[ℝ] A ○ 𝟭 B) s := by
    intro s
    rw [Real.sq_sqrt]
    exact dconv_nonneg (R := ℝ) indicate_nonneg indicate_nonneg s -- why do I need the annotation??
  have := sum_mul_sq_le_sq_mul_sq univ f (fun s ↦ f s * (A ∩ (s +ᵥ B)).card)
  refine div_le_of_nonneg_of_le_mul (by positivity) ?_ ?_
  · refine sum_nonneg fun i _ ↦ ?_
    -- indicate nonneg should be a positivity lemma
    exact mul_nonneg (dconv_nonneg indicate_nonneg indicate_nonneg _) (by positivity)
  simp only [←sq, ←mul_assoc, hf, thing_two, mul_pow, claim_one] at this
  refine this.trans ?_
  rw [mul_comm]

lemma claim_three {H : Finset (G × G)} (hH : H ⊆ A ×ˢ A) :
    ∑ s, (𝟭_[ℝ] A ○ 𝟭 B) s * ((A ∩ (s +ᵥ B)) ×ˢ (A ∩ (s +ᵥ B)) ∩ H).card =
      ∑ ab in H, ∑ s, (𝟭_[ℝ] A ○ 𝟭 B) s * (𝟭 B (ab.1 - s) * 𝟭 B (ab.2 - s)) := by
  simp only [sum_comm (s := H), ←mul_sum]
  refine sum_congr rfl fun x _ ↦ ?_
  congr 1
  rw [card_eq_sum_ones, inter_comm, ←filter_mem_eq_inter, sum_filter, Nat.cast_sum]
  refine sum_congr rfl fun ⟨a, b⟩ hab ↦ ?_
  have : a ∈ A ∧ b ∈ A := by simpa using hH hab
  simp only [mem_inter, mem_product, Nat.cast_ite, Nat.cast_zero, Nat.cast_one, this, true_and,
    indicate_apply, ite_and, boole_mul, ←neg_vadd_mem_iff, vadd_eq_add, neg_add_eq_sub]

lemma claim_four (ab : G × G) :
    ∑ s, (𝟭_[ℝ] A ○ 𝟭 B) s * (𝟭 B (ab.1 - s) * 𝟭 B (ab.2 - s)) ≤
      B.card * (𝟭 B ○ 𝟭 B) (ab.1 - ab.2) := by
  rcases ab with ⟨a, b⟩
  have : ∀ s, (𝟭_[ℝ] A ○ 𝟭 B) s ≤ B.card := fun s ↦ by
    simp only [dconv_eq_sum_add, conj_indicate_apply, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    simp only [indicate_apply, mul_boole, ←sum_filter (· ∈ B), filter_mem_eq_inter, univ_inter]
    refine sum_le_sum fun i _ ↦ ?_
    split
    · rfl
    · exact zero_le_one
  have : ∑ s : G, (𝟭_[ℝ] A ○ 𝟭 B) s * (𝟭 B ((a, b).1 - s) * 𝟭 B ((a, b).2 - s)) ≤
      B.card * ∑ s : G, (𝟭 B ((a, b).1 - s) * 𝟭 B ((a, b).2 - s)) := by
    rw [mul_sum]
    refine sum_le_sum fun i _ ↦ ?_
    exact mul_le_mul_of_nonneg_right (this _) (mul_nonneg (indicate_nonneg _) (indicate_nonneg _))
  refine this.trans_eq ?_
  congr 1
  simp only [dconv_eq_sum_add]
  exact Fintype.sum_equiv (Equiv.subLeft b) _ _ $ by simp

lemma claim_five {H : Finset (G × G)} (hH : H ⊆ A ×ˢ A) :
    ∑ s, (𝟭_[ℝ] A ○ 𝟭 B) s * ((A ∩ (s +ᵥ B)) ×ˢ (A ∩ (s +ᵥ B)) ∩ H).card ≤
      B.card * ∑ ab in H, (𝟭 B ○ 𝟭 B) (ab.1 - ab.2) := by
  rw [claim_three hH, mul_sum]
  exact sum_le_sum fun ab _ ↦ claim_four ab

noncomputable def H_choice (A B : Finset G) (c : ℝ) : Finset (G × G) :=
  (A ×ˢ A).filter
    fun ab ↦
      (𝟭_[ℝ] B ○ 𝟭 B) (ab.1 - ab.2) ≤ c / 2 * (E[A, B] ^ 2 / (A.card ^ 3 * B.card ^ 2))

-- lemma H_choice_subset :
lemma claim_six (c : ℝ) (hc : 0 ≤ c) :
    ∑ s, (𝟭_[ℝ] A ○ 𝟭 B) s * ((A ∩ (s +ᵥ B)) ×ˢ (A ∩ (s +ᵥ B)) ∩ H_choice A B c).card ≤
      c / 2 * (E[A, B] ^ 2 / (A.card * B.card)) := by
  refine (claim_five (filter_subset _ _)).trans ?_
  have : ∑ ab in H_choice A B c, (𝟭_[ℝ] B ○ 𝟭 B) (ab.1 - ab.2) ≤
      (H_choice A B c).card * (c / 2 * (E[A, B] ^ 2 / (A.card ^ 3 * B.card ^ 2))) := by
    rw [←nsmul_eq_mul]
    refine sum_le_card_nsmul _ _ _ ?_
    intro x hx
    exact (mem_filter.1 hx).2
  have hA : ((H_choice A B c).card : ℝ) ≤ A.card ^ 2 := by
    norm_cast
    exact (card_le_card (filter_subset _ _)).trans_eq (by simp [sq])
  refine (mul_le_mul_of_nonneg_left this (by positivity)).trans ?_
  rcases A.card.eq_zero_or_pos with hA | hA
  · rw [hA]
    simp
  rcases B.card.eq_zero_or_pos with hB | hB
  · rw [hB]
    simp
  calc
    _ ≤ (B.card : ℝ) * (A.card ^ 2 * (c / 2 * (E[A, B] ^ 2 / (A.card ^ 3 * B.card ^ 2))))
        := by gcongr
    _ = c / 2 * (E[A, B] ^ 2 / (card A * card B)) := by field_simp; ring

lemma claim_seven (c : ℝ) (hc : 0 ≤ c) (hA : (0 : ℝ) < card A) (hB : (0 : ℝ) < card B) :
    ∑ s, (𝟭_[ℝ] A ○ 𝟭 B) s *
        ((c / 2) * (E[A, B] ^ 2 / (A.card ^ 2 * B.card ^ 2)) +
          ((A ∩ (s +ᵥ B)) ×ˢ (A ∩ (s +ᵥ B)) ∩ H_choice A B c).card) ≤
      ∑ s, (𝟭_[ℝ] A ○ 𝟭 B) s * (c * (A ∩ (s +ᵥ B)).card ^ 2) :=
  calc _ = (c / 2 * (E[A, B] ^ 2 / (card A * card B))) +
    ∑ x : G, (𝟭_[ℝ] A ○ 𝟭 B) x * (card ((A ∩ (x +ᵥ B)) ×ˢ (A ∩ (x +ᵥ B)) ∩ H_choice A B c)) := by
        simp only [mul_add, sum_add_distrib, ←sum_mul, thing_two, ←mul_pow]
        field_simp
        ring
       _ ≤ _ := by
        refine (add_le_add_left (claim_six c hc) _).trans ?_
        rw [←add_mul, add_halves]
        simp only [mul_left_comm _ c, ←mul_sum]
        gcongr
        exact claim_two

lemma claim_eight (c : ℝ) (hc : 0 ≤ c) (hA : (0 : ℝ) < card A) (hB : (0 : ℝ) < card B) :
    ∃ s : G, ((c / 2) * (E[A, B] ^ 2 / (A.card ^ 2 * B.card ^ 2)) +
          ((A ∩ (s +ᵥ B)) ×ˢ (A ∩ (s +ᵥ B)) ∩ H_choice A B c).card) ≤
      c * (A ∩ (s +ᵥ B)).card ^ 2 := by
  by_contra!
  refine (claim_seven c hc hA hB).not_lt ?_
  refine sum_lt_sum ?_ ?_
  · intros s _
    exact mul_le_mul_of_nonneg_left (this s).le (dconv_nonneg indicate_nonneg indicate_nonneg s)
  have : 0 < 𝟭_[ℝ] A ○ 𝟭 B := by
    refine dconv_pos ?_ ?_
    · simpa [indicate_pos, Finset.card_pos] using hA
    · simpa [indicate_pos, Finset.card_pos] using hB
  rw [@Pi.lt_def] at this
  obtain ⟨-, i, hi : 0 < _⟩ := this
  exact ⟨i, by simp, mul_lt_mul_of_pos_left (this i) hi⟩

lemma test_case {E A B : ℕ} {K : ℝ} (hK : 0 < K) (hE : K⁻¹ * (A ^ 2 * B) ≤ E)
    (hA : 0 < A) (hB : 0 < B) :
    A / (Real.sqrt 2 * K) ≤ Real.sqrt 2⁻¹ * (E / (A * B)) := by
  rw [inv_mul_le_iff hK] at hE
  rw [mul_div_assoc', div_le_div_iff, ←mul_assoc, ←sq]
  rotate_left
  · positivity
  · positivity
  refine hE.trans_eq ?_
  field_simp
  ring

lemma lemma_one {c K : ℝ} (hc : 0 < c) (hK : 0 < K)
  (hE : K⁻¹ * (A.card ^ 2 * B.card) ≤ E[A, B])
  (hA : (0 : ℝ) < card A) (hB : (0 : ℝ) < card B) :
    ∃ s : G, ∃ X ⊆ A ∩ (s +ᵥ B), A.card / (Real.sqrt 2 * K) ≤ X.card ∧
      (1 - c) * X.card ^ 2 ≤
        ((X ×ˢ X).filter
          (fun ⟨a, b⟩ ↦ c / 2 * (K ^ 2)⁻¹ * A.card ≤ (𝟭 B ○ 𝟭 B) (a - b))).card := by
  obtain ⟨s, hs⟩ := claim_eight c hc.le hA hB
  set X := A ∩ (s +ᵥ B)
  refine ⟨s, X, subset_rfl, ?_, ?_⟩
  · have : (2 : ℝ)⁻¹ * (E[A, B] / (card A * card B)) ^ 2 ≤ (card X) ^ 2 := by
      refine le_of_mul_le_mul_left ?_ hc
      exact ((le_add_of_nonneg_right (Nat.cast_nonneg _)).trans hs).trans_eq' (by ring)
    replace := Real.sqrt_le_sqrt this
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity),
      Real.sqrt_sq (by positivity)] at this
    refine this.trans' ?_
    -- I'd like automation to handle the rest of this
    rw [inv_mul_le_iff hK] at hE
    rw [mul_div_assoc', div_le_div_iff, ←mul_assoc, ←sq]
    rotate_left
    · positivity
    · positivity
    refine hE.trans_eq ?_
    field_simp
    ring
  rw [one_sub_mul, sub_le_comm]
  refine ((le_add_of_nonneg_left (by positivity)).trans hs).trans' ?_
  rw [sq, ←Nat.cast_mul, ←card_product, ←cast_card_sdiff (filter_subset _ _), ←filter_not,
    ←filter_mem_eq_inter]
  refine Nat.cast_le.2 <| card_le_card ?_
  rintro ⟨a, b⟩
  simp (config := { contextual := true }) only [not_le, mem_product, mem_inter, and_imp,
    Prod.forall, not_lt, mem_filter, H_choice, filter_congr_decidable, and_self, true_and, X]
  rintro _ _ _ _ h
  -- I'd like automation to handle the rest of this
  refine h.le.trans ?_
  rw [mul_assoc]
  gcongr _ * ?_
  field_simp [hA, hB, hK, le_div_iff, div_le_iff] at hE ⊢
  convert_to (A.card ^ 2 * B.card) ^ 2 ≤ (E[A, B] * K) ^ 2
  · ring_nf
  · ring_nf
  gcongr

lemma lemma_one' {c K : ℝ} (hc : 0 < c) (hK : 0 < K)
    (hE : K⁻¹ * (A.card ^ 2 * B.card) ≤ E[A, B])
    (hA : (0 : ℝ) < card A) (hB : (0 : ℝ) < card B) :
    ∃ s : G, ∃ X ⊆ A ∩ (s +ᵥ B), A.card / (2 * K) ≤ X.card ∧
      (1 - c) * X.card ^ 2 ≤
        ((X ×ˢ X).filter
          (fun ⟨a, b⟩ ↦ c / 2 * (K ^ 2)⁻¹ * A.card ≤ (𝟭 B ○ 𝟭 B) (a - b))).card := by
  obtain ⟨s, X, hX₁, hX₂, hX₃⟩ := lemma_one hc hK hE hA hB
  refine ⟨s, X, hX₁, hX₂.trans' ?_, hX₃⟩
  gcongr _ / (?_ * _)
  rw [Real.sqrt_le_iff]
  norm_num

end lemma1

section lemma2

open Pointwise

lemma many_pairs {K : ℝ} {x : G}
    (hab : (1 / 8 : ℝ) / 2 * (K ^ 2)⁻¹ * A.card ≤ (𝟭 B ○ 𝟭 B) x) :
    A.card / (2 ^ 4 * K ^ 2) ≤ ((B ×ˢ B).filter (fun ⟨c, d⟩ ↦ c - d = x)).card :=
  calc _ = (1 / 8 : ℝ) / 2 * (K ^ 2)⁻¹ * A.card := by ring
       _ ≤ (𝟭 B ○ 𝟭 B) x := hab
       _ ≤ ((B ×ˢ B).filter (fun ⟨c, d⟩ ↦ c - d = x)).card := by
          rw [indicate_dconv_indicate_apply _ _ _]

variable {H : Finset (G × G)} {X : Finset G}

lemma quadruple_bound_part {K : ℝ} (a c : G)
    (hac : (1 / 8 : ℝ) / 2 * (K ^ 2)⁻¹ * A.card ≤ (𝟭 B ○ 𝟭 B) (a - c)) :
    A.card / (2 ^ 4 * K ^ 2) ≤ ((B ×ˢ B).filter fun ⟨a₁, a₂⟩ ↦ a₁ - a₂ = a - c).card :=
  many_pairs hac

lemma quadruple_bound_other {a b c : G} {K : ℝ} {H : Finset (G × G)}
    (hac : (a, c) ∈ H) (hbc : (b, c) ∈ H)
    (hH : ∀ x ∈ H, (1 / 8 : ℝ) / 2 * (K ^ 2)⁻¹ * A.card ≤ (𝟭 B ○ 𝟭 B) (x.1 - x.2)) :
    (A.card / (2 ^ 4 * K ^ 2)) ^ 2 ≤ (((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦
        a₁ - a₂ = a - c ∧ a₃ - a₄ = b - c).card := by
  change (_ : ℝ) ≤ (((B ×ˢ B) ×ˢ B ×ˢ B).filter fun (z : (G × G) × G × G) ↦
    z.1.1 - z.1.2 = a - c ∧ z.2.1 - z.2.2 = b - c).card
  rw [filter_product (s := B ×ˢ B) (t := B ×ˢ B) (fun z ↦ z.1 - z.2 = a - c)
    (fun z ↦ z.1 - z.2 = b - c), card_product, sq, Nat.cast_mul]
  gcongr ?_ * ?_
  · exact quadruple_bound_part _ _ (hH _ hac)
  · exact quadruple_bound_part _ _ (hH _ hbc)

lemma quadruple_bound_left {a b : G} {K : ℝ} {H : Finset (G × G)}
    (ha : a ∈ oneOfPair H X) (hb : b ∈ oneOfPair H X)
    (hH : ∀ x ∈ H, (1 / 8 : ℝ) / 2 * (K ^ 2)⁻¹ * A.card ≤ (𝟭 B ○ 𝟭 B) (x.1 - x.2))
    (hH' : H ⊆ X ×ˢ X) :
    ((X.card : ℝ) / 2) * (A.card / (2 ^ 4 * K ^ 2)) ^ 2 ≤
      ((X.filter fun c ↦ (a, c) ∈ H ∧ (b, c) ∈ H).sigma fun c ↦
      ((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦
        a₁ - a₂ = a - c ∧ a₃ - a₄ = b - c).card :=
  calc _ ≤ ∑ _x in X.filter fun c ↦ (a, c) ∈ H ∧ (b, c) ∈ H,
            ((A.card / (2 ^ 4 * K ^ 2)) ^ 2 : ℝ) := by
                rw [sum_const, nsmul_eq_mul]
                gcongr ?_ * _
                exact quadruple_bound_c ha hb hH'
       _ ≤ ∑ c in X.filter fun c ↦ (a, c) ∈ H ∧ (b, c) ∈ H,
            ((((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ((a₁, a₂), a₃, a₄) ↦
                a₁ - a₂ = a - c ∧ a₃ - a₄ = b - c).card : ℝ) := sum_le_sum <| fun i hi ↦ by
            simp only [not_and, mem_filter] at hi
            exact quadruple_bound_other hi.2.1 hi.2.2 hH
       _ = _ := by rw [card_sigma, Nat.cast_sum]

lemma quadruple_bound {K : ℝ} {x : G} (hx : x ∈ oneOfPair H X - oneOfPair H X)
    (hH : ∀ x ∈ H, (1 / 8 : ℝ) / 2 * (K ^ 2)⁻¹ * A.card ≤ (𝟭 B ○ 𝟭 B) (x.1 - x.2))
    (hH' : H ⊆ X ×ˢ X) :
    (A.card ^ 2 * X.card) / (2 ^ 9 * K ^ 4) ≤
      (((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦ (a₁ - a₂) - (a₃ - a₄) = x).card := by
  rw [mem_sub] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  refine (quadruple_bound_right H X rfl).trans' ?_
  refine (quadruple_bound_left ha hb hH hH').trans_eq' ?_
  ring

lemma big_quadruple_bound {K : ℝ}
    (hH : ∀ x ∈ H, (1 / 8 : ℝ) / 2 * (K ^ 2)⁻¹ * A.card ≤ (𝟭 B ○ 𝟭 B) (x.1 - x.2))
    (hH' : H ⊆ X ×ˢ X)
    (hX : A.card / (2 * K) ≤ X.card) :
    ((oneOfPair H X - oneOfPair H X).card) * (A.card ^ 3 / (2 ^ 10 * K ^ 5)) ≤
      B.card ^ 4 :=
  calc _ = ((oneOfPair H X - oneOfPair H X).card) *
                ((A.card ^ 2 * (A.card / (2 * K))) / (2 ^ 9 * K ^ 4)) := by ring
       _ ≤ ((oneOfPair H X - oneOfPair H X).card) *
                ((A.card ^ 2 * X.card) / (2 ^ 9 * K ^ 4)) := by gcongr
       _ = ∑ _x in oneOfPair H X - oneOfPair H X,
            ((A.card ^ 2 * X.card) / (2 ^ 9 * K ^ 4) : ℝ) := by simp
       _ ≤ ∑ x in oneOfPair H X - oneOfPair H X,
          ((((B ×ˢ B) ×ˢ B ×ˢ B).filter
            fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦ (a₁ - a₂) - (a₃ - a₄) = x).card : ℝ) :=
              sum_le_sum fun x hx ↦ quadruple_bound hx hH hH'
       _ ≤ ∑ x, ((((B ×ˢ B) ×ˢ B ×ˢ B).filter
            fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ ↦ (a₁ - a₂) - (a₃ - a₄) = x).card : ℝ) :=
              sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ ↦ by positivity)
       _ = _ := by
          rw [←Nat.cast_sum, ←card_eq_sum_card_fiberwise]
          · simp only [card_product, Nat.cast_mul]
            ring_nf
          · simp

theorem BSG_aux {K : ℝ} (hK : 0 < K) (hA : (0 : ℝ) < A.card) (hB : (0 : ℝ) < B.card)
    (hAB : K⁻¹ * (A.card ^ 2 * B.card) ≤ E[A, B]) :
    ∃ s : G, ∃ A' ⊆ A ∩ (s +ᵥ B), (2 ^ 4 : ℝ)⁻¹ * K⁻¹ * A.card ≤ A'.card ∧
    (A' - A').card ≤ 2 ^ 10 * K ^ 5 * B.card ^ 4 / A.card ^ 3 := by
  obtain ⟨s, X, hX₁, hX₂, hX₃⟩ := lemma_one' (c := 1 / 8) (by norm_num) hK hAB hA hB
  set H : Finset (G × G) := (X ×ˢ X).filter
    fun ⟨a, b⟩ ↦ (1 / 8 : ℝ) / 2 * (K ^ 2)⁻¹ * A.card ≤ (𝟭 B ○ 𝟭 B) (a - b)
  have : (0 : ℝ) < X.card := hX₂.trans_lt' (by positivity)
  refine ⟨s, oneOfPair H X, (filter_subset _ _).trans hX₁, ?_, ?_⟩
  · rw [←mul_inv, inv_mul_eq_div]
    exact oneOfPair_bound (filter_subset _ _) this (hX₃.trans_eq' (by norm_num)) hX₂
  have := big_quadruple_bound (H := H) (fun x hx ↦ (mem_filter.1 hx).2) (filter_subset _ _) hX₂
  rw [le_div_iff (by positivity)]
  rw [mul_div_assoc', div_le_iff (by positivity)] at this
  exact this.trans_eq (by ring)

theorem BSG {K : ℝ} (hK : 0 ≤ K) (hB : B.Nonempty) (hAB : K⁻¹ * (A.card ^ 2 * B.card) ≤ E[A, B]) :
    ∃ A' ⊆ A, (2 ^ 4 : ℝ)⁻¹ * K⁻¹ * A.card ≤ A'.card ∧
      (A' - A').card ≤ 2 ^ 10 * K ^ 5 * B.card ^ 4 / A.card ^ 3 := by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · exact ⟨∅, by simp⟩
  obtain rfl | hK := eq_or_lt_of_le hK
  · exact ⟨∅, by simp⟩
  · obtain ⟨s, A', hA, h⟩ := BSG_aux hK (by simpa [card_pos]) (by simpa [card_pos]) hAB
    exact ⟨A', hA.trans (inter_subset_left ..), h⟩

theorem BSG₂ {K : ℝ} (hK : 0 ≤ K) (hB : B.Nonempty) (hAB : K⁻¹ * (A.card ^ 2 * B.card) ≤ E[A, B]) :
    ∃ A' ⊆ A, ∃ B' ⊆ B, (2 ^ 4 : ℝ)⁻¹ * K⁻¹ * A.card ≤ A'.card ∧
    (2 ^ 4 : ℝ)⁻¹ * K⁻¹ * A.card ≤ B'.card ∧
      (A' - B').card ≤ 2 ^ 10 * K ^ 5 * B.card ^ 4 / A.card ^ 3 := by
  obtain rfl | hA := A.eq_empty_or_nonempty
  · exact ⟨∅, by simp, ∅, by simp⟩
  obtain rfl | hK := eq_or_lt_of_le hK
  · exact ⟨∅, by simp, ∅, by simp⟩
  · obtain ⟨s, A', hA, h⟩ := BSG_aux hK (by simpa [card_pos]) (by simpa [card_pos]) hAB
    refine ⟨A', hA.trans (inter_subset_left ..), -s +ᵥ A' ,?_, ?_⟩
    calc
      -s +ᵥ A' ⊆ -s +ᵥ (A ∩ (s +ᵥ B)) := vadd_finset_subset_vadd_finset hA
      _ ⊆ -s +ᵥ (s +ᵥ B) := vadd_finset_subset_vadd_finset (inter_subset_right ..)
      _ = B := neg_vadd_vadd ..
    refine ⟨h.1, (card_vadd_finset (-s) A') ▸ h.1, ?_⟩
    convert h.2 using 2
    simp only [sub_eq_add_neg, neg_vadd_finset_distrib, neg_neg]
    rw [add_vadd_comm]
    apply card_vadd_finset

theorem BSG_self {K : ℝ} (hK : 0 ≤ K) (hA : A.Nonempty) (hAK : K⁻¹ * A.card ^ 3 ≤ E[A]) :
    ∃ A' ⊆ A, (2 ^ 4 : ℝ)⁻¹ * K⁻¹ * A.card ≤ A'.card ∧
      (A' - A').card ≤ 2 ^ 10 * K ^ 5 * A.card := by
  convert BSG hK hA ?_ using 5
  · have := hA.card_pos
    field_simp
    ring
  · ring_nf
    assumption

theorem BSG_self' {K : ℝ} (hK : 0 ≤ K) (hA : A.Nonempty) (hAK : K⁻¹ * A.card ^ 3 ≤ E[A]) :
    ∃ A' ⊆ A, (2 ^ 4 : ℝ)⁻¹ * K⁻¹ * A.card ≤ A'.card ∧
      (A' - A').card ≤ 2 ^ 14 * K ^ 6 * A'.card := by
  obtain ⟨A', hA', hAA', hAK'⟩ := BSG_self hK hA hAK
  refine ⟨A', hA', hAA', hAK'.trans ?_⟩
  calc
    _ = 2 ^ 14 * K ^ 6 * ((2 ^ 4)⁻¹ * K⁻¹ * A.card) := ?_
    _ ≤ _ := by gcongr
  obtain rfl | hK := hK.eq_or_lt
  · simp
  · field_simp
    ring

end lemma2
