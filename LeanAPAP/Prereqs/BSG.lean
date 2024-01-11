import LeanAPAP.Prereqs.Convolution.Order
import Mathlib.Combinatorics.Additive.Energy
import LeanAPAP.Mathlib.Algebra.BigOperators.Order
import LeanAPAP.Mathlib.Data.Real.Sqrt
import LeanAPAP.Mathlib.Data.Finset.Card

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
variable {β : Type*} [CommSemiring β] [StarRing β]
variable {A B : Finset G} {x : G}

-- TODO: does this work for anything more general than Ring?
lemma card_inter_eq {γ : Type*} [Ring γ] :
    ((A ∩ B).card : γ) = A.card + B.card - (A ∪ B).card := by
  rw [eq_sub_iff_add_eq, ←Nat.cast_add, Finset.card_inter_add_card_union, Nat.cast_add]

lemma card_union_eq {γ : Type*} [Ring γ] :
    ((A ∪ B).card : γ) = A.card + B.card - (A ∩ B).card := by
  rw [eq_sub_iff_add_eq, ←Nat.cast_add, Finset.card_union_add_card_inter, Nat.cast_add]

open BigOperators Finset

open scoped ComplexConjugate Pointwise

lemma conj_indicate : conj (𝟭_[β] A x) = 𝟭 A x := RingHom.map_ite_one_zero _ _

lemma thing_one : (𝟭_[β] B ○ 𝟭 A) x = ∑ y, 𝟭 A y * 𝟭 B (x + y) := by
  simp only [dconv_eq_sum_add, conj_indicate, mul_comm]

lemma thing_one_right : (𝟭_[β] A ○ 𝟭 B) x = (A ∩ (x +ᵥ B)).card := by
  rw [indicate_dconv_indicate_apply]
  congr 1
  refine (Finset.card_congr (fun a _ => (a, a - x)) ?_ (by simp) ?_).symm
  · simp (config := {contextual := true}) [←neg_vadd_mem_iff, neg_add_eq_sub]
  · simp only [mem_product, and_imp, Prod.forall, mem_filter, mem_inter, exists_prop, Prod.mk.injEq]
    rintro a b ha hb rfl
    refine ⟨a, ⟨ha, ?_⟩, rfl, by simp⟩
    simp [←neg_vadd_mem_iff, hb]

lemma thing_two : ∑ s, (𝟭_[β] A ○ 𝟭 B) s = A.card * B.card := by
  simp only [sum_dconv, conj_indicate, sum_indicate]

lemma thing_three : ∑ s, ((𝟭 A ○ 𝟭 B) s ^ 2 : β) = additiveEnergy A B := by
  simp only [indicate_dconv_indicate_apply, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, sum_mul,
    sum_filter, Nat.cast_ite, Nat.cast_zero, sum_product, sq, additiveEnergy, mul_sum]
  simp only [mul_boole, sum_comm (s := univ), sum_ite_eq, mem_univ, ite_true]
  simp only [sum_comm (s := B) (t := A), sub_eq_sub_iff_add_eq_add]
  exact sum_comm

section lemma1

lemma claim_one : ∑ s, (𝟭_[β] A ○ 𝟭 B) s * (A ∩ (s +ᵥ B)).card = additiveEnergy A B := by
  simp only [←thing_three, ←thing_one_right, sq]

lemma claim_two :
    (additiveEnergy A B : ℝ) ^ 2 / (A.card * B.card) ≤
      ∑ s, (𝟭_[ℝ] A ○ 𝟭 B) s * (A ∩ (s +ᵥ B)).card ^ 2 := by
  let f := fun s => ((𝟭_[ℝ] A ○ 𝟭 B) s).sqrt
  have hf : ∀ s, f s ^ 2 = (𝟭_[ℝ] A ○ 𝟭 B) s := by
    intro s
    rw [Real.sq_sqrt]
    exact dconv_nonneg (β := ℝ) indicate_nonneg indicate_nonneg s -- why do I need the annotation??
  have := sum_mul_sq_le_sq_mul_sq univ f (fun s => f s * (A ∩ (s +ᵥ B)).card)
  refine div_le_of_nonneg_of_le_mul (by positivity) ?_ ?_
  · refine sum_nonneg fun i _ => ?_
    -- indicate nonneg should be a positivity lemma
    exact mul_nonneg (dconv_nonneg indicate_nonneg indicate_nonneg _) (by positivity)
  simp only [←sq, ←mul_assoc, hf, thing_two, mul_pow, claim_one] at this
  refine this.trans ?_
  rw [mul_comm]

lemma claim_three {H : Finset (G × G)} (hH : H ⊆ A ×ˢ A) :
    ∑ s, (𝟭_[ℝ] A ○ 𝟭 B) s * ((A ∩ (s +ᵥ B)) ×ˢ (A ∩ (s +ᵥ B)) ∩ H).card =
      ∑ ab in H, ∑ s, (𝟭_[ℝ] A ○ 𝟭 B) s * (𝟭 B (ab.1 - s) * 𝟭 B (ab.2 - s)) := by
  simp only [sum_comm (s := H), ←mul_sum]
  refine sum_congr rfl fun x _ => ?_
  congr 1
  rw [card_eq_sum_ones, inter_comm, ←filter_mem_eq_inter, sum_filter, Nat.cast_sum]
  refine sum_congr rfl fun ⟨a, b⟩ hab => ?_
  have : a ∈ A ∧ b ∈ A := by simpa using hH hab
  simp only [mem_inter, mem_product, Nat.cast_ite, Nat.cast_zero, Nat.cast_one, this, true_and,
    indicate_apply, ite_and, boole_mul, ←neg_vadd_mem_iff, vadd_eq_add, neg_add_eq_sub]

lemma claim_four (ab : G × G) :
    ∑ s, (𝟭_[ℝ] A ○ 𝟭 B) s * (𝟭 B (ab.1 - s) * 𝟭 B (ab.2 - s)) ≤
      B.card * (𝟭 B ○ 𝟭 B) (ab.1 - ab.2) := by
  rcases ab with ⟨a, b⟩
  have : ∀ s, (𝟭_[ℝ] A ○ 𝟭 B) s ≤ B.card := fun s => by
    simp only [dconv_eq_sum_add, conj_indicate, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    simp only [indicate_apply, mul_boole, ←sum_filter (· ∈ B), filter_mem_eq_inter, univ_inter]
    refine sum_le_sum fun i _ => ?_
    split
    · rfl
    · exact zero_le_one
  have : ∑ s : G, (𝟭_[ℝ] A ○ 𝟭 B) s * (𝟭 B ((a, b).1 - s) * 𝟭 B ((a, b).2 - s)) ≤
      B.card * ∑ s : G, (𝟭 B ((a, b).1 - s) * 𝟭 B ((a, b).2 - s)) := by
    rw [mul_sum]
    refine sum_le_sum fun i _ => ?_
    exact mul_le_mul_of_nonneg_right (this _) (mul_nonneg (indicate_nonneg _) (indicate_nonneg _))
  refine this.trans_eq ?_
  congr 1
  simp only [dconv_eq_sum_add, conj_indicate]
  refine sum_nbij (b - ·) (by simp) (by simp) (by simp) ?_
  intro c _
  exact ⟨b - c, by simp⟩

lemma claim_five {H : Finset (G × G)} (hH : H ⊆ A ×ˢ A) :
    ∑ s, (𝟭_[ℝ] A ○ 𝟭 B) s * ((A ∩ (s +ᵥ B)) ×ˢ (A ∩ (s +ᵥ B)) ∩ H).card ≤
      B.card * ∑ ab in H, (𝟭 B ○ 𝟭 B) (ab.1 - ab.2) := by
  rw [claim_three hH, mul_sum]
  exact sum_le_sum fun ab _ => claim_four ab

noncomputable def H_choice (A B : Finset G) (c : ℝ) : Finset (G × G) :=
  (A ×ˢ A).filter
    fun ab =>
      (𝟭_[ℝ] B ○ 𝟭 B) (ab.1 - ab.2) ≤ c / 2 * ((additiveEnergy A B) ^ 2 / (A.card ^ 3 * B.card ^ 2))

-- lemma H_choice_subset :
lemma claim_six (c : ℝ) (hc : 0 ≤ c) :
    ∑ s, (𝟭_[ℝ] A ○ 𝟭 B) s * ((A ∩ (s +ᵥ B)) ×ˢ (A ∩ (s +ᵥ B)) ∩ H_choice A B c).card ≤
      c / 2 * ((additiveEnergy A B) ^ 2 / (A.card * B.card)) := by
  refine (claim_five (filter_subset _ _)).trans ?_
  have : ∑ ab in H_choice A B c, (𝟭_[ℝ] B ○ 𝟭 B) (ab.1 - ab.2) ≤
      (H_choice A B c).card * (c / 2 * ((additiveEnergy A B) ^ 2 / (A.card ^ 3 * B.card ^ 2))) := by
    rw [←nsmul_eq_mul]
    refine sum_le_card_nsmul _ _ _ ?_
    intro x hx
    exact (mem_filter.1 hx).2
  have hA : ((H_choice A B c).card : ℝ) ≤ A.card ^ 2 := by
    norm_cast
    exact (card_le_of_subset (filter_subset _ _)).trans_eq (by simp [sq])
  refine (mul_le_mul_of_nonneg_left this (by positivity)).trans ?_
  rcases A.card.eq_zero_or_pos with hA | hA
  · rw [hA]
    simp
  rcases B.card.eq_zero_or_pos with hB | hB
  · rw [hB]
    simp
  calc
    _ ≤ (B.card : ℝ) * (A.card ^ 2 * (c / 2 * (additiveEnergy A B ^ 2 / (A.card ^ 3 * B.card ^ 2))))
        := by gcongr
    _ = c / 2 * (additiveEnergy A B ^ 2 / (card A * card B)) := by field_simp; ring

lemma claim_seven (c : ℝ) (hc : 0 ≤ c) (hA : (0 : ℝ) < card A) (hB : (0 : ℝ) < card B) :
    ∑ s, (𝟭_[ℝ] A ○ 𝟭 B) s *
        ((c / 2) * (additiveEnergy A B ^ 2 / (A.card ^ 2 * B.card ^ 2)) +
          ((A ∩ (s +ᵥ B)) ×ˢ (A ∩ (s +ᵥ B)) ∩ H_choice A B c).card) ≤
      ∑ s, (𝟭_[ℝ] A ○ 𝟭 B) s * (c * (A ∩ (s +ᵥ B)).card ^ 2) :=
  calc _ = (c / 2 * (additiveEnergy A B ^ 2 / (card A * card B))) +
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
    ∃ s : G, ((c / 2) * (additiveEnergy A B ^ 2 / (A.card ^ 2 * B.card ^ 2)) +
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
  (hE : K⁻¹ * (A.card ^ 2 * B.card) ≤ additiveEnergy A B)
  (hA : (0 : ℝ) < card A) (hB : (0 : ℝ) < card B) :
    ∃ X ⊆ A, A.card / (Real.sqrt 2 * K) ≤ X.card ∧
      (1 - c) * X.card ^ 2 ≤
        ((X ×ˢ X).filter
          (fun ⟨a, b⟩ => c / 2 * (K ^ 2)⁻¹ * A.card ≤ (𝟭 B ○ 𝟭 B) (a - b))).card := by
  obtain ⟨s, hs⟩ := claim_eight c hc.le hA hB
  set X := A ∩ (s +ᵥ B)
  refine ⟨X, inter_subset_left _ _, ?_, ?_⟩
  · have : (2 : ℝ)⁻¹ * (additiveEnergy A B / (card A * card B)) ^ 2 ≤ (card X) ^ 2 := by
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
  refine Nat.cast_le.2 <| card_le_of_subset ?_
  rintro ⟨a, b⟩
  simp (config := { contextual := True }) only [not_le, mem_product, mem_inter, and_imp,
    Prod.forall, not_lt, mem_filter, H_choice, filter_congr_decidable, and_self, true_and]
  rintro _ _ _ _ h
  -- I'd like automation to handle the rest of this
  refine h.le.trans ?_
  rw [mul_assoc]
  gcongr _ * ?_
  field_simp [hA, hB, hK, le_div_iff, div_le_iff] at hE ⊢
  convert_to ((A.card : ℝ) ^ 2 * B.card) ^ 2 ≤ (additiveEnergy A B * K) ^ 2
  · ring_nf
  · ring_nf
  gcongr

lemma lemma_one' {c K : ℝ} (hc : 0 < c) (hK : 0 < K)
    (hE : K⁻¹ * (A.card ^ 2 * B.card) ≤ additiveEnergy A B)
    (hA : (0 : ℝ) < card A) (hB : (0 : ℝ) < card B) :
    ∃ X ⊆ A, A.card / (2 * K) ≤ X.card ∧
      (1 - c) * X.card ^ 2 ≤
        ((X ×ˢ X).filter
          (fun ⟨a, b⟩ => c / 2 * (K ^ 2)⁻¹ * A.card ≤ (𝟭 B ○ 𝟭 B) (a - b))).card := by
  obtain ⟨X, hX₁, hX₂, hX₃⟩ := lemma_one hc hK hE hA hB
  refine ⟨X, hX₁, hX₂.trans' ?_, hX₃⟩
  gcongr _ / (?_ * _)
  rw [Real.sqrt_le_iff]
  norm_num

end lemma1

section lemma2

open Pointwise

lemma many_pairs {K : ℝ} {x : G}
    (hab : (1 / 8 : ℝ) / 2 * (K ^ 2)⁻¹ * A.card ≤ (𝟭 B ○ 𝟭 B) x) :
    A.card / (2 ^ 4 * K ^ 2) ≤ ((B ×ˢ B).filter (fun ⟨c, d⟩ => c - d = x)).card :=
  calc _ = (1 / 8 : ℝ) / 2 * (K ^ 2)⁻¹ * A.card := by ring
       _ ≤ (𝟭 B ○ 𝟭 B) x := hab
       _ ≤ ((B ×ˢ B).filter (fun ⟨c, d⟩ => c - d = x)).card := by
          rw [indicate_dconv_indicate_apply _ _ _]

-- A'
noncomputable def one_of_pair (H : Finset (G × G)) (X : Finset G) : Finset G :=
  X.filter fun x => (3 / 4 : ℝ) * X.card ≤ (H.filter fun yz => yz.1 = x).card

variable {H : Finset (G × G)} {X : Finset G}

lemma one_of_pair_mem :
    x ∈ one_of_pair H X ↔ x ∈ X ∧ (3 / 4 : ℝ) * X.card ≤ (H.filter fun yz => yz.1 = x).card :=
  mem_filter

lemma one_of_pair_mem' (hH : H ⊆ X ×ˢ X) :
    (H.filter fun yz => yz.1 = x).card = (X.filter fun c => (x, c) ∈ H).card := by
  refine card_congr (fun y _ => y.2) ?_ (by aesop) (by simp)
  simp only [Prod.forall, mem_filter, and_imp]
  rintro a b hab rfl
  exact ⟨(mem_product.1 (hH hab)).2, hab⟩

lemma one_of_pair_bound_one :
    ∑ x in X \ one_of_pair H X, ((H.filter (fun xy => xy.1 = x)).card : ℝ) ≤
      (3 / 4 : ℝ) * X.card ^ 2 :=
  calc _ ≤ ∑ _x in X \ one_of_pair H X, (3 / 4 : ℝ) * X.card := sum_le_sum fun i hi => by
          simp only [one_of_pair, ←filter_not, Prod.forall, not_le, not_lt, mem_filter] at hi
          exact hi.2.le
       _ = (X \ one_of_pair H X).card * ((3 / 4 : ℝ) * X.card) := by simp
       _ ≤ X.card * ((3 / 4 : ℝ) * X.card) :=
          mul_le_mul_of_nonneg_right
            (Nat.cast_le.2 (card_le_of_subset (sdiff_subset _ _)))
            (by positivity)
       _ = _ := by ring

lemma one_of_pair_bound_two (hH : H ⊆ X ×ˢ X)
    (Hcard : (7 / 8 : ℝ) * X.card ^ 2 ≤ H.card) :
    (1 / 8 : ℝ) * X.card ^ 2 ≤ X.card * (one_of_pair H X).card :=
  calc _ = (7 / 8 : ℝ) * X.card ^ 2 - 3 / 4 * X.card ^ 2 := by ring
       _ ≤ H.card - (3 / 4 : ℝ) * X.card ^ 2 := by linarith
       _ ≤ H.card - ∑ x in X \ one_of_pair H X, ↑(H.filter (fun xy => xy.1 = x)).card :=
          sub_le_sub_left one_of_pair_bound_one _
       _ = (H.card - ∑ x in X, ↑(H.filter (fun xy => xy.1 = x)).card) +
              ∑ x in one_of_pair H X, ↑(H.filter (fun xy => xy.1 = x)).card := by
          rw [sum_sdiff_eq_sub, sub_add]
          exact filter_subset _ _
       _ = ∑ x in one_of_pair H X, ↑(H.filter (fun xy => xy.1 = x)).card := by
          rw [add_left_eq_self, sub_eq_zero, ←Nat.cast_sum, Nat.cast_inj,
            ←card_eq_sum_card_fiberwise]
          intro x hx
          exact (mem_product.1 (hH hx)).1
       _ ≤ ∑ _x in one_of_pair H X, ↑X.card := sum_le_sum <| fun i hi => Nat.cast_le.2 <| by
          rw [one_of_pair_mem' hH]
          exact card_le_of_subset (filter_subset _ _)
       _ = X.card * (one_of_pair H X).card := by simp [mul_comm]

lemma one_of_pair_bound {K : ℝ} (hH : H ⊆ X ×ˢ X)
    (hX : (0 : ℝ) < X.card)
    (Hcard : (7 / 8 : ℝ) * X.card ^ 2 ≤ H.card)
    (h : A.card / (2 * K) ≤ X.card) :
    A.card / (2 ^ 4 * K) ≤ (one_of_pair H X).card := -- by
  calc _ = (A.card / (2 * K)) / 8 := by ring
       _ ≤ (X.card / 8 : ℝ) := by gcongr
       _ ≤ (one_of_pair H X).card :=
            le_of_mul_le_mul_left ((one_of_pair_bound_two hH Hcard).trans_eq' (by ring)) hX

lemma quadruple_bound_part {K : ℝ} (a c : G)
    (hac : (1 / 8 : ℝ) / 2 * (K ^ 2)⁻¹ * A.card ≤ (𝟭 B ○ 𝟭 B) (a - c)) :
    A.card / (2 ^ 4 * K ^ 2) ≤
      ((B ×ˢ B).filter fun ⟨a₁, a₂⟩ => a₁ - a₂ = a - c).card :=
  many_pairs hac

lemma quadruple_bound_right {a b : G} (H : Finset (G × G)) (X : Finset G) (h : x = a - b) :
    (((X.filter fun c => (a, c) ∈ H ∧ (b, c) ∈ H).sigma fun c =>
      ((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ =>
        a₁ - a₂ = a - c ∧ a₃ - a₄ = b - c).card : ℝ) ≤
      (((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ =>
        (a₁ - a₂) - (a₃ - a₄) = a - b).card := by
  rw [←h, Nat.cast_le]
  refine card_le_card_of_inj_on Sigma.snd ?_ ?_
  · simp only [not_and, mem_product, and_imp, Prod.forall, mem_sigma, mem_filter, Sigma.forall]
    intro c a₁ a₂ a₃ a₄ _ _ _ ha₁ ha₂ ha₃ ha₄ h₁ h₂
    simp [*]
  simp only [not_and, mem_product, and_imp, Prod.forall, mem_sigma, mem_filter, Sigma.forall,
    Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq]
  simp (config := {contextual := true})
  aesop

lemma quadruple_bound_c {a b : G} {H : Finset (G × G)}
    (ha : a ∈ one_of_pair H X) (hb : b ∈ one_of_pair H X)
    (hH : H ⊆ X ×ˢ X) :
    (X.card : ℝ) / 2 ≤ (X.filter fun c => (a, c) ∈ H ∧ (b, c) ∈ H).card := by
  rw [one_of_pair_mem, one_of_pair_mem' hH] at ha hb
  rw [filter_and, card_inter_eq, ←filter_or]
  have : ((X.filter fun c => (a, c) ∈ H ∨ (b, c) ∈ H).card : ℝ) ≤ X.card := by
    rw [Nat.cast_le]
    exact card_le_of_subset (filter_subset _ _)
  linarith [ha.2, hb.2, this]

lemma quadruple_bound_other {a b c : G} {K : ℝ} {H : Finset (G × G)}
    (hac : (a, c) ∈ H)
    (hbc : (b, c) ∈ H)
    (hH : ∀ x ∈ H, (1 / 8 : ℝ) / 2 * (K ^ 2)⁻¹ * A.card ≤ (𝟭 B ○ 𝟭 B) (x.1 - x.2)) :
    (A.card / (2 ^ 4 * K ^ 2)) ^ 2 ≤ (((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ =>
        a₁ - a₂ = a - c ∧ a₃ - a₄ = b - c).card := by
  change (_ : ℝ) ≤ (((B ×ˢ B) ×ˢ B ×ˢ B).filter fun (z : (G × G) × G × G) =>
    z.1.1 - z.1.2 = a - c ∧ z.2.1 - z.2.2 = b - c).card
  rw [filter_product (s := B ×ˢ B) (t := B ×ˢ B) (fun z => z.1 - z.2 = a - c)
    (fun z => z.1 - z.2 = b - c), card_product, sq, Nat.cast_mul]
  gcongr ?_ * ?_
  · exact quadruple_bound_part _ _ (hH _ hac)
  · exact quadruple_bound_part _ _ (hH _ hbc)

lemma quadruple_bound_left {a b : G} {K : ℝ} {H : Finset (G × G)}
    (ha : a ∈ one_of_pair H X) (hb : b ∈ one_of_pair H X)
    (hH : ∀ x ∈ H, (1 / 8 : ℝ) / 2 * (K ^ 2)⁻¹ * A.card ≤ (𝟭 B ○ 𝟭 B) (x.1 - x.2))
    (hH' : H ⊆ X ×ˢ X) :
    ((X.card : ℝ) / 2) * (A.card / (2 ^ 4 * K ^ 2)) ^ 2 ≤
      ((X.filter fun c => (a, c) ∈ H ∧ (b, c) ∈ H).sigma fun c =>
      ((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ =>
        a₁ - a₂ = a - c ∧ a₃ - a₄ = b - c).card :=
  calc _ ≤ ∑ _x in X.filter fun c => (a, c) ∈ H ∧ (b, c) ∈ H,
            ((A.card / (2 ^ 4 * K ^ 2)) ^ 2 : ℝ) := by
                rw [sum_const, nsmul_eq_mul]
                gcongr ?_ * _
                exact quadruple_bound_c ha hb hH'
       _ ≤ ∑ c in X.filter fun c => (a, c) ∈ H ∧ (b, c) ∈ H,
            ((((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ((a₁, a₂), a₃, a₄) =>
                a₁ - a₂ = a - c ∧ a₃ - a₄ = b - c).card : ℝ) := sum_le_sum <| fun i hi => by
            simp only [not_and, mem_filter] at hi
            exact quadruple_bound_other hi.2.1 hi.2.2 hH
       _ = _ := by rw [card_sigma, Nat.cast_sum]

lemma quadruple_bound {K : ℝ} {x : G} (hx : x ∈ one_of_pair H X - one_of_pair H X)
    (hH : ∀ x ∈ H, (1 / 8 : ℝ) / 2 * (K ^ 2)⁻¹ * A.card ≤ (𝟭 B ○ 𝟭 B) (x.1 - x.2))
    (hH' : H ⊆ X ×ˢ X) :
    (A.card ^ 2 * X.card) / (2 ^ 9 * K ^ 4) ≤
      (((B ×ˢ B) ×ˢ B ×ˢ B).filter fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ => (a₁ - a₂) - (a₃ - a₄) = x).card := by
  rw [mem_sub] at hx
  obtain ⟨a, b, ha, hb, rfl⟩ := hx
  refine (quadruple_bound_right H X rfl).trans' ?_
  refine (quadruple_bound_left ha hb hH hH').trans_eq' ?_
  ring

lemma big_quadruple_bound {K : ℝ}
    (hH : ∀ x ∈ H, (1 / 8 : ℝ) / 2 * (K ^ 2)⁻¹ * A.card ≤ (𝟭 B ○ 𝟭 B) (x.1 - x.2))
    (hH' : H ⊆ X ×ˢ X)
    (hX : A.card / (2 * K) ≤ X.card) :
    ((one_of_pair H X - one_of_pair H X).card) * (A.card ^ 3 / (2 ^ 10 * K ^ 5)) ≤
      B.card ^ 4 :=
  calc _ = ((one_of_pair H X - one_of_pair H X).card) *
                ((A.card ^ 2 * (A.card / (2 * K))) / (2 ^ 9 * K ^ 4)) := by ring
       _ ≤ ((one_of_pair H X - one_of_pair H X).card) *
                ((A.card ^ 2 * X.card) / (2 ^ 9 * K ^ 4)) := by gcongr
       _ = ∑ _x in one_of_pair H X - one_of_pair H X,
            ((A.card ^ 2 * X.card) / (2 ^ 9 * K ^ 4) : ℝ) := by simp
       _ ≤ ∑ x in one_of_pair H X - one_of_pair H X,
          ((((B ×ˢ B) ×ˢ B ×ˢ B).filter
            fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ => (a₁ - a₂) - (a₃ - a₄) = x).card : ℝ) :=
              sum_le_sum fun x hx => quadruple_bound hx hH hH'
       _ ≤ ∑ x, ((((B ×ˢ B) ×ˢ B ×ˢ B).filter
            fun ⟨⟨a₁, a₂⟩, a₃, a₄⟩ => (a₁ - a₂) - (a₃ - a₄) = x).card : ℝ) :=
              sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => by positivity)
       _ = _ := by
          rw [←Nat.cast_sum, ←card_eq_sum_card_fiberwise]
          · simp only [card_product, Nat.cast_mul]
            ring_nf
          · simp

theorem BSG_aux {K : ℝ} (hK : 0 < K) (hA : (0 : ℝ) < A.card) (hB : (0 : ℝ) < B.card)
    (hAB : K⁻¹ * (A.card ^ 2 * B.card) ≤ additiveEnergy A B) :
    ∃ A' ⊆ A, (2 ^ 4 : ℝ)⁻¹ * K⁻¹ * A.card ≤ A'.card ∧
    (A' - A').card ≤ 2 ^ 10 * K ^ 5 * B.card ^ 4 / A.card ^ 3 := by
  obtain ⟨X, hX₁, hX₂, hX₃⟩ := lemma_one' (c := 1 / 8) (by norm_num) hK hAB hA hB
  set H : Finset (G × G) := (X ×ˢ X).filter
    fun ⟨a, b⟩ => (1 / 8 : ℝ) / 2 * (K ^ 2)⁻¹ * A.card ≤ (𝟭 B ○ 𝟭 B) (a - b)
  have : (0 : ℝ) < X.card := hX₂.trans_lt' (by positivity)
  refine ⟨one_of_pair H X, (filter_subset _ _).trans hX₁, ?_, ?_⟩
  · rw [←mul_inv, inv_mul_eq_div]
    exact one_of_pair_bound (filter_subset _ _) this (hX₃.trans_eq' (by norm_num)) hX₂
  have := big_quadruple_bound (H := H) (fun x hx => (mem_filter.1 hx).2) (filter_subset _ _) hX₂
  rw [le_div_iff (by positivity)]
  rw [mul_div_assoc', div_le_iff (by positivity)] at this
  exact this.trans_eq (by ring)

theorem BSG {K : ℝ} (hK : 0 ≤ K) (hB : B.Nonempty)
    (hAB : K⁻¹ * (A.card ^ 2 * B.card) ≤ additiveEnergy A B) :
    ∃ A' ⊆ A, (2 ^ 4 : ℝ)⁻¹ * K⁻¹ * A.card ≤ A'.card ∧
    (A' - A').card ≤ 2 ^ 10 * K ^ 5 * B.card ^ 4 / A.card ^ 3 := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · exact ⟨∅, by simp⟩
  rcases eq_or_lt_of_le hK with rfl | hK
  · exact ⟨∅, by simp⟩
  · exact BSG_aux hK (by simpa [card_pos]) (by simpa [card_pos]) hAB

end lemma2
