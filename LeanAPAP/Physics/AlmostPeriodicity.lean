import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Combinatorics.Additive.DoublingConst
import Mathlib.Data.Complex.ExponentialBounds
import LeanAPAP.Mathlib.Analysis.SpecialFunctions.Pow.Real
import LeanAPAP.Prereqs.Convolution.Discrete.Basic
import LeanAPAP.Prereqs.Convolution.Norm
import LeanAPAP.Prereqs.Expect.Complex
import LeanAPAP.Prereqs.Inner.Discrete.Basic
import LeanAPAP.Prereqs.MarcinkiewiczZygmund

/-!
# Almost-periodicity
-/

open MeasureTheory
open scoped Pointwise Combinatorics.Additive

namespace Finset
variable {α : Type*} [DecidableEq α] {s : Finset α} {k : ℕ}

section Add
variable [Add α]

lemma big_shifts_step1 (L : Finset (Fin k → α)) (hk : k ≠ 0) :
    ∑ x in L + s.piDiag (Fin k), ∑ l in L, ∑ s in s.piDiag (Fin k), (if l + s = x then 1 else 0)
      = L.card * s.card := by
  simp only [@sum_comm _ _ _ _ (L + _), sum_ite_eq]
  rw [sum_const_nat]
  intro l hl
  have := Fin.pos_iff_nonempty.1 (pos_iff_ne_zero.2 hk)
  rw [sum_const_nat, mul_one, Finset.card_piDiag]
  exact fun s hs ↦ if_pos (Finset.add_mem_add hl hs)

end Add

variable [AddCommGroup α] [Fintype α]

lemma reindex_count (L : Finset (Fin k → α)) (hk : k ≠ 0) (hL' : L.Nonempty) (l₁ : Fin k → α) :
    ∑ l₂ in L, ite (l₁ - l₂ ∈ univ.piDiag (Fin k)) 1 0 =
      (univ.filter fun t ↦ (l₁ - fun _ ↦ t) ∈ L).card :=
  calc
    _ = ∑ l₂ in L, ∑ t : α, ite ((l₁ - fun _ ↦ t) = l₂) 1 0 := by
      refine sum_congr rfl fun l₂ hl₂ ↦ ?_
      rw [Fintype.sum_ite_eq_ite_exists]
      simp only [mem_piDiag, mem_univ, eq_sub_iff_add_eq, true_and, sub_eq_iff_eq_add',
        @eq_comm _ l₁]
      rfl
      rintro i j h rfl
      cases k
      · simp at hk
      · simpa using congr_fun h 0
    _ = (univ.filter fun t ↦ (l₁ - fun _ ↦ t) ∈ L).card := by
      simp only [sum_comm, sum_ite_eq, card_eq_sum_ones, sum_filter]

end Finset

section
variable {α : Type*} {g : α → ℝ} {c ε : ℝ} {A : Finset α}

open Finset
lemma my_markov (hc : 0 < c) (hg : ∀ a ∈ A, 0 ≤ g a) (h : ∑ a in A, g a ≤ ε * c * A.card) :
    (1 - ε) * A.card ≤ (A.filter (g · ≤ c)).card := by
  classical
  have := h.trans'
    (sum_le_sum_of_subset_of_nonneg (filter_subset (¬g · ≤ c) A) fun i hi _ ↦ hg _ hi)
  have :=
    (card_nsmul_le_sum _ _ c (by simp (config := { contextual := true }) [le_of_lt])).trans this
  rw [nsmul_eq_mul, mul_right_comm] at this
  have := le_of_mul_le_mul_right this hc
  rw [filter_not, cast_card_sdiff (filter_subset _ _)] at this
  linarith only [this]

lemma my_other_markov (hc : 0 ≤ c) (hε : 0 ≤ ε) (hg : ∀ a ∈ A, 0 ≤ g a)
    (h : ∑ a in A, g a ≤ ε * c * A.card) : (1 - ε) * A.card ≤ (A.filter (g · ≤ c)).card := by
  rcases hc.lt_or_eq with (hc | rfl)
  · exact my_markov hc hg h
  simp only [mul_zero, zero_mul] at h
  classical
  rw [one_sub_mul, sub_le_comm, ← cast_card_sdiff (filter_subset _ A), ← filter_not,
    filter_false_of_mem]
  · simp; positivity
  intro i hi
  rw [(sum_eq_zero_iff_of_nonneg hg).1 (h.antisymm (sum_nonneg hg)) i hi]
  simp

end

open Finset Real
open scoped BigOperators Pointwise NNReal ENNReal

variable {G : Type*} [Fintype G] {A S : Finset G} {f : G → ℂ} {x ε K : ℝ} {k m : ℕ}

local notation "𝓛" x => 1 + log (min 1 x)⁻¹

private lemma curlog_pos (hx₀ : 0 < x) : 0 < 𝓛 x := by
  have : 0 ≤ log (min 1 x)⁻¹ := log_nonneg $ one_le_inv (by positivity) inf_le_left
  positivity

section
variable [MeasurableSpace G] [DiscreteMeasurableSpace G]

lemma lemma28_end (hε : 0 < ε) (hm : 1 ≤ m) (hk : 64 * m / ε ^ 2 ≤ k) :
    (8 * m) ^ m * k ^ (m - 1) * A.card ^ k * k * (2 * ‖f‖_[2 * m] : ℝ) ^ (2 * m) ≤
      1 / 2 * ((k * ε) ^ (2 * m) * ∑ i : G, ‖f i‖ ^ (2 * m)) * ↑A.card ^ k := by
  have hmeq : ((2 * m : ℕ) : ℝ≥0∞) = 2 * m := by rw [Nat.cast_mul, Nat.cast_two]
  have hm' : 2 * m ≠ 0 := by
    refine mul_ne_zero two_pos.ne' ?_
    rw [← pos_iff_ne_zero, ← Nat.succ_le_iff]
    exact hm
  rw [mul_pow (2 : ℝ), ← hmeq, ← dLpNorm_pow_eq_sum_norm hm' f, ← mul_assoc, ← mul_assoc,
    mul_right_comm _ (A.card ^ k : ℝ), mul_right_comm _ (A.card ^ k : ℝ),
    mul_right_comm _ (A.card ^ k : ℝ)]
  gcongr ?_ * _ * _
  rw [mul_assoc (_ ^ m : ℝ), ← pow_succ, Nat.sub_add_cancel hm, pow_mul, pow_mul, ← mul_pow,
    ← mul_pow]
  have : (1 / 2 : ℝ) ^ m ≤ 1 / 2 := by
    have :=
      pow_le_pow_of_le_one (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) ≤ 1 by norm_num) hm
    rwa [pow_one] at this
  refine (mul_le_mul_of_nonneg_right this (by positivity)).trans' ?_
  rw [← mul_pow]
  refine pow_le_pow_left (by positivity) ?_ _
  rw [mul_right_comm, mul_comm _ ε, mul_pow, ← mul_assoc, sq (k : ℝ), ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg k)
  rw [mul_right_comm, div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div, le_div_iff₀' (zero_lt_two' ℝ),
    ← div_le_iff₀', ← mul_assoc]
  · norm_num1; exact hk
  positivity

end

variable [DecidableEq G] [AddCommGroup G]

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

lemma lemma28_part_one (hm : 1 ≤ m) (x : G) :
    ∑ a in A ^^ k, ‖∑ i, f (x - a i) - (k • (mu A ∗ f)) x‖ ^ (2 * m) ≤
      (8 * m) ^ m * k ^ (m - 1) *
        ∑ a in A ^^ k, ∑ i, ‖f (x - a i) - (mu A ∗ f) x‖ ^ (2 * m) := by
  let f' : G → ℂ := fun a ↦ f (x - a) - (mu A ∗ f) x
  refine (RCLike.marcinkiewicz_zygmund (by linarith only [hm]) f' ?_).trans_eq' ?_
  · intro i
    rw [Fintype.sum_piFinset_apply, sum_sub_distrib]
    simp only [sub_eq_zero, sum_const, indicate_apply]
    rw [← Pi.smul_apply (card A), ← smul_conv, card_smul_mu, conv_eq_sum_sub']
    simp only [boole_mul, indicate_apply]
    rw [← sum_filter, filter_mem_eq_inter, univ_inter, sub_self, smul_zero]
  congr with a : 1
  simp only [sum_sub_distrib, Pi.smul_apply, sum_const, card_fin]

lemma big_shifts_step2 (L : Finset (Fin k → G)) (hk : k ≠ 0) :
    (∑ x in L + S.piDiag (Fin k), ∑ l in L, ∑ s in S.piDiag (Fin k), ite (l + s = x) (1 : ℝ) 0) ^ 2
      ≤ (L + S.piDiag (Fin k)).card * S.card *
        ∑ l₁ in L, ∑ l₂ in L, ite (l₁ - l₂ ∈ univ.piDiag (Fin k)) 1 0 := by
  refine sq_sum_le_card_mul_sum_sq.trans ?_
  simp_rw [sq, sum_mul, @sum_comm _ _ _ _ (L + S.piDiag (Fin k)), boole_mul, sum_ite_eq, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have : ∀ f : (Fin k → G) → (Fin k → G) → ℝ,
    ∑ x in L, ∑ y in S.piDiag (Fin k), (if x + y ∈ L + S.piDiag (Fin k) then f x y else 0) =
      ∑ x in L, ∑ y in S.piDiag (Fin k), f x y := by
    refine fun f ↦ sum_congr rfl fun x hx ↦ ?_
    exact sum_congr rfl fun y hy ↦ if_pos $ add_mem_add hx hy
  rw [this]
  have (x y) :
      ∑ s₁ in S.piDiag (Fin k), ∑ s₂ in S.piDiag (Fin k), ite (y + s₂ = x + s₁) (1 : ℝ) 0 =
        ite (x - y ∈ univ.piDiag (Fin k)) 1 0 *
          ∑ s₁ in S.piDiag (Fin k), ∑ s₂ in S.piDiag (Fin k), ite (s₂ = x + s₁ - y) 1 0 := by
    simp_rw [mul_sum, boole_mul, ← ite_and]
    refine sum_congr rfl fun s₁ hs₁ ↦ ?_
    refine sum_congr rfl fun s₂ hs₂ ↦ ?_
    refine if_congr ?_ rfl rfl
    rw [eq_sub_iff_add_eq', and_iff_right_of_imp]
    intro h
    simp only [mem_piDiag] at hs₁ hs₂
    have : x - y = s₂ - s₁ := by rw [sub_eq_sub_iff_add_eq_add, ← h, add_comm]
    rw [this]
    obtain ⟨i, -, rfl⟩ := hs₁
    obtain ⟨j, -, rfl⟩ := hs₂
    exact mem_image.2 ⟨j - i, mem_univ _, rfl⟩
  simp_rw [@sum_comm _ _ _ _ (S.piDiag (Fin k)) L, this, sum_ite_eq']
  have : ∑ x in L, ∑ y in L,
        ite (x - y ∈ univ.piDiag (Fin k)) (1 : ℝ) 0 *
          ∑ z in S.piDiag (Fin k), ite (x + z - y ∈ S.piDiag (Fin k)) 1 0 ≤
      ∑ x in L, ∑ y in L, ite (x - y ∈ univ.piDiag (Fin k)) 1 0 * (S.card : ℝ) := by
    refine sum_le_sum fun l₁ _ ↦ sum_le_sum fun l₂ _ ↦ ?_
    refine mul_le_mul_of_nonneg_left ?_ (by split_ifs <;> norm_num)
    refine (sum_le_card_nsmul _ _ 1 ?_).trans_eq ?_
    · intro x _; split_ifs <;> norm_num
    have := Fin.pos_iff_nonempty.1 (pos_iff_ne_zero.2 hk)
    rw [card_piDiag]
    simp only [nsmul_one]
  refine this.trans ?_
  simp_rw [← sum_mul, mul_comm]
  rfl

-- might be true for dumb reason when k = 0, since L would be singleton and rhs is |G|,
-- so its just |S| ≤ |G|
lemma big_shifts (S : Finset G) (L : Finset (Fin k → G)) (hk : k ≠ 0)
    (hL' : L.Nonempty) (hL : L ⊆ A ^^ k) :
    ∃ a : Fin k → G, a ∈ L ∧
      L.card * S.card ≤ (A + S).card ^ k * (univ.filter fun t : G ↦ (a - fun _ ↦ t) ∈ L).card := by
  rcases S.eq_empty_or_nonempty with (rfl | hS)
  · simpa only [card_empty, mul_zero, zero_le', and_true] using hL'
  have hS' : 0 < S.card := by rwa [card_pos]
  have : (L + S.piDiag (Fin k)).card ≤ (A + S).card ^ k := by
    refine (card_le_card (add_subset_add_right hL)).trans ?_
    rw [← Fintype.card_piFinset_const]
    refine card_le_card fun i hi ↦ ?_
    simp only [mem_add, mem_piDiag, Fintype.mem_piFinset, exists_prop, exists_and_left,
      exists_exists_and_eq_and] at hi ⊢
    obtain ⟨y, hy, a, ha, rfl⟩ := hi
    intro j
    exact ⟨y j, hy _, a, ha, rfl⟩
  rsuffices ⟨a, ha, h⟩ : ∃ a ∈ L,
    L.card * S.card ≤ (L + S.piDiag (Fin k)).card * (univ.filter fun t ↦ (a - fun _ ↦ t) ∈ L).card
  · exact ⟨a, ha, h.trans (Nat.mul_le_mul_right _ this)⟩
  clear! A
  have : L.card ^ 2 * S.card ≤
    (L + S.piDiag (Fin k)).card *
      ∑ l₁ in L, ∑ l₂ in L, ite (l₁ - l₂ ∈ univ.piDiag (Fin k)) 1 0 := by
    refine Nat.le_of_mul_le_mul_left ?_ hS'
    rw [mul_comm, mul_assoc, ← sq, ← mul_pow, mul_left_comm, ← mul_assoc, ← big_shifts_step1 L hk]
    exact_mod_cast @big_shifts_step2 G _ _ _ _ _ L hk
  simp only [reindex_count L hk hL'] at this
  rw [sq, mul_assoc, ← smul_eq_mul, mul_sum] at this
  rw [← sum_const] at this
  exact exists_le_of_sum_le hL' this

variable [MeasurableSpace G]


namespace AlmostPeriodicity

def LProp (k m : ℕ) (ε : ℝ) (f : G → ℂ) (A : Finset G) (a : Fin k → G) : Prop :=
  ‖fun x : G ↦ ∑ i, f (x - a i) - (k • (μ A ∗ f)) x‖_[2 * m] ≤ k * ε * ‖f‖_[2 * m]

noncomputable instance : DecidablePred (LProp k m ε f A) := Classical.decPred _

noncomputable def l (k m : ℕ) (ε : ℝ) (f : G → ℂ) (A : Finset G) : Finset (Fin k → G) :=
  (A ^^ k).filter (LProp k m ε f A)

lemma lemma28_markov (hε : 0 < ε) (hm : 1 ≤ m)
    (h : ∑ a in A ^^ k,
        (‖fun x : G ↦ ∑ i : Fin k, f (x - a i) - (k • (mu A ∗ f)) x‖_[2 * m] ^ (2 * m) : ℝ) ≤
      1 / 2 * (k * ε * ‖f‖_[2 * m]) ^ (2 * m) * A.card ^ k) :
    (A.card ^ k : ℝ) / 2 ≤ (l k m ε f A).card := by
  rw [← Nat.cast_pow, ← Fintype.card_piFinset_const] at h
  have := my_other_markov (by positivity) (by norm_num) (fun _ _ ↦ by positivity) h
  norm_num1 at this
  rw [Fintype.card_piFinset_const, mul_comm, mul_one_div, Nat.cast_pow] at this
  refine this.trans_eq ?_
  rw [l]
  congr with a : 3
  refine pow_le_pow_iff_left ?_ ?_ ?_ <;> positivity

variable [DiscreteMeasurableSpace G]

lemma lemma28_part_two (hm : 1 ≤ m) (hA : A.Nonempty) :
    (8 * m) ^ m * k ^ (m - 1) * ∑ a in A ^^ k, ∑ i, ‖τ (a i) f - mu A ∗ f‖_[2 * m] ^ (2 * m) ≤
      (8 * m) ^ m * k ^ (m - 1) * ∑ a in A ^^ k, ∑ i : Fin k, (2 * ‖f‖_[2 * m]) ^ (2 * m) := by
  -- lots of the equalities about m can be automated but it's *way* slower
  have hmeq : ((2 * m : ℕ) : ℝ≥0∞) = 2 * m := by rw [Nat.cast_mul, Nat.cast_two]
  have hm' : 1 < 2 * m := (Nat.mul_le_mul_left 2 hm).trans_lt' $ by norm_num1
  have hm'' : (1 : ℝ≥0∞) ≤ 2 * m := by rw [← hmeq, Nat.one_le_cast]; exact hm'.le
  gcongr
  refine (dLpNorm_sub_le hm'').trans ?_
  rw [dLpNorm_translate, two_mul ‖f‖_[2 * m], add_le_add_iff_left]
  have hmeq' : ((2 * m : ℝ≥0) : ℝ≥0∞) = 2 * m := by
    rw [ENNReal.coe_mul, ENNReal.coe_two, ENNReal.coe_natCast]
  have : (1 : ℝ≥0) < 2 * m := by
    rw [← Nat.cast_two, ← Nat.cast_mul, Nat.one_lt_cast]
    exact hm'
  rw [← hmeq', conv_comm]
  refine (dLpNorm_conv_le this.le _ _).trans ?_
  rw [dL1Norm_mu hA, mul_one]

lemma lemma28 (hε : 0 < ε) (hm : 1 ≤ m) (hk : (64 : ℝ) * m / ε ^ 2 ≤ k) :
    (A.card ^ k : ℝ) / 2 ≤ (l k m ε f A).card := by
  have : 0 < k := by
    rw [← @Nat.cast_pos ℝ]
    refine hk.trans_lt' ?_
    refine div_pos (mul_pos (by norm_num1) ?_) (pow_pos hε _)
    rw [Nat.cast_pos, ← Nat.succ_le_iff]
    exact hm
  rcases A.eq_empty_or_nonempty with (rfl | hA)
  · simp [zero_pow this.ne']
  refine lemma28_markov hε hm ?_
  have hm' : 2 * m ≠ 0 := by linarith
  have hmeq : ((2 * m : ℕ) : ℝ≥0∞) = 2 * m := by rw [Nat.cast_mul, Nat.cast_two]
  rw [← hmeq, mul_pow]
  simp only [dLpNorm_pow_eq_sum_norm hm']
  rw [sum_comm]
  have : ∀ x : G, ∑ a in A ^^ k,
      ‖∑ i, f (x - a i) - (k • (mu A ∗ f)) x‖ ^ (2 * m) ≤
    (8 * m) ^ m * k ^ (m - 1) *
      ∑ a in A ^^ k, ∑ i, ‖f (x - a i) - (mu A ∗ f) x‖ ^ (2 * m) :=
    lemma28_part_one hm
  refine (sum_le_sum fun x _ ↦ this x).trans ?_
  rw [← mul_sum]
  simp only [@sum_comm _ _ G]
  have (a : Fin k → G) (i : Fin k) :
      ∑ x, ‖f (x - a i) - (mu A ∗ f) x‖ ^ (2 * m) = ‖τ (a i) f - mu A ∗ f‖_[2 * m] ^ (2 * m) := by
    rw [← hmeq, dLpNorm_pow_eq_sum_norm hm']
    simp only [Pi.sub_apply, translate_apply]
  simp only [this]
  have :
    (8 * m) ^ m * k ^ (m - 1) * ∑ a in A ^^ k, ∑ i, ‖τ (a i) f - mu A ∗ f‖_[2 * m] ^ (2 * m) ≤
      (8 * m) ^ m * k ^ (m - 1) * ∑ a in A ^^ k, ∑ i, (2 * ‖f‖_[2 * m]) ^ (2 * m) :=
    lemma28_part_two hm hA
  refine le_trans (mod_cast this) ?_
  simp only [sum_const, Fintype.card_piFinset_const, nsmul_eq_mul, Nat.cast_pow]
  refine (lemma28_end hε hm hk).trans_eq' ?_
  simp [mul_assoc, card_fin]

lemma just_the_triangle_inequality {t : G} {a : Fin k → G} (ha : a ∈ l k m ε f A)
    (ha' : (a + fun _ ↦ t) ∈ l k m ε f A) (hk : 0 < k) (hm : 1 ≤ m) :
    ‖τ (-t) (mu A ∗ f) - mu A ∗ f‖_[2 * m] ≤ 2 * ε * ‖f‖_[2 * m] := by
  let f₁ : G → ℂ := fun x ↦ ∑ i, f (x - a i)
  let f₂ : G → ℂ := fun x ↦ ∑ i, f (x - a i - t)
  have hp : (1 : ℝ≥0∞) ≤ 2 * m := by norm_cast; linarith
  have h₁ : ‖f₁ - k • (mu A ∗ f)‖_[2 * m] ≤ k * ε * ‖f‖_[2 * m] := by
    rw [l, Finset.mem_filter] at ha ; exact ha.2
  have h₂ : ‖f₂ - k • (mu A ∗ f)‖_[2 * m] ≤ k * ε * ‖f‖_[2 * m] := by
    rw [l, Finset.mem_filter, LProp] at ha'
    refine ha'.2.trans_eq' ?_
    congr with i : 1
    simp [sub_sub, f₂]
  have h₃ : f₂ = τ t f₁ := by
    ext i : 1
    rw [translate_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [sub_right_comm]
  have h₄₁ : ‖τ t f₁ - k • (mu A ∗ f)‖_[2 * m] = ‖τ (-t) (τ t f₁ - k • (mu A ∗ f))‖_[2 * m] := by
    rw [dLpNorm_translate]
  have h₄ : ‖τ t f₁ - k • (mu A ∗ f)‖_[2 * m] = ‖f₁ - τ (-t) (k • (mu A ∗ f))‖_[2 * m] := by
    rw [h₄₁, translate_sub_right, translate_translate]
    simp
  have h₅₁ : ‖τ (-t) (k • (mu A ∗ f)) - f₁‖_[2 * m] ≤ k * ε * ‖f‖_[2 * m] := by
    rwa [dLpNorm_sub_comm, ← h₄, ← h₃]
  have : (0 : ℝ) < k := by positivity
  refine le_of_mul_le_mul_left ?_ this
  rw [← nsmul_eq_mul, ← NNReal.coe_nsmul, ← dLpNorm_nsmul _ (_ - mu A ∗ f), nsmul_sub, ←
    translate_smul_right (-t) (mu A ∗ f) k, mul_assoc, mul_left_comm, two_mul ((k : ℝ) * _), ←
    mul_assoc]
  calc
    (‖τ (-t) (k • (μ A ∗ f)) - k • (μ A ∗ f)‖_[2 * m] : ℝ)
      ≤ ↑(‖τ (-t) (k • (μ A ∗ f)) - f₁‖_[2 * m] + ‖f₁ - k • (μ A ∗ f)‖_[2 * m]) := by
      gcongr; exact dLpNorm_sub_le_dLpNorm_sub_add_dLpNorm_sub (mod_cast hp)
    _ ≤ k * ε * ‖f‖_[2 * m] + k * ε * ‖f‖_[2 * m] := by push_cast; gcongr

lemma T_bound (hK₂ : 2 ≤ K) (Lc Sc Ac ASc Tc : ℕ) (hk : k = ⌈(64 : ℝ) * m / (ε / 2) ^ 2⌉₊)
    (h₁ : Lc * Sc ≤ ASc ^ k * Tc) (h₂ : (Ac : ℝ) ^ k / 2 ≤ Lc) (h₃ : (ASc : ℝ) ≤ K * Ac)
    (hAc : 0 < Ac) (hε : 0 < ε) (hε' : ε ≤ 1) (hm : 1 ≤ m) :
    K ^ (-512 * m / ε ^ 2 : ℝ) * Sc ≤ Tc := by
  have hk' : k = ⌈(256 : ℝ) * m / ε ^ 2⌉₊ := by
    rw [hk, div_pow, div_div_eq_mul_div, mul_right_comm]
    congr 3
    norm_num
  have hK : 0 < K := by positivity
  have : (0 : ℝ) < Ac ^ k := by positivity
  refine le_of_mul_le_mul_left ?_ this
  have : (Ac : ℝ) ^ k ≤ K * Lc := by
    rw [div_le_iff₀'] at h₂
    refine h₂.trans (mul_le_mul_of_nonneg_right hK₂ (Nat.cast_nonneg _))
    exact zero_lt_two
  rw [neg_mul, neg_div, Real.rpow_neg hK.le, mul_left_comm,
    inv_mul_le_iff (Real.rpow_pos_of_pos hK _)]
  refine (mul_le_mul_of_nonneg_right this (Nat.cast_nonneg _)).trans ?_
  rw [mul_assoc]
  rw [← @Nat.cast_le ℝ, Nat.cast_mul] at h₁
  refine (mul_le_mul_of_nonneg_left h₁ hK.le).trans ?_
  rw [Nat.cast_mul, ← mul_assoc, ← mul_assoc, Nat.cast_pow]
  refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
  refine (mul_le_mul_of_nonneg_left (pow_le_pow_left (Nat.cast_nonneg _) h₃ k) hK.le).trans ?_
  rw [mul_pow, ← mul_assoc, ← pow_succ']
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (Nat.cast_nonneg _) _)
  rw [← Real.rpow_natCast]
  refine Real.rpow_le_rpow_of_exponent_le (one_le_two.trans hK₂) ?_
  rw [Nat.cast_add_one, ← le_sub_iff_add_le, hk']
  refine (Nat.ceil_lt_add_one ?_).le.trans ?_
  · positivity
  have : (1 : ℝ) ≤ 128 * (m / ε ^ 2) := by
    rw [div_eq_mul_one_div]
    refine one_le_mul_of_one_le_of_one_le (by norm_num1) ?_
    refine one_le_mul_of_one_le_of_one_le (Nat.one_le_cast.2 hm) ?_
    refine one_le_one_div (by positivity) ?_
    rw [sq_le_one_iff hε.le]
    exact hε'
  rw [mul_div_assoc, mul_div_assoc]
  linarith only [this]

-- trivially true for other reasons for big ε
lemma almost_periodicity (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1) (m : ℕ) (f : G → ℂ)
    (hK₂ : 2 ≤ K) (hK : σ[A, S] ≤ K) :
    ∃ T : Finset G,
      K ^ (-512 * m / ε ^ 2 : ℝ) * S.card ≤ T.card ∧
        ∀ t ∈ T, ‖τ t (mu A ∗ f) - mu A ∗ f‖_[2 * m] ≤ ε * ‖f‖_[2 * m] := by
  obtain rfl | hm := m.eq_zero_or_pos
  · exact ⟨S, by simp⟩
  obtain rfl | hA := A.eq_empty_or_nonempty
  · refine ⟨univ, ?_, fun t _ ↦ ?_⟩
    · have : K ^ ((-512 : ℝ) * m / ε ^ 2) ≤ 1 := by
        refine Real.rpow_le_one_of_one_le_of_nonpos (one_le_two.trans hK₂) ?_
        rw [neg_mul, neg_div, Right.neg_nonpos_iff]
        positivity
      refine (mul_le_mul_of_nonneg_right this (Nat.cast_nonneg _)).trans ?_
      rw [one_mul, Nat.cast_le]
      exact card_le_univ _
    simp only [mu_empty, zero_conv, translate_zero_right, sub_self, dLpNorm_zero]
    positivity
  let k := ⌈(64 : ℝ) * m / (ε / 2) ^ 2⌉₊
  have hk : k ≠ 0 := by positivity
  let L := l k m (ε / 2) f A
  have : (A.card : ℝ) ^ k / 2 ≤ L.card := lemma28 (half_pos hε) hm (Nat.le_ceil _)
  have hL : L.Nonempty := by
    rw [← card_pos, ← @Nat.cast_pos ℝ]
    exact this.trans_lt' (by positivity)
  obtain ⟨a, ha, hL'⟩ := big_shifts S _ hk hL (filter_subset _ _)
  refine ⟨univ.filter fun t : G ↦ (a + fun _ ↦ -t) ∈ L, ?_, ?_⟩
  · simp_rw [sub_eq_add_neg] at hL'
    exact T_bound hK₂ L.card S.card A.card (A + S).card _ rfl hL' this
      (by rw [← cast_addConst_mul_card]; gcongr) hA.card_pos hε hε' hm
  intro t ht
  simp only [exists_prop, exists_eq_right, mem_filter, mem_univ, true_and] at ht
  have := just_the_triangle_inequality ha ht hk.bot_lt hm
  rwa [neg_neg, mul_div_cancel₀ _ (two_ne_zero' ℝ)] at this

theorem linfty_almost_periodicity (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (hK₂ : 2 ≤ K)
    (hK : σ[A, S] ≤ K) (B C : Finset G) (hB : B.Nonempty) (hC : C.Nonempty) :
    ∃ T : Finset G,
      K ^ (-4096 * ⌈𝓛 (C.card / B.card)⌉ / ε ^ 2) * S.card ≤ T.card ∧
      ∀ t ∈ T, ‖τ t (μ_[ℂ] A ∗ 𝟭 B ∗ μ C) - μ A ∗ 𝟭 B ∗ μ C‖_[∞] ≤ ε := by
  let r : ℝ := min 1 (C.card / B.card)
  set m : ℝ := 𝓛 (C.card / B.card)
  have hm₀ : 0 < m := curlog_pos (by positivity)
  have hm₁ : 1 ≤ ⌈m⌉₊ := Nat.one_le_iff_ne_zero.2 $ by positivity
  obtain ⟨T, hKT, hT⟩ := almost_periodicity (ε / exp 1) (by positivity)
    (div_le_one_of_le (hε₁.trans $ one_le_exp zero_le_one) $ by positivity) ⌈m⌉₊ (𝟭 B) hK₂ hK
  norm_cast at hT
  set M : ℕ := 2 * ⌈m⌉₊
  have hM₀ : (M : ℝ≥0) ≠ 0 := by positivity
  have hM₁ : 1 < (M : ℝ≥0) := by norm_cast; simp [← Nat.succ_le_iff, M]; linarith
  have hM : (M : ℝ≥0).IsConjExponent _ := .conjExponent hM₁
  refine ⟨T, ?_, fun t ht ↦ ?_⟩
  · calc
      _ = K ^(-(512 * 8) / ε ^ 2 * ⌈m⌉₊) * S.card := by
          rw [mul_div_right_comm, natCast_ceil_eq_intCast_ceil hm₀.le]; norm_num
      _ ≤ K ^(-(512 * exp 1 ^ 2) / ε ^ 2 * ⌈m⌉₊) * S.card := by
          gcongr
          · exact one_le_two.trans hK₂
          calc
            _ ≤ 2.7182818286 ^ 2 := pow_le_pow_left (by positivity) exp_one_lt_d9.le _
            _ ≤ _ := by norm_num
      _ = _ := by simp [div_div_eq_mul_div, ← mul_div_right_comm, mul_right_comm]
      _ ≤ _ := hKT
  set F : G → ℂ := τ t (μ A ∗ 𝟭 B) - μ A ∗ 𝟭 B
  have (x) :=
    calc
      (τ t (μ A ∗ 𝟭 B ∗ μ C) - μ A ∗ 𝟭 B ∗ μ C : G → ℂ) x
        = (F ∗ μ C) x := by simp [sub_conv, F]
      _ = ∑ y, F y * μ C (x - y) := conv_eq_sum_sub' ..
      _ = ∑ y, F y * μ (x +ᵥ -C) y := by simp [neg_add_eq_sub]
  rw [dLinftyNorm_eq_iSup_norm]
  refine ciSup_le fun x ↦ ?_
  calc
    ‖(τ t (μ A ∗ 𝟭 B ∗ μ C) - μ A ∗ 𝟭 B ∗ μ C : G → ℂ) x‖
      = ‖∑ y, F y * μ (x +ᵥ -C) y‖ := by rw [this]
    _ ≤ ∑ y, ‖F y * μ (x +ᵥ -C) y‖ := norm_sum_le _ _
    _ = ‖F * μ (x +ᵥ -C)‖_[1] := by rw [dL1Norm_eq_sum_norm]; rfl
    _ ≤ ‖F‖_[M] * ‖μ_[ℂ] (x +ᵥ -C)‖_[NNReal.conjExponent M] := dL1Norm_mul_le hM _ _
    _ ≤ ε / exp 1 * B.card ^ (M : ℝ)⁻¹ * ‖μ_[ℂ] (x +ᵥ -C)‖_[NNReal.conjExponent M] := by
        gcongr
        simpa only [← ENNReal.coe_natCast, dLpNorm_indicate hM₀] using hT _ ht
    _ = ε * ((C.card / B.card) ^ (-(M : ℝ)⁻¹) / exp 1) := by
        rw [← mul_comm_div, dLpNorm_mu hM.symm.one_le hC.neg.vadd_finset, card_vadd_finset,
          card_neg, hM.symm.coe.inv_sub_one, div_rpow, mul_assoc, NNReal.coe_natCast]
        push_cast
        rw [rpow_neg, rpow_neg, ← div_eq_mul_inv, inv_div_inv]
        all_goals positivity
    _ ≤ ε := mul_le_of_le_one_right (by positivity) $ (div_le_one $ by positivity).2 ?_
  calc
    (C.card / B.card : ℝ) ^ (-(M : ℝ)⁻¹)
      ≤ r ^ (-(M : ℝ)⁻¹) :=
        rpow_le_rpow_of_nonpos (by positivity) inf_le_right $ neg_nonpos.2 $ by positivity
    _ ≤ r ^ (-(1 + log r⁻¹)⁻¹) :=
        rpow_le_rpow_of_exponent_ge (by positivity) inf_le_left $ neg_le_neg $ inv_le_inv_of_le
          (by positivity) $ (Nat.le_ceil _).trans $
            mod_cast Nat.le_mul_of_pos_left _ (by positivity)
    _ ≤ r ^ (-(0 + log r⁻¹)⁻¹) := by
      obtain hr | hr : r = 1 ∨ r < 1 := inf_le_left.eq_or_lt
      · simp [hr]
      have : 0 < log r⁻¹ := log_pos <| one_lt_inv (by positivity) hr
      exact rpow_le_rpow_of_exponent_ge (by positivity) inf_le_left (by gcongr; exact zero_le_one)
    _ = r ^ (log r)⁻¹ := by simp [inv_neg]
    _ ≤ exp 1 := rpow_inv_log_le_exp_one

theorem linfty_almost_periodicity_boosted (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (k : ℕ) (hk : k ≠ 0)
    (hK₂ : 2 ≤ K) (hK : σ[A, S] ≤ K) (hS : S.Nonempty)
    (B C : Finset G) (hB : B.Nonempty) (hC : C.Nonempty) :
    ∃ T : Finset G,
      K ^ (-4096 * ⌈𝓛 (C.card / B.card)⌉ * k ^ 2/ ε ^ 2) * S.card ≤ T.card ∧
      ‖μ T ∗^ k ∗ (μ_[ℂ] A ∗ 𝟭 B ∗ μ C) - μ A ∗ 𝟭 B ∗ μ C‖_[∞] ≤ ε := by
  obtain ⟨T, hKT, hT⟩ := linfty_almost_periodicity (ε / k) (by positivity)
    (div_le_one_of_le (hε₁.trans $ mod_cast Nat.one_le_iff_ne_zero.2 hk) $ by positivity) hK₂ hK
    _ _ hB hC
  refine ⟨T, by simpa only [div_pow, div_div_eq_mul_div] using hKT, ?_⟩
  set F := μ_[ℂ] A ∗ 𝟭 B ∗ μ C
  have hT' : T.Nonempty := by
    have : (0 : ℝ) < T.card := hKT.trans_lt' $ by positivity
    simpa [card_pos] using this
  calc
    (‖μ T ∗^ k ∗ F - F‖_[∞] : ℝ)
      = ‖𝔼 a ∈ T ^^ k, (τ (∑ i, a i) F - F)‖_[∞] := by
        rw [mu_iterConv_conv, expect_sub_distrib, expect_const hT'.piFinset_const]
    _ ≤ 𝔼 a ∈ T ^^ k, ‖τ (∑ i, a i) F - F‖_[∞] := dLpNorm_expect_le le_top
    _ ≤ 𝔼 _a ∈ T ^^ k, ε := ?_
    _ = ε := by rw [expect_const hT'.piFinset_const]
  push_cast
  refine expect_le_expect fun x hx ↦
  calc
    (‖τ (∑ i, x i) F - F‖_[⊤] : ℝ)
    _ ≤ ∑ i, ‖τ (x i) F - F‖_[⊤] := dLpNorm_translate_sum_sub_le le_top _ _ _
    _ ≤ ∑ _i, ε / k := by push_cast; exact sum_le_sum fun i _ ↦ hT _ $ Fintype.mem_piFinset.1 hx _
    _ = ε := by simp only [sum_const, card_fin, nsmul_eq_mul]; rw [mul_div_cancel₀]; positivity

end AlmostPeriodicity
