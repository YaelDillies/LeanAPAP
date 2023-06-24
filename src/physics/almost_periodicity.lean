import misc
import mathlib.convolution

/-!
# Almost-periodicity
-/

variables {G : Type*} [fintype G] [decidable_eq G] [add_comm_group G]

open_locale big_operators pointwise
open finset

namespace almost_periodicity

def L_prop (k m : ℕ) (ε : ℝ) (f : G → ℂ) (A : finset G) (a : fin k → G) : Prop :=
‖λ x : G, ∑ i : fin k, f (x - a i) - (k • (mu A ∗ f)) x‖_[2 * m] ≤ k * ε * ‖f‖_[2 * m]

noncomputable instance (k m : ℕ) (ε : ℝ) (f : G → ℂ) (A : finset G) :
  decidable_pred (L_prop k m ε f A) := classical.dec_pred _

noncomputable def L (k m : ℕ) (ε : ℝ) (f : G → ℂ) (A : finset G) : finset (fin k → G) :=
((fintype.pi_finset (λ i : fin k, A)).filter (L_prop k m ε f A))

lemma lemma28 {ε : ℝ} {m : ℕ} {A : finset G} {f : G → ℂ} {k : ℕ}
  (hε : 0 < ε) (hm : 1 ≤ m) (hk : (256 : ℝ) * m / ε ^ 2 ≤ k) :
  A.card ^ k / 2 ≤ (L k m ε f A).card :=
sorry

lemma just_the_triangle_inequality {ε : ℝ} {m : ℕ} {A : finset G} {f : G → ℂ} {k : ℕ} {t : G}
  {a : fin k → G} (ha : a ∈ L k m ε f A) (ha' : a + (λ _, t) ∈ L k m ε f A) (hk : 0 < k)
  (hm : 1 ≤ m) :
  ‖τ (-t) (mu A ∗ f) - mu A ∗ f‖_[2 * m] ≤ 2 * ε * ‖f‖_[2 * m] :=
begin
  let f₁ : G → ℂ := λ x, ∑ i, f (x - a i),
  let f₂ : G → ℂ := λ x, ∑ i, f (x - a i - t),
  have hp : (1 : ennreal) ≤ 2 * m := by norm_cast; linarith,
  have h₁ : ‖f₁ - k • (mu A ∗ f)‖_[2*m] ≤ k * ε * ‖f‖_[2 * m],
  { rw [L, finset.mem_filter] at ha, exact ha.2 },
  have h₂ : ‖f₂ - k • (mu A ∗ f)‖_[2*m] ≤ k * ε * ‖f‖_[2 * m],
  { rw [L, finset.mem_filter, L_prop] at ha',
    refine ha'.2.trans_eq' _,
    congr' with i : 1,
    simp [f₂, sub_sub] },
  have h₃ : f₂ = τ t f₁,
  { ext i : 1,
    rw translate_apply,
    refine finset.sum_congr rfl (λ j hj, _),
    rw sub_right_comm },
  have h₄₁ : ‖τ t f₁ - k • (mu A ∗ f)‖_[2 * m] = ‖τ (-t) (τ t f₁ - k • (mu A ∗ f))‖_[2 * m],
  { rw Lpnorm_translate },
  have h₄ : ‖τ t f₁ - k • (mu A ∗ f)‖_[2 * m] = ‖f₁ - τ (-t) (k • (mu A ∗ f))‖_[2 * m],
  { rw [h₄₁, translate_sub_right, translate_translate],
    simp },
  have h₅₁ : ‖τ (-t) (k • (mu A ∗ f)) - f₁‖_[2 * m] ≤ k * ε * ‖f‖_[2 * m],
  { rwa [Lpnorm_sub_comm hp, ←h₄, ←h₃] },
  have : (0 : ℝ) < k, by positivity,
  refine le_of_mul_le_mul_left _ this,
  rw [←nsmul_eq_mul, ←lpnorm_nsmul hp, nsmul_sub, nsmul_translate, mul_assoc, mul_left_comm,
    two_mul ((k : ℝ) * _), ←mul_assoc],
  exact (lpnorm_sub_le _ _ _ hp).trans (add_le_add h₅₁ h₁),
end

def _root_.finset.wide_diag (k : ℕ) (S : finset G) : finset (fin k → G) := S.image (λ i _, i)
def fintype_wide_diag (k : ℕ) : finset (fin k → G) := univ.wide_diag k

lemma _root_.finset.wide_diag_card {k : ℕ} (hk : k ≠ 0) {S : finset G} :
  (S.wide_diag k).card = S.card :=
begin
  cases k,
  { simpa using hk },
  rw [finset.wide_diag, card_image_of_injective],
  intros i j h,
  dsimp at h,
  exact congr_fun h 0,
end

lemma big_shifts_step1 {k : ℕ} {S : finset G} (L : finset (fin k → G)) :
  ∑ x in L + S.wide_diag k, ∑ l in L, ∑ s in S.wide_diag k, ite (l + s = x) 1 0 = L.card * S.card :=
begin
  simp only [@sum_comm _ _ _ _ (L + _)],
  simp only [sum_ite_eq],
  rw sum_const_nat,
  intros l hl,
  rw [sum_const_nat],

end

lemma big_shifts {k : ℕ} {A S : finset G} (L : finset (fin k → G)) :
  ∃ a : fin k → G, a ∈ L ∧
    L.card * S.card ≤ (A + S).card ^ k * (univ.filter (λ t : G, a + (λ _, t) ∈ L)).card :=
begin

end

-- trivially true for other reasons for big ε
theorem almost_periodicity {ε : ℝ} {A S : finset G} {K : ℝ} {f : G → ℂ} {m : ℕ}
  (hε : 0 < ε) (hε' : ε ≤ 1) (hK : ((A + S).card : ℝ) ≤ K * A.card) :
  ∃ T : finset G, K ^ (-2048 * m / ε ^ 2 : ℝ) * S.card ≤ T.card ∧
    ∀ t ∈ T, ‖τ t (mu A ∗ f) - mu A ∗ f‖_[2 * m] ≤ ε * ‖f‖_[2 * m] :=
sorry

end almost_periodicity
