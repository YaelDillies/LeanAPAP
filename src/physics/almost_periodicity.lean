import misc
import mathlib.convolution

/-!
# Almost-periodicity
-/

variables {G : Type*} [fintype G] [decidable_eq G] [add_comm_group G]

open_locale big_operators pointwise

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
  {a : fin k → G} (ha : a ∈ L k m ε f A) (ha' : a + (λ _, t) ∈ L k m ε f A) :
  ‖τ t (mu A ∗ f) - mu A ∗ f‖_[2 * m] ≤ 2 * ε * ‖f‖_[2 * m] :=
sorry

lemma big_shifts {k : ℕ} {A S : finset G} (L : finset (fin k → G)) :
  L.card * S.card ≤
    (A + S).card ^ k * (finset.univ.filter (λ t : G, ∃ a ∈ L, a + (λ _, t) ∈ L)).card :=
sorry

-- trivially true for other reasons for big ε
theorem almost_periodicity {ε : ℝ} {A S : finset G} {K : ℝ} {f : G → ℂ} {m : ℕ}
  (hε : 0 < ε) (hε' : ε ≤ 1) (hK : ((A + S).card : ℝ) ≤ K * A.card) :
  ∃ T : finset G, K ^ (-2048 * m / ε ^ 2 : ℝ) * S.card ≤ T.card ∧
    ∀ t ∈ T, ‖τ t (mu A ∗ f) - mu A ∗ f‖_[2 * m] ≤ ε * ‖f‖_[2 * m] :=
sorry

end almost_periodicity
