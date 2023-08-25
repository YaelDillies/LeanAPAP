import Mathlib.Data.Finset.Pointwise
import Mathlib.Data.Real.Nnreal
import LeanAPAP.Mathlib.Algebra.BigOperators.Expect
import LeanAPAP.Mathlib.Algebra.Star.SelfAdjoint
import LeanAPAP.Mathlib.Data.Fintype.Lattice
import LeanAPAP.Prereqs.Translate

#align_import prereqs.indicator

open Finset

open Fintype (card)

open Function

open scoped BigOperators Expectations Pointwise

/-! ### Indicator -/

variable {ι α β γ : Type*} [DecidableEq α]

section Semiring
variable [Semiring β] [Semiring γ] {s : Finset α}

def indicate (s : Finset α) (a : α) : β :=
  ite (a ∈ s) 1 0

notation "𝟭 " => indicate

notation "𝟭_[" β "] " => @indicate _ β _ _

lemma indicate_apply (x : α) : 𝟭_[β] s x = ite (x ∈ s) 1 0 := rfl

@[simp]
lemma indicate_empty : (𝟭 ∅ : α → β) = 0 := by ext <;> simp [indicate]

@[simp]
lemma indicate_univ [Fintype α] : (𝟭 Finset.univ : α → β) = 1 := by ext <;> simp [indicate]

lemma indicate_inter_apply (s t : Finset α) (x : α) : 𝟭_[β] (s ∩ t) x = 𝟭 s x * 𝟭 t x := by
  simp [indicate_apply, ite_and]

lemma indicate_inter (s t : Finset α) : 𝟭_[β] (s ∩ t) = 𝟭 s * 𝟭 t :=
  funext <| indicate_inter_apply _ _

lemma map_indicate (f : β →+* γ) (s : Finset α) (x : α) : f (𝟭 s x) = 𝟭 s x :=
  RingHom.map_ite_one_zero _ _

variable (β)

@[simp]
lemma indicate_image {α' : Type*} [DecidableEq α'] (e : α ≃ α') (s : Finset α) (a : α') :
    𝟭_[β] (s.image e) a = 𝟭 s (e.symm a) := by
  simp only [indicate, ← e.injective.mem_finset_image, Equiv.apply_symm_apply]

section Nontrivial
variable {β} [Nontrivial β] {a : α}

@[simp]
lemma indicate_eq_zero : 𝟭_[β] s a = 0 ↔ a ∉ s :=
  one_ne_zero.ite_eq_right_iff

lemma indicate_ne_zero : 𝟭_[β] s a ≠ 0 ↔ a ∈ s :=
  one_ne_zero.ite_ne_right_iff

variable (β)

@[simp]
lemma support_indicate : support (𝟭_[β] s) = s := by ext <;> exact indicate_ne_zero

end Nontrivial

lemma sum_indicate [Fintype α] (s : Finset α) : ∑ x, 𝟭_[β] s x = s.card := by
  simp [indicate_apply, ← Finset.mem_coe, Set.filter_mem_univ_eq_toFinset]

lemma card_eq_sum_indicate [Fintype α] (s : Finset α) : s.card = ∑ x, 𝟭_[ℕ] s x :=
  (sum_indicate _ _).symm

lemma translate_indicate [AddCommGroup α] (a : α) (s : Finset α) : τ a (𝟭_[β] s) = 𝟭 (a +ᵥ s) := by ext <;> simp [indicate_apply, ← neg_vadd_mem_iff, sub_eq_neg_add]

variable {β} [StarRing β]

lemma indicate_isSelfAdjoint (s : Finset α) : IsSelfAdjoint (𝟭_[β] s) :=
  Pi.isSelfAdjoint.2 λ g => by rw [indicate] <;> split_ifs <;> simp

end Semiring

section CommSemiring
variable [CommSemiring β]

lemma indicate_inf_apply [Fintype α] (s : Finset ι) (t : ι → Finset α) (x : α) :
    𝟭_[β] (s.inf t) x = ∏ i in s, 𝟭 (t i) x := by simp [indicate_apply, mem_inf, prod_boole]

lemma indicate_inf [Fintype α] (s : Finset ι) (t : ι → Finset α) (x : α) :
    𝟭_[β] (s.inf t) = ∏ i in s, 𝟭 (t i) :=
  funext λ x => by rw [Finset.prod_apply, indicate_inf_apply]

end CommSemiring

section Semifield
variable [Fintype ι] [DecidableEq ι] [Semifield β]

lemma expect_indicate (s : Finset ι) : 𝔼 x, 𝟭_[β] s x = s.card / Fintype.card ι := by
  simp only [expect_univ, indicate]
  rw [← sum_filter, filter_mem_eq_inter, univ_inter, sum_const, Nat.smul_one_eq_coe]

end Semifield

namespace NNReal
open scoped NNReal

@[simp, norm_cast]
lemma coe_indicate' (s : Finset α) (x : α) : ↑(𝟭_[ℝ≥0] s x) = 𝟭_[ℝ] s x :=
  map_indicate NNReal.toRealHom _ _

@[simp]
lemma coe_comp_indicate (s : Finset α) : coe ∘ 𝟭_[ℝ≥0] s = 𝟭_[ℝ] s := by
  ext <;> exact coe_indicate' _ _

end NNReal

section OrderedSemiring
variable [OrderedSemiring β] {s : Finset α}

@[simp]
lemma indicate_nonneg : 0 ≤ 𝟭_[β] s := λ a => by rw [indicate_apply] <;> split_ifs <;> norm_num

@[simp]
lemma indicate_pos [Nontrivial β] : 0 < 𝟭_[β] s ↔ s.Nonempty := by
  simpa [indicate_apply, Pi.lt_def, Function.funext_iff, lt_iff_le_and_ne, @eq_comm β 0]

end OrderedSemiring

/-! ### Normalised indicator -/

section DivisionSemiring
variable [DivisionSemiring β] [DivisionSemiring γ] {s : Finset α}

/-- The normalised indicate of a set. -/
def mu (s : Finset α) : α → β :=
  (s.card : β)⁻¹ • 𝟭 s

notation "μ " => mu

notation "μ_[" β "] " => @mu _ β _ _

lemma mu_apply (x : α) : μ s x = (s.card : β)⁻¹ * ite (x ∈ s) 1 0 := rfl

@[simp]
lemma mu_empty : (μ ∅ : α → β) = 0 := by ext <;> simp [mu]

lemma map_mu (f : β →+* γ) (s : Finset α) (x : α) : f (μ s x) = μ s x := by
  simp_rw [mu, Pi.smul_apply, smul_eq_mul, map_mul, map_indicate, map_inv₀, map_natCast]

variable (β)

section Nontrivial
variable {β} [Nontrivial β] [CharZero β] {a : α}

@[simp]
lemma mu_eq_zero : μ_[β] s a = 0 ↔ a ∉ s := by
  simp only [mu_apply, mul_boole, ite_eq_right_iff, inv_eq_zero, Nat.cast_eq_zero, card_eq_zero]
  refine' imp_congr_right λ ha => _
  simp only [ne_empty_of_mem ha]

lemma mu_ne_zero : μ_[β] s a ≠ 0 ↔ a ∈ s :=
  mu_eq_zero.not_left

variable (β)

@[simp]
lemma support_mu (s : Finset α) : support (μ_[β] s) = s := by
  ext <;> simpa [mu_apply, ne_empty_of_mem] using ne_empty_of_mem

end Nontrivial

lemma card_smul_mu [CharZero β] (s : Finset α) : s.card • μ_[β] s = 𝟭 s := by
  ext x : 1
  rw [Pi.smul_apply, mu_apply, indicate_apply, nsmul_eq_mul]
  split_ifs
  · rw [mul_one, mul_inv_cancel]
    rw [Nat.cast_ne_zero, ← pos_iff_ne_zero, Finset.card_pos]
    exact ⟨_, h⟩
  · rw [MulZeroClass.mul_zero, MulZeroClass.mul_zero]

lemma card_smul_mu_apply [CharZero β] (s : Finset α) (x : α) : s.card • μ_[β] s x = 𝟭 s x :=
  congr_λ (card_smul_mu β _) _

lemma sum_mu [CharZero β] [Fintype α] (hs : s.Nonempty) : ∑ x, μ_[β] s x = 1 := by
  simpa [mu_apply] using mul_inv_cancel _; exact Nat.cast_ne_zero.2 hs.card_pos.ne'

lemma translate_mu [AddCommGroup α] (a : α) (s : Finset α) : τ a (μ_[β] s) = μ (a +ᵥ s) := by
  ext <;> simp [mu_apply, ← neg_vadd_mem_iff, sub_eq_neg_add]

end DivisionSemiring

section Semifield
variable (β) [Semifield β] {s : Finset α}

lemma expect_mu [CharZero β] [Fintype α] (hs : s.Nonempty) : 𝔼 x, μ_[β] s x = (card α)⁻¹ := by
  rw [expect, card_univ, sum_mu _ hs, one_div] <;> infer_instance

end Semifield

namespace IsROrC
variable {𝕜 : Type*} [IsROrC 𝕜] [Fintype α] (s : Finset α) (a : α)

@[simp, norm_cast]
lemma coe_mu : ↑(μ_[ℝ] s a) = μ_[𝕜] s a :=
  map_mu (algebraMap ℝ 𝕜) _ _

@[simp]
lemma coe_comp_mu : coe ∘ μ_[ℝ] s = μ_[𝕜] s :=
  funext <| coe_mu _

end IsROrC

namespace NNReal
open scoped NNReal

@[simp, norm_cast]
lemma coe_mu (s : Finset α) (x : α) : ↑(μ_[ℝ≥0] s x) = μ_[ℝ] s x :=
  map_mu NNReal.toRealHom _ _

@[simp]
lemma coe_comp_mu (s : Finset α) : coe ∘ μ_[ℝ≥0] s = μ_[ℝ] s :=
  funext <| coe_mu _

end NNReal

section LinearOrderedSemifield
variable [LinearOrderedSemifield β] {s : Finset α}

@[simp]
lemma mu_nonneg : 0 ≤ μ_[β] s := λ a => by rw [mu_apply] <;> split_ifs <;> norm_num

@[simp]
lemma mu_pos : 0 < μ_[β] s ↔ s.Nonempty := by
  have : ¬s = ∅ ↔ s.nonempty := finset.nonempty_iff_ne_empty.symm
  simp [Pi.lt_def, mu_apply, Function.funext_iff, lt_iff_le_and_ne, @eq_comm β 0, this,
    Finset.Nonempty]

end LinearOrderedSemifield

namespace Tactic
open Positivity

private lemma indicate_pos_of_nonempty [OrderedSemiring β] [Nontrivial β] {s : Finset α} :
    s.Nonempty → 0 < 𝟭_[β] s :=
  indicate_pos.2

private lemma mu_pos_of_nonempty [LinearOrderedField β] {s : Finset α} :
    s.Nonempty → 0 < μ_[β] s :=
  mu_pos.2

/-- Extension for the `positivity` tactic: multiplication is nonnegative/positive/nonzero if both
multiplicands are. -/
@[positivity]
unsafe def positivity_indicate : expr → tactic strictness
  | e@q(@indicate $(α) $(β) $(hα) $(hβ) $(s)) =>
    (do
        let p ← to_expr ``(Finset.Nonempty $(s)) >>= find_assumption
        positive <$> mk_mapp `` indicate_pos_of_nonempty [α, β, none, none, none, none, p]) <|>
      do
      nonnegative <$> mk_mapp `` indicate_nonneg [α, β, none, none, s]
  | e@q(@mu $(α) $(β) $(hβ) $(hα) $(s)) =>
    (do
        let p ← to_expr ``(Finset.Nonempty $(s)) >>= find_assumption
        positive <$> mk_app `` mu_pos_of_nonempty [p]) <|>
      nonnegative <$> mk_mapp `` mu_nonneg [α, β, none, none, s]
  | e => pp e >>= fail ∘ format.bracket "The expression `" "` isn't of the form `f ∗ g` or `f ○ g`"

variable [LinearOrderedField β] {s : Finset α}

example : 0 ≤ 𝟭_[β] s := by positivity

example : 0 ≤ μ_[β] s := by positivity

example (hs : s.Nonempty) : 0 < 𝟭_[β] s := by positivity

example (hs : s.Nonempty) : 0 < μ_[β] s := by positivity

end Tactic
