import data.finset.pointwise
import data.real.nnreal
import mathlib.algebra.big_operators.expect
import mathlib.algebra.star.self_adjoint
import mathlib.data.fintype.lattice
import prereqs.translate

open finset fintype (card) function
open_locale big_operators expectations pointwise

/-! ### Indicator -/

variables {ι α β γ : Type*} [decidable_eq α]

section semiring
variables [semiring β] [semiring γ] {s : finset α}

def indicate (s : finset α) (a : α) : β := ite (a ∈ s) 1 0

notation (name := indicate) `𝟭 ` := indicate

notation (name := indicate_ascripted) `𝟭_[` β `] ` := @indicate _ β _ _

lemma indicate_apply (x : α) : 𝟭_[β] s x = ite (x ∈ s) 1 0 := rfl

@[simp] lemma indicate_empty : (𝟭 ∅ : α → β) = 0 := by ext; simp [indicate]

@[simp] lemma indicate_univ [fintype α] : (𝟭 finset.univ : α → β) = 1 :=
by ext; simp [indicate]

lemma indicate_inter_apply (s t : finset α) (x : α) : 𝟭_[β] (s ∩ t) x = 𝟭 s x * 𝟭 t x :=
by simp [indicate_apply, ite_and]

lemma indicate_inter (s t : finset α) : 𝟭_[β] (s ∩ t) = 𝟭 s * 𝟭 t :=
funext $ indicate_inter_apply _ _

lemma map_indicate (f : β →+* γ) (s : finset α) (x : α) : f (𝟭 s x) = 𝟭 s x :=
ring_hom.map_ite_one_zero _ _

variables (β)

@[simp] lemma indicate_image {α' : Type*} [decidable_eq α'] (e : α ≃ α') (s : finset α) (a : α') :
  𝟭_[β] (s.image e) a = 𝟭 s (e.symm a) :=
by simp only [indicate, ←e.injective.mem_finset_image, equiv.apply_symm_apply]

section nontrivial
variables {β} [nontrivial β] {a : α}

@[simp] lemma indicate_eq_zero : 𝟭_[β] s a = 0 ↔ a ∉ s := one_ne_zero.ite_eq_right_iff

lemma indicate_ne_zero : 𝟭_[β] s a ≠ 0 ↔ a ∈ s := one_ne_zero.ite_ne_right_iff

variables (β)

@[simp] lemma support_indicate : support (𝟭_[β] s) = s := by ext; exact indicate_ne_zero

end nontrivial

lemma sum_indicate [fintype α] (s : finset α) : ∑ x, 𝟭_[β] s x = s.card :=
by simp [indicate_apply, ←finset.mem_coe, set.filter_mem_univ_eq_to_finset]

lemma card_eq_sum_indicate [fintype α] (s : finset α) : s.card = ∑ x, 𝟭_[ℕ] s x :=
(sum_indicate _ _).symm

lemma translate_indicate [add_comm_group α] (a : α) (s : finset α) : τ a (𝟭_[β] s) = 𝟭 (a +ᵥ s) :=
by ext; simp [indicate_apply, ←neg_vadd_mem_iff, sub_eq_neg_add]

variables {β} [star_ring β]

lemma indicate_is_self_adjoint (s : finset α) : is_self_adjoint (𝟭_[β] s) :=
pi.is_self_adjoint.2 $ λ g, by rw [indicate]; split_ifs; simp

end semiring

section comm_semiring
variables [comm_semiring β]

lemma indicate_inf_apply [fintype α] (s : finset ι) (t : ι → finset α) (x : α) :
  𝟭_[β] (s.inf t) x = ∏ i in s, 𝟭 (t i) x :=
by simp [indicate_apply, mem_inf, prod_boole]

lemma indicate_inf [fintype α] (s : finset ι) (t : ι → finset α) (x : α) :
  𝟭_[β] (s.inf t) = ∏ i in s, 𝟭 (t i) :=
funext $ λ x, by rw [finset.prod_apply, indicate_inf_apply]

end comm_semiring

section semifield
variables [fintype ι] [decidable_eq ι] [semifield β]

lemma expect_indicate (s : finset ι) : 𝔼 x, 𝟭_[β] s x = s.card / fintype.card ι :=
begin
  simp only [expect_univ, indicate],
  rw [←sum_filter, filter_mem_eq_inter, univ_inter, sum_const, nat.smul_one_eq_coe],
end

end semifield

namespace nnreal
open_locale nnreal

@[simp, norm_cast] lemma coe_indicate' (s : finset α) (x : α) : ↑(𝟭_[ℝ≥0] s x) = 𝟭_[ℝ] s x :=
map_indicate nnreal.to_real_hom _ _

@[simp] lemma coe_comp_indicate (s : finset α) : coe ∘ 𝟭_[ℝ≥0] s = 𝟭_[ℝ] s :=
by ext; exact coe_indicate' _ _

end nnreal

section ordered_semiring
variables [ordered_semiring β] {s : finset α}

@[simp] lemma indicate_nonneg : 0 ≤ 𝟭_[β] s :=
λ a, by rw indicate_apply; split_ifs; norm_num

@[simp] lemma indicate_pos [nontrivial β] : 0 < 𝟭_[β] s ↔ s.nonempty :=
by simpa [indicate_apply, pi.lt_def, function.funext_iff, lt_iff_le_and_ne, @eq_comm β 0]

end ordered_semiring

/-! ### Normalised indicator -/

section division_semiring
variables [division_semiring β] [division_semiring γ] {s : finset α}

/-- The normalised indicate of a set. -/
def mu (s : finset α) : α → β := (s.card : β)⁻¹ • 𝟭 s

notation `μ ` := mu

notation `μ_[` β `] ` := @mu _ β _ _

lemma mu_apply (x : α) : μ s x = (s.card : β)⁻¹ * ite (x ∈ s) 1 0 := rfl

@[simp] lemma mu_empty : (μ ∅ : α → β) = 0 := by ext; simp [mu]

lemma map_mu (f : β →+* γ) (s : finset α) (x : α) : f (μ s x) = μ s x :=
by simp_rw [mu, pi.smul_apply, smul_eq_mul, map_mul, map_indicate, map_inv₀, map_nat_cast]

variables (β)

section nontrivial
variables {β} [nontrivial β] [char_zero β] {a : α}

@[simp] lemma mu_eq_zero : μ_[β] s a = 0 ↔ a ∉ s :=
begin
  simp only [mu_apply, mul_boole, ite_eq_right_iff, inv_eq_zero, nat.cast_eq_zero, card_eq_zero],
  refine imp_congr_right (λ ha, _),
  simp only [ne_empty_of_mem ha],
end

lemma mu_ne_zero : μ_[β] s a ≠ 0 ↔ a ∈ s := mu_eq_zero.not_left

variables (β)

@[simp] lemma support_mu (s : finset α) : support (μ_[β] s) = s :=
by ext; simpa [mu_apply, ne_empty_of_mem] using ne_empty_of_mem

end nontrivial

lemma card_smul_mu [char_zero β] (s : finset α) : s.card • μ_[β] s = 𝟭 s :=
begin
  ext x : 1,
  rw [pi.smul_apply, mu_apply, indicate_apply, nsmul_eq_mul],
  split_ifs,
  { rw [mul_one, mul_inv_cancel],
    rw [nat.cast_ne_zero, ←pos_iff_ne_zero, finset.card_pos],
    exact ⟨_, h⟩ },
  { rw [mul_zero, mul_zero] }
end

lemma card_smul_mu_apply [char_zero β] (s : finset α) (x : α) : s.card • μ_[β] s x = 𝟭 s x :=
congr_fun (card_smul_mu β _) _

lemma sum_mu [char_zero β] [fintype α] (hs : s.nonempty) : ∑ x, μ_[β] s x = 1 :=
by { simpa [mu_apply] using mul_inv_cancel _, exact nat.cast_ne_zero.2 hs.card_pos.ne' }

lemma translate_mu [add_comm_group α] (a : α) (s : finset α) : τ a (μ_[β] s) = μ (a +ᵥ s) :=
by ext; simp [mu_apply, ←neg_vadd_mem_iff, sub_eq_neg_add]

end division_semiring

section semifield
variables (β) [semifield β] {s : finset α}

lemma expect_mu [char_zero β] [fintype α] (hs : s.nonempty) : 𝔼 x, μ_[β] s x = (card α)⁻¹ :=
by rw [expect, card_univ, sum_mu _ hs, one_div]; apply_instance

end semifield

namespace nnreal
open_locale nnreal

@[simp, norm_cast] lemma coe_mu (s : finset α) (x : α) : ↑(μ_[ℝ≥0] s x) = μ_[ℝ] s x :=
map_mu nnreal.to_real_hom _ _

@[simp] lemma coe_comp_mu (s : finset α) : coe ∘ μ_[ℝ≥0] s = μ_[ℝ] s :=
by ext; exact coe_mu _ _

end nnreal

section linear_ordered_semifield
variables [linear_ordered_semifield β] {s : finset α}

@[simp] lemma mu_nonneg : 0 ≤ μ_[β] s := λ a, by rw mu_apply; split_ifs; norm_num

@[simp] lemma mu_pos : 0 < μ_[β] s ↔ s.nonempty :=
begin
  have : ¬ s = ∅ ↔ s.nonempty := finset.nonempty_iff_ne_empty.symm,
  simp [pi.lt_def, mu_apply, function.funext_iff, lt_iff_le_and_ne, @eq_comm β 0, this,
    finset.nonempty],
end

end linear_ordered_semifield

namespace tactic
open positivity

private lemma indicate_pos_of_nonempty [ordered_semiring β] [nontrivial β]
  {s : finset α} : s.nonempty → 0 < 𝟭_[β] s := indicate_pos.2

private lemma mu_pos_of_nonempty [linear_ordered_field β] {s : finset α} :
  s.nonempty → 0 < μ_[β] s := mu_pos.2

/-- Extension for the `positivity` tactic: multiplication is nonnegative/positive/nonzero if both
multiplicands are. -/
@[positivity]
meta def positivity_indicate : expr → tactic strictness
| e@`(@indicate %%α %%β %%hα %%hβ %%s) := (do
    p ← to_expr ``(finset.nonempty %%s) >>= find_assumption,
    positive <$> mk_mapp ``indicate_pos_of_nonempty [α, β, none, none, none, none, p]) <|> do
    nonnegative <$> mk_mapp ``indicate_nonneg [α, β, none, none, s]
| e@`(@mu %%α %%β %%hβ %%hα %%s) := (do
    p ← to_expr ``(finset.nonempty %%s) >>= find_assumption,
    positive <$> mk_app ``mu_pos_of_nonempty [p]) <|>
    nonnegative <$> mk_mapp ``mu_nonneg [α, β, none, none, s]
| e := pp e >>= fail ∘ format.bracket "The expression `" "` isn't of the form `f ∗ g` or `f ○ g`"

variables [linear_ordered_field β] {s : finset α}

example : 0 ≤ 𝟭_[β] s := by positivity
example : 0 ≤ μ_[β] s := by positivity
example (hs : s.nonempty) : 0 < 𝟭_[β] s := by positivity
example (hs : s.nonempty) : 0 < μ_[β] s := by positivity

end tactic
