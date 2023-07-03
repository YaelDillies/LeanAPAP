import data.finset.pointwise
import mathlib.data.fintype.lattice
import prereqs.translate

open finset function
open_locale big_operators pointwise

/-! ### Indicator -/

variables {ι α β γ : Type*} [decidable_eq α]

section semiring
variables [semiring β] [semiring γ] {s : finset α}

def indicator (s : finset α) (a : α) : β := ite (a ∈ s) 1 0

notation `𝟭 ` := _root_.indicator

notation `𝟭_[` β `] ` := @_root_.indicator _ β _ _

lemma indicator_apply (x : α) : 𝟭_[β] s x = ite (x ∈ s) 1 0 := rfl

@[simp] lemma indicator_empty : (𝟭 ∅ : α → β) = 0 := by ext; simp [indicator]

@[simp] lemma indicator_univ [fintype α] : (𝟭 finset.univ : α → β) = 1 :=
by ext; simp [indicator]

lemma indicator_inter_apply (s t : finset α) (x : α) : 𝟭_[β] (s ∩ t) x = 𝟭 s x * 𝟭 t x :=
by simp [indicator_apply, ite_and]

lemma indicator_inter (s t : finset α) : 𝟭_[β] (s ∩ t) = 𝟭 s * 𝟭 t :=
funext $ indicator_inter_apply _ _

lemma map_indicator (f : β →+* γ) (s : finset α) (x : α) : f (𝟭 s x) = 𝟭 s x :=
ring_hom.map_ite_one_zero _ _

variables (β)

@[simp] lemma support_indicator [nontrivial β] : support (𝟭_[β] s) = s :=
by ext; simp [indicator_apply]

lemma sum_indicator [fintype α] (s : finset α) : ∑ x, 𝟭_[β] s x = s.card :=
by simp [indicator_apply, ←finset.mem_coe, set.filter_mem_univ_eq_to_finset]

lemma translate_indicator [add_comm_group α] (a : α) (s : finset α) : τ a (𝟭_[β] s) = 𝟭 (a +ᵥ s) :=
by ext; simp [indicator_apply, ←neg_vadd_mem_iff, sub_eq_neg_add]

end semiring

section comm_semiring
variables [comm_semiring β]

lemma indicator_inf_apply [fintype α] (s : finset ι) (t : ι → finset α) (x : α) :
  𝟭_[β] (s.inf t) x = ∏ i in s, 𝟭 (t i) x :=
by simp [indicator_apply, mem_inf, prod_boole]

lemma indicator_inf [fintype α] (s : finset ι) (t : ι → finset α) (x : α) :
  𝟭_[β] (s.inf t) = ∏ i in s, 𝟭 (t i) :=
funext $ λ x, by rw [finset.prod_apply, indicator_inf_apply]

end comm_semiring

section ordered_semiring
variables [ordered_semiring β] {s : finset α}

@[simp] lemma indicator_nonneg : 0 ≤ 𝟭_[β] s :=
λ a, by rw indicator_apply; split_ifs; norm_num

@[simp] lemma indicator_pos [nontrivial β] : 0 < 𝟭_[β] s ↔ s.nonempty :=
by simpa [indicator_apply, pi.lt_def, function.funext_iff, lt_iff_le_and_ne, @eq_comm β 0]

end ordered_semiring

/-! ### Normalised indicator -/

section division_semiring
variables [division_semiring β] [division_semiring γ] {s : finset α}

/-- The normalised indicator of a set. -/
def mu (s : finset α) : α → β := (s.card : β)⁻¹ • 𝟭 s

notation `μ ` := mu

notation `μ_[` β `] ` := @mu _ β _ _

lemma mu_apply (x : α) : μ s x = (s.card : β)⁻¹ * ite (x ∈ s) 1 0 := rfl

@[simp] lemma mu_empty : (μ ∅ : α → β) = 0 := by ext; simp [mu]

lemma map_mu (f : β →+* γ) (s : finset α) (x : α) : f (μ s x) = μ s x :=
by simp_rw [mu, pi.smul_apply, smul_eq_mul, map_mul, map_indicator, map_inv₀, map_nat_cast]

variables (β)

@[simp] lemma support_mu [char_zero β] (s : finset α) : support (μ_[β] s) = s :=
by ext; simpa [mu_apply, ne_empty_of_mem] using ne_empty_of_mem

lemma card_smul_mu [char_zero β] (s : finset α) : s.card • μ_[β] s = 𝟭 s :=
begin
  ext x : 1,
  rw [pi.smul_apply, mu_apply, indicator_apply, nsmul_eq_mul],
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

private lemma indicator_pos_of_nonempty [ordered_semiring β] [nontrivial β]
  {s : finset α} : s.nonempty → 0 < 𝟭_[β] s := indicator_pos.2

private lemma mu_pos_of_nonempty [linear_ordered_field β] {s : finset α} :
  s.nonempty → 0 < μ_[β] s := mu_pos.2

/-- Extension for the `positivity` tactic: multiplication is nonnegative/positive/nonzero if both
multiplicands are. -/
@[positivity]
meta def positivity_indicator : expr → tactic strictness
| e@`(@_root_.indicator %%α %%β %%hα %%hβ %%s) := (do
    p ← to_expr ``(finset.nonempty %%s) >>= find_assumption,
    positive <$> mk_mapp ``indicator_pos_of_nonempty [α, β, none, none, none, none, p]) <|> do
    nonnegative <$> mk_mapp ``indicator_nonneg [α, β, none, none, s]
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
