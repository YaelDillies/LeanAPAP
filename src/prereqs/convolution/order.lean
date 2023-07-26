import mathlib.algebra.star.order
import prereqs.convolution.basic

open finset function real
open_locale big_operators complex_conjugate nnreal pointwise

variables {α β : Type*} [fintype α] [decidable_eq α] [add_comm_group α]

section ordered_comm_semiring
variables [ordered_comm_semiring β] [star_ordered_ring β] {f g : α → β}

lemma conv_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ f ∗ g :=
λ a, sum_nonneg $ λ x _, mul_nonneg (hf _) (hg _)

lemma dconv_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ f ○ g :=
λ a, sum_nonneg $ λ x _, mul_nonneg (hf _) $ star_nonneg.2 $ hg _

end ordered_comm_semiring

section strict_ordered_comm_semiring
variables [strict_ordered_comm_semiring β] [star_ordered_ring β] {f g : α → β}

--TODO: Those can probably be generalised to `ordered_comm_semiring` but we don't really care
@[simp] lemma support_conv (hf : 0 ≤ f) (hg : 0 ≤ g) : support (f ∗ g) = support f + support g :=
begin
  refine (support_conv_subset _ _).antisymm _,
  rintro _ ⟨a, b, ha, hb, rfl⟩,
  dsimp,
  rw conv_apply_add,
  exact ne_of_gt (sum_pos' (λ c _, mul_nonneg (hf _) $ hg _) ⟨0, mem_univ _,
    mul_pos ((hf _).lt_of_ne' $ by simpa using ha) ((hg _).lt_of_ne' $ by simpa using hb)⟩),
end

@[simp] lemma support_dconv (hf : 0 ≤ f) (hg : 0 ≤ g) : support (f ○ g) = support f - support g :=
by simpa [sub_eq_add_neg] using support_conv hf (conjneg_nonneg.2 hg)

lemma conv_pos (hf : 0 < f) (hg : 0 < g) : 0 < f ∗ g :=
begin
  rw pi.lt_def at ⊢ hf hg,
  obtain ⟨hf, a, ha⟩ := hf,
  obtain ⟨hg, b, hb⟩ := hg,
  refine ⟨conv_nonneg hf hg, a + b, _⟩,
  rw conv_apply_add,
  exact sum_pos' (λ c _, mul_nonneg (hf _) $ hg _) ⟨0, by simpa using mul_pos ha hb⟩,
end

lemma dconv_pos (hf : 0 < f) (hg : 0 < g) : 0 < f ○ g :=
by rw ←conv_conjneg; exact conv_pos hf (conjneg_pos.2 hg)

end strict_ordered_comm_semiring

section ordered_comm_semiring
variables [ordered_comm_semiring β] [star_ordered_ring β] {f g : α → β} {n : ℕ}

@[simp] lemma iter_conv_nonneg (hf : 0 ≤ f) : ∀ {n}, 0 ≤ f ∗^ n
| 0 := λ _, by dsimp; split_ifs; norm_num
| (n + 1) := conv_nonneg hf iter_conv_nonneg

end ordered_comm_semiring

section strict_ordered_comm_semiring
variables [strict_ordered_comm_semiring β] [star_ordered_ring β] {f g : α → β} {n : ℕ}

@[simp] lemma iter_conv_pos (hf : 0 < f) : ∀ {n}, 0 < f ∗^ n
| 0 := pi.lt_def.2 ⟨iter_conv_nonneg hf.le, 0, by simp⟩
| (n + 1) := conv_pos hf iter_conv_pos

end strict_ordered_comm_semiring

namespace tactic
section
variables [ordered_comm_semiring β] [star_ordered_ring β] {f g : α → β}

private lemma conv_nonneg_of_pos_of_nonneg (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ f ∗ g :=
conv_nonneg hf.le hg

private lemma conv_nonneg_of_nonneg_of_pos (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ f ∗ g :=
conv_nonneg hf hg.le

private lemma dconv_nonneg_of_pos_of_nonneg (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ f ○ g :=
dconv_nonneg hf.le hg

private lemma dconv_nonneg_of_nonneg_of_pos (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ f ○ g :=
dconv_nonneg hf hg.le

end

open positivity

/-- Extension for the `positivity` tactic: convolution/difference convolution/iterated convolution
is nonnegative/positive if both multiplicands are. -/
@[positivity]
meta def positivity_conv : expr → tactic strictness
| e@`(%%f ∗ %%g) := do
  strictness_f ← core f,
  strictness_g ← core g,
  match strictness_f, strictness_g with
  | positive pf, positive pg := positive <$> mk_app ``conv_pos [pf, pg]
  | positive pf, nonnegative pg := nonnegative <$> mk_mapp ``conv_nonneg_of_pos_of_nonneg
      [none, none, none, none, none, none, none, f, g, pf, pg]
  | nonnegative pf, positive pg := nonnegative <$> mk_mapp ``conv_nonneg_of_nonneg_of_pos
      [none, none, none, none, none, none, none, f, g, pf, pg]
  | nonnegative pf, nonnegative pg := nonnegative <$> mk_mapp ``conv_nonneg
      [none, none, none, none, none, none, none, f, g, pf, pg]
  | sf@_, sg@ _ := positivity_fail e f g sf sg
  end
| e@`(%%f ○ %%g) := do
  strictness_f ← core f,
  strictness_g ← core g,
  match strictness_f, strictness_g with
  | positive pf, positive pg := positive <$> mk_app ``dconv_pos [pf, pg]
  | positive pf, nonnegative pg := nonnegative <$> mk_mapp ``dconv_nonneg_of_pos_of_nonneg
      [none, none, none, none, none, none, none, f, g, pf, pg]
  | nonnegative pf, positive pg := nonnegative <$> mk_mapp ``dconv_nonneg_of_nonneg_of_pos
      [none, none, none, none, none, none, none, f, g, pf, pg]
  | nonnegative pf, nonnegative pg := nonnegative <$> mk_mapp ``dconv_nonneg
      [none, none, none, none, none, none, none, f, g, pf, pg]
  | sf@_, sg@ _ := positivity_fail e f g sf sg
  end
| e@`(%%f ∗^ %%n) := do
  strictness_f ← core f,
  match strictness_f with
  | positive p := positive <$> mk_mapp ``iter_conv_pos
      [none, none, none, none, none, none, none, none, p, n]
  | nonnegative p := nonnegative <$> mk_mapp ``iter_conv_nonneg
      [none, none, none, none, none, none, none, none, p, n]
  | _ := failed
  end
| e := pp e >>= fail ∘ format.bracket "The expression `"
    "` isn't of the form `f ∗ g`, `f ○ g` or `f ∗^ n`"

variables [strict_ordered_comm_semiring β] [star_ordered_ring β] {f g : α → β}

example (hf : 0 < f) (hg : 0 < g) : 0 < f ∗ g := by positivity
example (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ f ∗ g := by positivity
example (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ f ∗ g := by positivity
example (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ f ∗ g := by positivity

example (hf : 0 < f) (hg : 0 < g) : 0 < f ○ g := by positivity
example (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ f ○ g := by positivity
example (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ f ○ g := by positivity
example (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ f ○ g := by positivity

example (hf : 0 < f) (n : ℕ) : 0 < f ∗^ n := by positivity
example (hf : 0 ≤ f) (n : ℕ) : 0 ≤ f ∗^ n := by positivity

end tactic
