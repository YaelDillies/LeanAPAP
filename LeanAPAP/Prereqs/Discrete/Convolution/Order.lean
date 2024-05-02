import LeanAPAP.Mathlib.Tactic.Positivity
import LeanAPAP.Prereqs.Discrete.Convolution.Basic

open Finset Function Real
open scoped BigOperators ComplexConjugate NNReal Pointwise

variable {α β : Type*} [Fintype α] [DecidableEq α] [AddCommGroup α]

section OrderedCommSemiring
variable [OrderedCommSemiring β] [StarRing β] [StarOrderedRing β] {f g : α → β}

lemma conv_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ f ∗ g :=
  fun _a ↦ sum_nonneg fun _x _ ↦ mul_nonneg (hf _) (hg _)

lemma dconv_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ f ○ g :=
  fun _a ↦ sum_nonneg fun _x _ ↦ mul_nonneg (hf _) $ star_nonneg_iff.2 $ hg _

end OrderedCommSemiring

section StrictOrderedCommSemiring
variable [StrictOrderedCommSemiring β] [StarRing β] [StarOrderedRing β] {f g : α → β}

--TODO: Those can probably be generalised to `OrderedCommSemiring` but we don't really care
@[simp] lemma support_conv (hf : 0 ≤ f) (hg : 0 ≤ g) : support (f ∗ g) = support f + support g := by
  refine' (support_conv_subset _ _).antisymm _
  rintro _ ⟨a, ha, b, hb, rfl⟩
  rw [mem_support, conv_apply_add]
  exact ne_of_gt $ sum_pos' (fun c _ ↦ mul_nonneg (hf _) $ hg _) ⟨0, mem_univ _,
    mul_pos ((hf _).lt_of_ne' $ by simpa using ha) $ (hg _).lt_of_ne' $ by simpa using hb⟩

@[simp]
lemma support_dconv (hf : 0 ≤ f) (hg : 0 ≤ g) : support (f ○ g) = support f - support g := by
  simpa [sub_eq_add_neg] using support_conv hf (conjneg_nonneg.2 hg)

lemma conv_pos (hf : 0 < f) (hg : 0 < g) : 0 < f ∗ g := by
  rw [Pi.lt_def] at hf hg ⊢
  obtain ⟨hf, a, ha⟩ := hf
  obtain ⟨hg, b, hb⟩ := hg
  refine' ⟨conv_nonneg hf hg, a + b, _⟩
  rw [conv_apply_add]
  exact sum_pos' (fun c _ ↦ mul_nonneg (hf _) $ hg _) ⟨0, by simpa using mul_pos ha hb⟩

lemma dconv_pos (hf : 0 < f) (hg : 0 < g) : 0 < f ○ g := by
  rw [←conv_conjneg]; exact conv_pos hf (conjneg_pos.2 hg)

end StrictOrderedCommSemiring

section OrderedCommSemiring
variable [OrderedCommSemiring β] [StarRing β] [StarOrderedRing β] {f g : α → β} {n : ℕ}

@[simp] lemma iterConv_nonneg (hf : 0 ≤ f) : ∀ {n}, 0 ≤ f ∗^ n
  | 0 => fun _ ↦ by dsimp; split_ifs <;> norm_num
  | n + 1 => conv_nonneg (iterConv_nonneg hf) hf

end OrderedCommSemiring

section StrictOrderedCommSemiring
variable [StrictOrderedCommSemiring β] [StarRing β] [StarOrderedRing β] {f g : α → β} {n : ℕ}

@[simp] lemma iterConv_pos (hf : 0 < f) : ∀ {n}, 0 < f ∗^ n
  | 0 => Pi.lt_def.2 ⟨iterConv_nonneg hf.le, 0, by simp⟩
  | n + 1 => conv_pos (iterConv_pos hf) hf

end StrictOrderedCommSemiring

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function

section
variable [OrderedCommSemiring β] [StarRing β] [StarOrderedRing β] {f g : α → β}

private lemma conv_nonneg_of_pos_of_nonneg (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ f ∗ g :=
  conv_nonneg hf.le hg

private lemma conv_nonneg_of_nonneg_of_pos (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ f ∗ g :=
  conv_nonneg hf hg.le

private lemma dconv_nonneg_of_pos_of_nonneg (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ f ○ g :=
  dconv_nonneg hf.le hg

private lemma dconv_nonneg_of_nonneg_of_pos (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ f ○ g :=
  dconv_nonneg hf hg.le

end

-- TODO: Make it sound again :(
set_option linter.unusedVariables false in
/-- The `positivity` extension which identifies expressions of the form `f ∗ g`,
such that `positivity` successfully recognises both `f` and `g`. -/
@[positivity _ ∗ _] def evalConv : PositivityExt where eval {u α} zα pα e := do
  let .app (.app (_f : Q($α → $α → $α)) (a : Q($α))) (b : Q($α)) ← withReducible (whnf e)
    | throwError "not ∗"
  let ra ← core zα pα a; let rb ← core zα pα b
  match ra, rb with
  | .positive pa, .positive pb => return .positive q(dummy_pos_of_pos_pos $pa $pb)
  | .positive pa, .nonnegative pb => return .nonnegative q(dummy_nng_of_pos_nng $pa $pb)
  | .nonnegative pa, .positive pb => return .nonnegative q(dummy_nng_of_nng_pos $pa $pb)
  | .nonnegative pa, .nonnegative pb => return .nonnegative q(dummy_nng_of_nng_nng $pa $pb)
  | .positive pa, .nonzero pb => return .nonzero q(dummy_nzr_of_pos_nzr $pa $pb)
  | .nonzero pa, .positive pb => return .nonzero q(dummy_nzr_of_nzr_pos $pa $pb)
  | .nonzero pa, .nonzero pb => return .nonzero q(dummy_nzr_of_nzr_nzr $pa $pb)
  | _, _ => pure .none

-- TODO: Make it sound again :(
set_option linter.unusedVariables false in
/-- The `positivity` extension which identifies expressions of the form `f ○ g`,
such that `positivity` successfully recognises both `f` and `g`. -/
@[positivity _ ○ _] def evalDConv : PositivityExt where eval {u α} zα pα e := do
  let .app (.app (_f : Q($α → $α → $α)) (a : Q($α))) (b : Q($α)) ← withReducible (whnf e)
    | throwError "not ∗"
  let ra ← core zα pα a; let rb ← core zα pα b
  match ra, rb with
  | .positive pa, .positive pb => return .positive q(dummy_pos_of_pos_pos $pa $pb)
  | .positive pa, .nonnegative pb => return .nonnegative q(dummy_nng_of_pos_nng $pa $pb)
  | .nonnegative pa, .positive pb => return .nonnegative q(dummy_nng_of_nng_pos $pa $pb)
  | .nonnegative pa, .nonnegative pb => return .nonnegative q(dummy_nng_of_nng_nng $pa $pb)
  | .positive pa, .nonzero pb => return .nonzero q(dummy_nzr_of_pos_nzr $pa $pb)
  | .nonzero pa, .positive pb => return .nonzero q(dummy_nzr_of_nzr_pos $pa $pb)
  | .nonzero pa, .nonzero pb => return .nonzero q(dummy_nzr_of_nzr_nzr $pa $pb)
  | _, _ => pure .none

-- TODO: Make it sound again :(
set_option linter.unusedVariables false in
/-- The `positivity` extension which identifies expressions of the form `f ○ g`,
such that `positivity` successfully recognises both `f` and `g`. -/
@[positivity _ ∗^ _] def evalIterConv : PositivityExt where eval {u α} zα pα e := do
  let .app (.app (_f : Q($α → $α → $α)) (a : Q($α))) (b : Q($α)) ← withReducible (whnf e)
    | throwError "not ∗"
  match ← core zα pα a with
  | .positive pa => return .positive q(dummy_pos_of_pos $pa)
  | .nonnegative pa => return .nonnegative q(dummy_nng_of_nng $pa)
  | .nonzero pa => return .nonzero q(dummy_nzr_of_nzr $pa)
  | _ => return .none

variable [StrictOrderedCommSemiring β] [StarRing β] [StarOrderedRing β] {f g : α → β}

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

end Mathlib.Meta.Positivity
