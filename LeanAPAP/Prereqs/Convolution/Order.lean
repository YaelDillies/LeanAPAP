import Project.Mathlib.Algebra.Star.Order
import Project.Prereqs.Convolution.Basic

#align_import prereqs.convolution.order

open Finset Function Real

open scoped BigOperators ComplexConjugate NNReal Pointwise

variable {α β : Type _} [Fintype α] [DecidableEq α] [AddCommGroup α]

section OrderedCommSemiring

variable [OrderedCommSemiring β] [StarOrderedRing β] {f g : α → β}

theorem conv_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ f ∗ g := fun a =>
  sum_nonneg fun x _ => mul_nonneg (hf _) (hg _)

theorem dconv_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ f ○ g := fun a =>
  sum_nonneg fun x _ => mul_nonneg (hf _) <| star_nonneg.2 <| hg _

end OrderedCommSemiring

section StrictOrderedCommSemiring

variable [StrictOrderedCommSemiring β] [StarOrderedRing β] {f g : α → β}

--TODO: Those can probably be generalised to `ordered_comm_semiring` but we don't really care
@[simp]
theorem support_conv (hf : 0 ≤ f) (hg : 0 ≤ g) : support (f ∗ g) = support f + support g :=
  by
  refine' (support_conv_subset _ _).antisymm _
  rintro _ ⟨a, b, ha, hb, rfl⟩
  dsimp
  rw [conv_apply_add]
  exact
    ne_of_gt
      (sum_pos' (fun c _ => mul_nonneg (hf _) <| hg _)
        ⟨0, mem_univ _,
          mul_pos ((hf _).lt_of_ne' <| by simpa using ha) ((hg _).lt_of_ne' <| by simpa using hb)⟩)

@[simp]
theorem support_dconv (hf : 0 ≤ f) (hg : 0 ≤ g) : support (f ○ g) = support f - support g := by
  simpa [sub_eq_add_neg] using support_conv hf (conjneg_nonneg.2 hg)

theorem conv_pos (hf : 0 < f) (hg : 0 < g) : 0 < f ∗ g :=
  by
  rw [Pi.lt_def] at hf hg ⊢
  obtain ⟨hf, a, ha⟩ := hf
  obtain ⟨hg, b, hb⟩ := hg
  refine' ⟨conv_nonneg hf hg, a + b, _⟩
  rw [conv_apply_add]
  exact sum_pos' (fun c _ => mul_nonneg (hf _) <| hg _) ⟨0, by simpa using mul_pos ha hb⟩

theorem dconv_pos (hf : 0 < f) (hg : 0 < g) : 0 < f ○ g := by
  rw [← conv_conjneg] <;> exact conv_pos hf (conjneg_pos.2 hg)

end StrictOrderedCommSemiring

section OrderedCommSemiring

variable [OrderedCommSemiring β] [StarOrderedRing β] {f g : α → β} {n : ℕ}

@[simp]
theorem iterConv_nonneg (hf : 0 ≤ f) : ∀ {n}, 0 ≤ f ∗^ n
  | 0 => fun _ => by dsimp <;> split_ifs <;> norm_num
  | n + 1 => conv_nonneg hf iterConv_nonneg

end OrderedCommSemiring

section StrictOrderedCommSemiring

variable [StrictOrderedCommSemiring β] [StarOrderedRing β] {f g : α → β} {n : ℕ}

@[simp]
theorem iterConv_pos (hf : 0 < f) : ∀ {n}, 0 < f ∗^ n
  | 0 => Pi.lt_def.2 ⟨iterConv_nonneg hf.le, 0, by simp⟩
  | n + 1 => conv_pos hf iterConv_pos

end StrictOrderedCommSemiring

namespace Tactic

section

variable [OrderedCommSemiring β] [StarOrderedRing β] {f g : α → β}

private theorem conv_nonneg_of_pos_of_nonneg (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ f ∗ g :=
  conv_nonneg hf.le hg

private theorem conv_nonneg_of_nonneg_of_pos (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ f ∗ g :=
  conv_nonneg hf hg.le

private theorem dconv_nonneg_of_pos_of_nonneg (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ f ○ g :=
  dconv_nonneg hf.le hg

private theorem dconv_nonneg_of_nonneg_of_pos (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ f ○ g :=
  dconv_nonneg hf hg.le

end

open Positivity

-- PLEASE REPORT THIS TO MATHPORT DEVS, THIS SHOULD NOT HAPPEN.
-- failed to format: unknown constant 'term.pseudo.antiquot'
/--
      Extension for the `positivity` tactic: convolution/difference convolution/iterated convolution
      is nonnegative/positive if both multiplicands are. -/
    @[ positivity ]
    unsafe
  def
    positivity_conv
    : expr → tactic strictness
    |
        e @ q( $ ( f ) ∗ $ ( g ) )
        =>
        do
          let strictness_f ← core f
            let strictness_g ← core g
            match
              strictness_f , strictness_g
              with
              | positive pf , positive pg => positive <$> mk_app ` ` conv_pos [ pf , pg ]
                |
                  positive pf , nonnegative pg
                  =>
                  nonnegative
                    <$>
                    mk_mapp
                      ` ` conv_nonneg_of_pos_of_nonneg
                        [ none , none , none , none , none , none , none , f , g , pf , pg ]
                |
                  nonnegative pf , positive pg
                  =>
                  nonnegative
                    <$>
                    mk_mapp
                      ` ` conv_nonneg_of_nonneg_of_pos
                        [ none , none , none , none , none , none , none , f , g , pf , pg ]
                |
                  nonnegative pf , nonnegative pg
                  =>
                  nonnegative
                    <$>
                    mk_mapp
                      ` ` conv_nonneg
                        [ none , none , none , none , none , none , none , f , g , pf , pg ]
                | sf @ _ , sg @ _ => positivity_fail e f g sf sg
      |
        e @ q( $ ( f ) ○ $ ( g ) )
        =>
        do
          let strictness_f ← core f
            let strictness_g ← core g
            match
              strictness_f , strictness_g
              with
              | positive pf , positive pg => positive <$> mk_app ` ` dconv_pos [ pf , pg ]
                |
                  positive pf , nonnegative pg
                  =>
                  nonnegative
                    <$>
                    mk_mapp
                      ` ` dconv_nonneg_of_pos_of_nonneg
                        [ none , none , none , none , none , none , none , f , g , pf , pg ]
                |
                  nonnegative pf , positive pg
                  =>
                  nonnegative
                    <$>
                    mk_mapp
                      ` ` dconv_nonneg_of_nonneg_of_pos
                        [ none , none , none , none , none , none , none , f , g , pf , pg ]
                |
                  nonnegative pf , nonnegative pg
                  =>
                  nonnegative
                    <$>
                    mk_mapp
                      ` ` dconv_nonneg
                        [ none , none , none , none , none , none , none , f , g , pf , pg ]
                | sf @ _ , sg @ _ => positivity_fail e f g sf sg
      |
        e @ q( $ ( f ) ∗^ $ ( n ) )
        =>
        do
          let strictness_f ← core f
            match
              strictness_f
              with
              |
                  positive p
                  =>
                  positive
                    <$>
                    mk_mapp
                      ` ` iterConv_pos
                        [ none , none , none , none , none , none , none , none , p , n ]
                |
                  nonnegative p
                  =>
                  nonnegative
                    <$>
                    mk_mapp
                      ` ` iterConv_nonneg
                        [ none , none , none , none , none , none , none , none , p , n ]
                | _ => failed
      |
        e
        =>
        pp e
          >>=
          fail
            ∘
            format.bracket "The expression `" "` isn't of the form `f ∗ g`, `f ○ g` or `f ∗^ n`"

variable [StrictOrderedCommSemiring β] [StarOrderedRing β] {f g : α → β}

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

end Tactic

