import algebra.star.pi
import prereqs.misc

/-!
# Convolution

## TODO

Multiplicativise? Probably ugly and not very useful.
Include convolution on `α → ℝ`. Generalise to star rings?
-/

open finset real
open_locale big_operators complex_conjugate nnreal

/-!
### The ring of functions under convolution

In this section, for a finite group `α`, we define a type synonym `with_conv α` of the functions
`α → ℂ`. We endow that type synonym with the ring structure given by pointwise addition and
convolution as multiplication.
-/

instance function.star_ring {ι α : Type*} [non_unital_semiring α] [star_ring α] :
  star_ring (ι → α) :=
pi.star_ring

@[simp] lemma pi.conj_apply {ι : Type*} {α : ι → Type*} [Π i, comm_semiring (α i)]
  [Π i, star_ring (α i)] (f : Π i, α i) (i : ι) :
  @star_ring_end (Π i, α i) _ (@pi.star_ring ι α _ _) f i = conj (f i) :=
rfl

noncomputable instance function.star_ring' {ι : Type*} : star_ring (ι → ℂ) :=
pi.star_ring

@[derive add_comm_group] def with_conv (α : Type*) : Type* := α → ℂ

variables {ι α : Type*}

/-- `to_conv` is the identity function to the `order_conv` of a linear order.  -/
def to_conv : (α → ℂ) ≃ with_conv α := equiv.refl _

/-- `of_conv` is the identity function from the `order_conv` of a linear order.  -/
def of_conv : with_conv α ≃ (α → ℂ) := equiv.refl _

@[simp] lemma to_conv_symm_eq : (@to_conv α).symm = of_conv := rfl
@[simp] lemma of_conv_symm_eq : (@of_conv α).symm = to_conv := rfl
@[simp] lemma to_conv_of_conv (f : with_conv α) : to_conv (of_conv f) = f := rfl
@[simp] lemma of_conv_to_conv (f : α → ℂ) : of_conv (to_conv f) = f := rfl
@[simp] lemma to_conv_inj {f g : α → ℂ} : to_conv f = to_conv g ↔ f = g := iff.rfl
@[simp] lemma of_conv_inj {f g : with_conv α} : of_conv f = of_conv g ↔ f = g := iff.rfl

@[simp] lemma to_conv_apply (f : α → ℂ) (a : α) : to_conv f a = f a := rfl
@[simp] lemma of_conv_apply (f : with_conv α) (a : α) : of_conv f a = f a := rfl

variables {α}

section add_group
variables [add_group α] [fintype α] [decidable_eq α]

instance : ring (with_conv α) :=
{ one := to_conv $ pi.single 0 1,
  mul := λ f g, to_conv $ λ a, ∑ x in univ.filter (λ x : α × α, x.1 + x.2 = a), f x.1 * g x.2,
  mul_assoc := sorry,
  one_mul := sorry,
  mul_one := sorry,
  left_distrib := sorry,
  right_distrib := sorry,
  ..with_conv.add_comm_group _ }

@[simp] lemma to_conv_zero : to_conv (0 : α → ℂ) = 0 := rfl
@[simp] lemma to_conv_neg (f : α → ℂ) : to_conv (-f) = -to_conv f := rfl
@[simp] lemma to_conv_add (f g : α → ℂ) : to_conv (f + g) = to_conv f + to_conv g := rfl
@[simp] lemma to_conv_sub (f g : α → ℂ) : to_conv (f - g) = to_conv f - to_conv g := rfl

@[simp] lemma of_conv_zero : (of_conv 0 : α → ℂ) = 0 := rfl
@[simp] lemma of_conv_neg (f : with_conv α) : of_conv (-f) = -of_conv f := rfl
@[simp] lemma of_conv_add (f g : with_conv α) : of_conv (f + g) = of_conv f + of_conv g := rfl
@[simp] lemma of_conv_sub (f g : with_conv α) : of_conv (f - g) = of_conv f - of_conv g := rfl

end add_group

section add_comm_group
variables [add_comm_group α] [fintype α] [decidable_eq α]

instance : comm_ring (with_conv α) :=
{ mul_comm := λ f g, funext $ λ a, sum_bij (λ x _, x.swap) (λ x hx, by simpa [add_comm] using hx)
    (λ _ _, mul_comm _ _) (λ _ _ _ _, prod.swap_inj.1)
    (λ x hx, ⟨x.swap, by simpa [add_comm] using hx, x.swap_swap.symm⟩),
  ..with_conv.ring }

end add_comm_group

/-!
### Convolution of functions

In this section, we define the convolution `f ∗ g` of functions `α → ℂ` and translate ring
properties of `with_conv α` to properties of `∗`.
-/

section add_group
variables [add_group α] [fintype α] [decidable_eq α]

/-- Convolution -/
def function.conv (f g : α → ℂ) : α → ℂ := of_conv (to_conv f * to_conv g)

notation f ` ∗ `:70 g:70 := function.conv f g

@[simp] lemma of_conv_mul (f g : with_conv α) : of_conv (f * g) = of_conv f ∗ of_conv g := rfl

lemma conv_apply (f g : α → ℂ) (a : α) :
  (f ∗ g) a = ∑ x in univ.filter (λ x : α × α, x.1 + x.2 = a), f x.1 * g x.2 := rfl

lemma conv_eq_sum_sub (f g : α → ℂ) (a : α) : (f ∗ g) a = ∑ t, f (a - t) * g t :=
begin
  rw conv_apply,
  refine sum_bij (λ x _, x.2) (λ x _, mem_univ _) _ _
    (λ b _, ⟨(a - b, b), mem_filter.2 ⟨mem_univ _, sub_add_cancel _ _⟩, rfl⟩);
    simp only [mem_filter, mem_univ, true_and, prod.forall],
  { rintro b c rfl,
    rw add_sub_cancel },
  { rintro b c x h rfl rfl,
    simpa [prod.ext_iff] using h }
end

lemma conv_eq_sum_add (f g : α → ℂ) (a : α) : (f ∗ g) a = ∑ t, f (a + t) * g (-t) :=
(conv_eq_sum_sub _ _ _).trans $ fintype.sum_equiv (equiv.neg _) _ _ $ λ t,
  by simp only [sub_eq_add_neg, equiv.neg_apply, neg_neg]

lemma conv_assoc (f g h : α → ℂ) : f ∗ g ∗ h = f ∗ (g ∗ h) := mul_assoc (to_conv f) _ _

@[simp] lemma conv_zero (f : α → ℂ) : f ∗ 0 = 0 := mul_zero (to_conv f)
@[simp] lemma zero_conv (f : α → ℂ) : 0 ∗ f = 0 := zero_mul (to_conv f)

@[simp] lemma conv_neg (f g : α → ℂ) : f ∗ (-g) = -(f ∗ g) := congr_arg of_conv (mul_neg _ _)
@[simp] lemma neg_conv (f g : α → ℂ) : (-f) ∗ g = -(f ∗ g) := congr_arg of_conv (neg_mul _ _)

lemma conv_add (f g h : α → ℂ) : f ∗ (g + h) = f ∗ g + f ∗ h := congr_arg of_conv (mul_add _ _ _)
lemma add_conv (f g h : α → ℂ) : (f + g) ∗ h = f ∗ h + g ∗ h := congr_arg of_conv (add_mul _ _ _)

lemma conv_sub (f g h : α → ℂ) : f ∗ (g - h) = f ∗ g - f ∗ h := congr_arg of_conv (mul_sub _ _ _)
lemma sub_conv (f g h : α → ℂ) : (f - g) ∗ h = f ∗ h - g ∗ h := congr_arg of_conv (sub_mul _ _ _)

end add_group

section add_comm_group
variables [add_comm_group α] [fintype α] [decidable_eq α]

lemma conv_apply_add (f g : α → ℂ) (a b : α) : (f ∗ g) (a + b) = ∑ t, f (a + t) * g (b - t) :=
begin
  rw conv_eq_sum_sub,
  exact fintype.sum_equiv (equiv.sub_left b) _ _ (λ t, by simp [add_sub_assoc, ←sub_add]),
end

lemma conv_comm (f g : α → ℂ) : f ∗ g = g ∗ f := mul_comm (to_conv f) _

@[simp] lemma conj_conv (f g : α → ℂ) : conj (f ∗ g) = conj f ∗ conj g :=
funext $ λ a, by simp only [pi.conj_apply, conv_apply, map_sum, map_mul]

@[simp] lemma conjneg_conv (f g : α → ℂ) : conjneg (f ∗ g) = conjneg f ∗ conjneg g :=
begin
  funext a,
  simp only [conv_apply, conjneg_apply, map_sum, map_mul],
  convert equiv.sum_comp_finset (equiv.neg (α × α)) _ rfl using 2,
  rw [←equiv.coe_to_embedding, ←map_eq_image (equiv.neg (α × α)).symm.to_embedding, map_filter],
  simp [function.comp, ←neg_eq_iff_eq_neg, add_comm],
end

lemma conv_eq_sum_sub' (f g : α → ℂ) (a : α) : (f ∗ g) a = ∑ t, f t * g (a - t) :=
by { rw conv_eq_sum_sub, exact fintype.sum_equiv (equiv.sub_left a) _ _ (λ t, by simp) }

lemma conv_eq_inner (f g : α → ℂ) (a : α) : (f ∗ g) a = ⟪conj f, τ a (λ x, g (-x))⟫_[ℂ] :=
by simp [L2inner_eq_sum, conv_eq_sum_sub', map_sum]

-- TODO: This proof would feel much less painful if we had `ℝ≥0`-valued Lp-norms.
/-- A special case of **Young's convolution inequality**. -/
lemma Lpnorm_conv_le {p : ℝ≥0} (hp : 1 < p) (f g : α → ℂ) : ‖f ∗ g‖_[p] ≤ ‖f‖_[p] * ‖g‖_[1] :=
begin
  have hp₀ := zero_lt_one.trans hp,
  rw [←rpow_le_rpow_iff _ (mul_nonneg _ _) hp₀, mul_rpow],
  any_goals { exact Lpnorm_nonneg },
  simp_rw [Lpnorm_rpow_eq_sum hp₀, conv_eq_sum_sub'],
  have hpconj : is_conjugate_exponent p (1 - p⁻¹)⁻¹ :=
    ⟨hp, by simp_rw [one_div, inv_inv, add_sub_cancel'_right]⟩,
  have : ∀ x, ‖∑ y, f y * g (x - y)‖ ^ (p : ℝ) ≤
    (∑ y, ‖f y‖ ^ (p : ℝ) * ‖g (x - y)‖) * (∑ y, ‖g (x - y)‖) ^ (p - 1 : ℝ),
  { intro x,
    rw [←le_rpow_inv_iff_of_pos (norm_nonneg _), mul_rpow, ←rpow_mul, sub_one_mul, mul_inv_cancel],
    rotate 1,
    { positivity },
    { exact sum_nonneg (λ _ _, norm_nonneg _) },
    { exact sum_nonneg (λ _ _, by positivity) },
    { exact rpow_nonneg_of_nonneg (sum_nonneg $ λ _ _, norm_nonneg _)  _ },
    { exact mul_nonneg (sum_nonneg $ λ _ _, by positivity)
        (rpow_nonneg_of_nonneg (sum_nonneg $ λ _ _, norm_nonneg _) _) },
    { positivity },
    calc
      _ ≤ ∑ y, ‖f y * g (x - y)‖ : norm_sum_le _ _
    ... = ∑ y, ‖f y‖ * ‖g (x - y)‖ ^ (p⁻¹ : ℝ) * ‖g (x - y)‖ ^ (1 - p⁻¹ : ℝ) : _
    ... ≤ _ : inner_le_Lp_mul_Lq _ _ _ hpconj
    ... = _ : _,
    { congr' with t,
      rw [norm_mul, mul_assoc, ←rpow_add' (norm_nonneg _), add_sub_cancel'_right, rpow_one],
      simp },
    { have : (1 - p⁻¹ : ℝ) ≠ 0 := sub_ne_zero.2 (inv_ne_one.2 $ by exact_mod_cast hp.ne').symm,
      simp only [abs_mul, abs_rpow_of_nonneg, mul_rpow, rpow_nonneg_of_nonneg, hp₀.ne', this,
        abs_norm, norm_nonneg, rpow_inv_rpow, ne.def, nnreal.coe_eq_zero, not_false_iff, one_div,
        rpow_rpow_inv, div_inv_eq_mul, one_mul] } },
  calc
    ∑ x, ‖∑ y, f y * g (x - y)‖ ^ (p : ℝ)
      ≤ ∑ x, (∑ y, ‖f y‖ ^ (p : ℝ) * ‖g (x - y)‖) * (∑ y, ‖g (x - y)‖) ^ (p - 1 : ℝ)
      : sum_le_sum $ λ i _, this _
  ... = _ : _,
  have hg : ∀ x, ∑ y, ‖g (x - y)‖ = ‖g‖_[1],
  { simp_rw L1norm_eq_sum,
    exact λ x, fintype.sum_equiv (equiv.sub_left _) _ _ (λ _, rfl) },
  have hg' : ∀ y, ∑ x, ‖g (x - y)‖ = ‖g‖_[1],
  { simp_rw L1norm_eq_sum,
    exact λ x, fintype.sum_equiv (equiv.sub_right _) _ _ (λ _, rfl) },
  simp_rw hg,
  rw [←sum_mul, sum_comm],
  simp_rw [←mul_sum, hg'],
  rw [←sum_mul, mul_assoc, ←rpow_one_add' Lpnorm_nonneg, add_sub_cancel'_right],
  { rw add_sub_cancel'_right,
    positivity }
end

end add_comm_group

/-!
### Difference convolution of functions

In this section, we define the difference convolution `f ○ g` of functions `α → ℂ` and show how it
interacts with the usual convolution.
-/

section add_group
variables [add_group α] [fintype α] [decidable_eq α]

/-- Difference convolution -/
def dconv (f g : α → ℂ) : α → ℂ :=
λ a, ∑ x in univ.filter (λ x : α × α, x.1 - x.2 = a), f x.1 * conj (g x.2)

end add_group

infix ` ○ `:70 := dconv

section add_comm_group
variables [add_comm_group α] [fintype α] [decidable_eq α]

lemma dconv_apply (f g : α → ℂ) (a : α) :
  (f ○ g) a = ∑ x in univ.filter (λ x : α × α, x.1 - x.2 = a), f x.1 * conj (g x.2) := rfl

@[simp] lemma conv_conjneg (f g : α → ℂ) : f ∗ conjneg g = f ○ g :=
funext $ λ a, sum_bij (λ x _, (x.1, -x.2)) (λ x hx, by simpa using hx) (λ x _, rfl)
  (λ x y _ _ h, by simpa [prod.ext_iff] using h)
  (λ x hx, ⟨(x.1, -x.2), by simpa [sub_eq_add_neg] using hx, by simp⟩)

@[simp] lemma dconv_conjneg (f g : α → ℂ) : f ○ conjneg g = f ∗ g :=
by rw [←conv_conjneg, conjneg_conjneg]

lemma dconv_eq_sum_add (f g : α → ℂ) (a : α) : (f ○ g) a = ∑ t, f (a + t) * conj (g t) :=
by simp [←conv_conjneg, conv_eq_sum_add]

lemma dconv_eq_sum_sub (f g : α → ℂ) (a : α) : (f ○ g) a = ∑ t, f t * conj (g (t - a)) :=
by simp [←conv_conjneg, conv_eq_sum_sub']

@[simp] lemma dconv_zero (f : α → ℂ) : f ○ 0 = 0 := by simp [←conv_conjneg]
@[simp] lemma zero_dconv (f : α → ℂ) : 0 ○ f = 0 := by simp [←conv_conjneg]

@[simp] lemma dconv_neg (f g : α → ℂ) : f ○ (-g) = -(f ○ g) := by ext : 1; simp [dconv]
@[simp] lemma neg_dconv (f g : α → ℂ) : (-f) ○ g = -(f ○ g) := by ext : 1; simp [dconv]

lemma dconv_add (f g h : α → ℂ) : f ○ (g + h) = f ○ g + f ○ h :=
by simp_rw [←conv_conjneg, conjneg_add, conv_add]

lemma add_dconv (f g h : α → ℂ) : (f + g) ○ h = f ○ h + g ○ h :=
by simp_rw [←conv_conjneg, add_conv]

lemma dconv_sub (f g h : α → ℂ) : f ○ (g - h) = f ○ g - f ○ h :=
by simp_rw [←conv_conjneg, conjneg_sub, conv_sub]

lemma sub_dconv (f g h : α → ℂ) : (f - g) ○ h = f ○ h - g ○ h :=
by simp_rw [←conv_conjneg, sub_conv]

@[simp] lemma conjneg_dconv (f g : α → ℂ) : conjneg (f ○ g) = g ○ f :=
by simp_rw [←conv_conjneg, conjneg_conv, conjneg_conjneg, conv_comm]

lemma dconv_apply_neg (f g : α → ℂ) (a : α) : (f ○ g) (-a) = conj ((g ○ f) a) :=
by rw [←conjneg_dconv f, conjneg_apply, complex.conj_conj]

lemma dconv_apply_sub (f g : α → ℂ) (a b : α) :
  (f ○ g) (a - b) = ∑ t, f (a + t) * conj (g (b + t)) :=
by simp [←conv_conjneg, sub_eq_add_neg, conv_apply_add, add_comm]

lemma dconv_eq_inner (f g : α → ℂ) (a : α) : (f ○ g) a = conj ⟪f, τ a g⟫_[ℂ] :=
by simp [L2inner_eq_sum, dconv_eq_sum_sub, map_sum]

end add_comm_group
