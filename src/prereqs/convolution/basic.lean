import mathlib.algebra.big_operators.basic
import mathlib.data.finset.basic
import mathlib.data.fintype.basic
import mathlib.data.real.nnreal
import prereqs.indicator

/-!
# Convolution

This file defines several versions of the discrete convolution of functions.

## Main declarations

* `function.conv`: Discrete convolution of two functions
* `dconv`: Discrete difference convolution of two functions
* `iter_conv`: Iterated convolution of a function

## Notation

* `f ∗ g`: Convolution
* `f ○ g`: Difference convolution
* `f ∗^ n`: Iterated convolution

## Notes

Some lemmas could technically be generalised to a non-commutative semiring domain. Doesn't seem very
useful given that the codomain in applications is either `ℝ`, `ℝ≥0` or `ℂ`.

Similarly we could drop the commutativity assumption on the domain, but this is unneeded at this
point in time.

## TODO

Multiplicativise? Probably ugly and not very useful.
-/

open finset fintype function
open_locale big_operators complex_conjugate expectations nnreal pointwise

variables {α β γ : Type*} [fintype α] [decidable_eq α] [add_comm_group α]

/-!
### Convolution of functions

In this section, we define the convolution `f ∗ g` and difference convolution `f ○ g` of functions
`f g : α → β`, and show how they interact.
-/

section comm_semiring
variables [comm_semiring β] [star_ring β] {f g : α → β}

/-- Convolution -/
@[nolint unused_arguments]
def function.conv (f g : α → β) : α → β := λ a, ∑ x : α × α with x.1 + x.2 = a, f x.1 * g x.2

/-- Difference convolution -/
def dconv (f g : α → β) : α → β := λ a, ∑ x : α × α with x.1 - x.2 = a, f x.1 * conj (g x.2)

/-- The trivial character. -/
def triv_char : α → β := λ a, if a = 0 then 1 else 0

infix ` ∗ `:70 := function.conv
infix ` ○ `:70 := dconv

lemma conv_apply (f g : α → β) (a : α) :
  (f ∗ g) a = ∑ x : α × α with x.1 + x.2 = a, f x.1 * g x.2 := rfl

lemma dconv_apply (f g : α → β) (a : α) :
  (f ○ g) a = ∑ x : α × α with x.1 - x.2 = a, f x.1 * conj (g x.2) := rfl

@[simp] lemma triv_char_apply (a : α) : (triv_char a : β) =  if a = 0 then 1 else 0 := rfl

@[simp] lemma conv_conjneg (f g : α → β) : f ∗ conjneg g = f ○ g :=
funext $ λ a, sum_bij (λ x _, (x.1, -x.2)) (λ x hx, by simpa using hx) (λ x _, rfl)
  (λ x y _ _ h, by simpa [prod.ext_iff] using h)
  (λ x hx, ⟨(x.1, -x.2), by simpa [sub_eq_add_neg] using hx, by simp⟩)

@[simp] lemma dconv_conjneg (f g : α → β) : f ○ conjneg g = f ∗ g :=
by rw [←conv_conjneg, conjneg_conjneg]

lemma conv_comm (f g : α → β) : f ∗ g = g ∗ f :=
funext $ λ a, sum_nbij' prod.swap (λ x hx, by simpa [add_comm] using hx) (λ x _, mul_comm _ _)
  prod.swap (λ x hx, by simpa [add_comm] using hx) (λ x _, x.swap_swap) (λ x _, x.swap_swap)

@[simp] lemma conj_conv (f g : α → β) : conj (f ∗ g) = conj f ∗ conj g :=
funext $ λ a, by simp only [pi.conj_apply, conv_apply, map_sum, map_mul]

@[simp] lemma conjneg_conv (f g : α → β) : conjneg (f ∗ g) = conjneg f ∗ conjneg g :=
begin
  funext a,
  simp only [conv_apply, conjneg_apply, map_sum, map_mul],
  convert equiv.sum_comp_finset (equiv.neg (α × α)) _ rfl using 2,
  rw [←equiv.coe_to_embedding, ←map_eq_image (equiv.neg (α × α)).symm.to_embedding, map_filter],
  simp [function.comp, ←neg_eq_iff_eq_neg, add_comm],
end

@[simp] lemma conjneg_dconv (f g : α → β) : conjneg (f ○ g) = g ○ f :=
by simp_rw [←conv_conjneg, conjneg_conv, conjneg_conjneg, conv_comm]

lemma conv_assoc (f g h : α → β) : f ∗ g ∗ h = f ∗ (g ∗ h) :=
begin
  ext a,
  simp only [sum_mul, mul_sum, conv_apply, sum_sigma'],
  refine sum_bij' (λ x hx, ⟨(x.2.1, x.2.2 + x.1.2), (x.2.2, x.1.2)⟩) _ _
    (λ x hx, ⟨(x.1.1 + x.2.1, x.2.2), (x.1.1, x.2.1)⟩) _ _ _;
  simp only [mem_sigma, mem_filter, mem_univ, true_and, sigma.forall, prod.forall, and_imp,
    heq_iff_eq];
  rintro b c de rfl rfl;
  simp only [add_assoc, mul_assoc, prod.mk.eta, eq_self_iff_true, and_self],
end

lemma conv_right_comm (f g h : α → β) : f ∗ g ∗ h = f ∗ h ∗ g :=
by rw [conv_assoc, conv_assoc, conv_comm g]

lemma conv_left_comm (f g h : α → β) : f ∗ (g ∗ h) = g ∗ (f ∗ h) :=
by rw [←conv_assoc, ←conv_assoc, conv_comm g]

lemma conv_conv_conv_comm (f g h i : α → β) : (f ∗ g) ∗ (h ∗ i) = (f ∗ h) ∗ (g ∗ i) :=
by rw [conv_assoc, conv_assoc, conv_left_comm g]

lemma conv_dconv_conv_comm (f g h i : α → β) : (f ∗ g) ○ (h ∗ i) = (f ○ h) ∗ (g ○ i) :=
by simp_rw [←conv_conjneg, conjneg_conv, conv_conv_conv_comm]

lemma dconv_conv_dconv_comm (f g h i : α → β) : (f ○ g) ∗ (h ○ i) = (f ∗ h) ○ (g ∗ i) :=
by simp_rw [←conv_conjneg, conjneg_conv, conv_conv_conv_comm]

lemma dconv_dconv_dconv_comm (f g h i : α → β) : (f ○ g) ○ (h ○ i) = (f ○ h) ○ (g ○ i) :=
by simp_rw [←conv_conjneg, conjneg_conv, conv_conv_conv_comm]

@[simp] lemma conv_zero (f : α → β) : f ∗ 0 = 0 := by ext; simp [conv_apply]
@[simp] lemma zero_conv (f : α → β) : 0 ∗ f = 0 := by ext; simp [conv_apply]
@[simp] lemma dconv_zero (f : α → β) : f ○ 0 = 0 := by simp [←conv_conjneg]
@[simp] lemma zero_dconv (f : α → β) : 0 ○ f = 0 := by simp [←conv_conjneg]

lemma conv_add (f g h : α → β) : f ∗ (g + h) = f ∗ g + f ∗ h :=
by ext; simp only [conv_apply, mul_add, sum_add_distrib, pi.add_apply]

lemma add_conv (f g h : α → β) : (f + g) ∗ h = f ∗ h + g ∗ h :=
by ext; simp only [conv_apply, add_mul, sum_add_distrib, pi.add_apply]

lemma dconv_add (f g h : α → β) : f ○ (g + h) = f ○ g + f ○ h :=
by simp_rw [←conv_conjneg, conjneg_add, conv_add]

lemma add_dconv (f g h : α → β) : (f + g) ○ h = f ○ h + g ○ h :=
by simp_rw [←conv_conjneg, add_conv]

lemma smul_conv [distrib_smul γ β] [is_scalar_tower γ β β] (c : γ) (f g : α → β) :
  (c • f) ∗ g = c • (f ∗ g) :=
by ext a; simp only [pi.smul_apply, smul_sum, conv_apply, smul_mul_assoc]

lemma smul_dconv [distrib_smul γ β] [is_scalar_tower γ β β] (c : γ) (f g : α → β) :
  (c • f) ○ g = c • (f ○ g) :=
by ext a; simp only [pi.smul_apply, smul_sum, dconv_apply, smul_mul_assoc]

lemma conv_smul [distrib_smul γ β] [smul_comm_class γ β β] (c : γ) (f g : α → β) :
  f ∗ (c • g) = c • (f ∗ g) :=
by ext a; simp only [pi.smul_apply, smul_sum, conv_apply, mul_smul_comm]

lemma dconv_smul [has_star γ] [distrib_smul γ β] [smul_comm_class γ β β] [star_module γ β]
  (c : γ) (f g : α → β) : f ○ (c • g) = star c • (f ○ g) :=
by ext a; simp only [pi.smul_apply, smul_sum, dconv_apply, mul_smul_comm, star_ring_end_apply,
  star_module.star_smul]

alias smul_conv ← smul_conv_assoc
alias smul_dconv ← smul_dconv_assoc
alias conv_smul ← smul_conv_left_comm
alias dconv_smul ← smul_dconv_left_comm

lemma mul_smul_conv_comm [monoid γ] [distrib_mul_action γ β] [is_scalar_tower γ β β]
   [smul_comm_class γ β β] (c d : γ) (f g : α → β) : (c * d) • (f ∗ g) = c • f ∗ d • g :=
by rw [smul_conv, conv_smul, mul_smul]

lemma map_conv {γ} [comm_semiring γ] [star_ring γ] (m : β →+* γ) (f g : α → β) (a : α) :
  m ((f ∗ g) a) = ((m ∘ f) ∗ (m ∘ g)) a :=
by simp_rw [conv_apply, map_sum, map_mul]

lemma comp_conv {γ} [comm_semiring γ] [star_ring γ] (m : β →+* γ) (f g : α → β) :
  m ∘ (f ∗ g) = (m ∘ f) ∗ (m ∘ g) :=
funext $ map_conv _ _ _

--TODO: Can we generalise to star ring homs?
lemma map_dconv (f g : α → ℝ≥0) (a : α) : (↑((f ○ g) a) : ℝ) = ((coe ∘ f) ○ (coe ∘ g)) a :=
by simp_rw [dconv_apply, nnreal.coe_sum, nnreal.coe_mul, star_ring_end_apply, star_trivial]

lemma conv_eq_sum_sub (f g : α → β) (a : α) : (f ∗ g) a = ∑ t, f (a - t) * g t :=
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

lemma conv_eq_sum_add (f g : α → β) (a : α) : (f ∗ g) a = ∑ t, f (a + t) * g (-t) :=
(conv_eq_sum_sub _ _ _).trans $ fintype.sum_equiv (equiv.neg _) _ _ $ λ t,
  by simp only [sub_eq_add_neg, equiv.neg_apply, neg_neg]

lemma dconv_eq_sum_add (f g : α → β) (a : α) : (f ○ g) a = ∑ t, f (a + t) * conj (g t) :=
by simp [←conv_conjneg, conv_eq_sum_add]

lemma conv_eq_sum_sub' (f g : α → β) (a : α) : (f ∗ g) a = ∑ t, f t * g (a - t) :=
by rw [conv_comm, conv_eq_sum_sub]; simp_rw mul_comm

lemma dconv_eq_sum_sub (f g : α → β) (a : α) : (f ○ g) a = ∑ t, f t * conj (g (t - a)) :=
by simp [←conv_conjneg, conv_eq_sum_sub']

lemma conv_eq_sum_add' (f g : α → β) (a : α) : (f ∗ g) a = ∑ t, f (-t) * g (a + t) :=
by rw [conv_comm, conv_eq_sum_add]; simp_rw mul_comm

lemma conv_apply_add (f g : α → β) (a b : α) : (f ∗ g) (a + b) = ∑ t, f (a + t) * g (b - t) :=
(conv_eq_sum_sub _ _ _).trans $
  fintype.sum_equiv (equiv.sub_left b) _ _ $ λ t, by simp [add_sub_assoc, ←sub_add]

lemma dconv_apply_neg (f g : α → β) (a : α) : (f ○ g) (-a) = conj ((g ○ f) a) :=
by rw [←conjneg_dconv f, conjneg_apply, complex.conj_conj]

lemma dconv_apply_sub (f g : α → β) (a b : α) :
  (f ○ g) (a - b) = ∑ t, f (a + t) * conj (g (b + t)) :=
by simp [←conv_conjneg, sub_eq_add_neg, conv_apply_add, add_comm]

lemma sum_conv_mul (f g h : α → β) : ∑ a, (f ∗ g) a * h a = ∑ a b, f a * g b * h (a + b) :=
begin
  simp_rw [conv_eq_sum_sub', sum_mul],
  rw sum_comm,
  exact sum_congr rfl (λ x _, fintype.sum_equiv (equiv.sub_right x) _ _ $ λ y, by simp),
end

lemma sum_dconv_mul (f g h : α → β) : ∑ a, (f ○ g) a * h a = ∑ a b, f a * conj (g b) * h (a - b) :=
begin
  simp_rw [dconv_eq_sum_sub, sum_mul],
  rw sum_comm,
  exact sum_congr rfl (λ x _, fintype.sum_equiv (equiv.sub_left x) _ _ $ λ y, by simp),
end

lemma sum_conv (f g : α → β) : ∑ a, (f ∗ g) a = (∑ a, f a) * ∑ a, g a :=
by simpa only [sum_mul_sum, sum_product, pi.one_apply, mul_one] using sum_conv_mul f g 1

lemma sum_dconv (f g : α → β) : ∑ a, (f ○ g) a = (∑ a, f a) * ∑ a, conj (g a) :=
by simpa only [sum_mul_sum, sum_product, pi.one_apply, mul_one] using sum_dconv_mul f g 1

@[simp] lemma conv_const (f : α → β) (b : β) : f ∗ const _ b = const _ ((∑ x, f x) * b) :=
by ext; simp [conv_eq_sum_sub', sum_mul]

@[simp] lemma const_conv (b : β) (f : α → β) : const _ b ∗ f = const _ (b * ∑ x, f x) :=
by ext; simp [conv_eq_sum_sub, mul_sum]

@[simp] lemma dconv_const (f : α → β) (b : β) : f ○ const _ b = const _ ((∑ x, f x) * conj b) :=
by ext; simp [dconv_eq_sum_sub, sum_mul]

@[simp] lemma const_dconv (b : β) (f : α → β) : const _ b ○ f = const _ (b * ∑ x, conj (f x)) :=
by ext; simp [dconv_eq_sum_add, mul_sum]

@[simp] lemma conv_triv_char (f : α → β) : f ∗ triv_char = f := by { ext a, simp [conv_eq_sum_sub] }
@[simp] lemma triv_char_conv (f : α → β) : triv_char ∗ f = f := by rw [conv_comm, conv_triv_char]

@[simp] lemma dconv_triv_char (f : α → β) : f ○ triv_char = f :=
by { ext a, simp [dconv_eq_sum_add] }

@[simp] lemma triv_char_dconv (f : α → β) : triv_char ○ f = conjneg f :=
by rw [←conv_conjneg, triv_char_conv]

lemma support_conv_subset (f g : α → β) : support (f ∗ g) ⊆ support f + support g :=
begin
  rintro a ha,
  obtain ⟨x, hx, h⟩ := exists_ne_zero_of_sum_ne_zero ha,
  exact ⟨x.1, x.2, left_ne_zero_of_mul h, right_ne_zero_of_mul h, (mem_filter.1 hx).2⟩,
end

lemma support_dconv_subset (f g : α → β) : support (f ○ g) ⊆ support f - support g :=
by simpa [sub_eq_add_neg] using support_conv_subset f (conjneg g)

lemma indicate_conv_indicate_apply (s t : finset α) (a : α) :
  (𝟭_[β] s ∗ 𝟭 t) a = ((s ×ˢ t).filter $ λ x : α × α, x.1 + x.2 = a).card :=
begin
  simp only [conv_apply, indicate_apply, ←ite_and, filter_comm, boole_mul, sum_boole],
  simp_rw [←mem_product, filter_mem_univ],
end

lemma indicate_dconv_indicate_apply (s t : finset α) (a : α) :
  (𝟭_[β] s ○ 𝟭 t) a = ((s ×ˢ t).filter $ λ x : α × α, x.1 - x.2 = a).card :=
begin
  simp only [dconv_apply, indicate_apply, ←ite_and, filter_comm, boole_mul, sum_boole,
    apply_ite conj, map_one, map_zero],
  simp_rw [←mem_product, filter_mem_univ],
end

end comm_semiring

section comm_ring
variables [comm_ring β] [star_ring β]

@[simp] lemma conv_neg (f g : α → β) : f ∗ (-g) = -(f ∗ g) := by ext; simp [conv_apply]
@[simp] lemma neg_conv (f g : α → β) : (-f) ∗ g = -(f ∗ g) := by ext; simp [conv_apply]
@[simp] lemma dconv_neg (f g : α → β) : f ○ (-g) = -(f ○ g) := by ext; simp [dconv_apply]
@[simp] lemma neg_dconv (f g : α → β) : (-f) ○ g = -(f ○ g) := by ext; simp [dconv_apply]

lemma conv_sub (f g h : α → β) : f ∗ (g - h) = f ∗ g - f ∗ h :=
by simp only [sub_eq_add_neg, conv_add, conv_neg]

lemma sub_conv (f g h : α → β) : (f - g) ∗ h = f ∗ h - g ∗ h :=
by simp only [sub_eq_add_neg, add_conv, neg_conv]

lemma dconv_sub (f g h : α → β) : f ○ (g - h) = f ○ g - f ○ h :=
by simp only [sub_eq_add_neg, dconv_add, dconv_neg]

lemma sub_dconv (f g h : α → β) : (f - g) ○ h = f ○ h - g ○ h :=
by simp only [sub_eq_add_neg, add_dconv, neg_dconv]

end comm_ring

section semifield
variables [semifield β] [star_ring β]

@[simp] lemma mu_univ_conv_mu_univ : μ_[β] (univ : finset α) ∗ μ univ = μ univ :=
by ext; cases eq_or_ne (card α : β) 0; simp [mu_apply, conv_eq_sum_add, card_univ, *]

@[simp] lemma mu_univ_dconv_mu_univ : μ_[β] (univ : finset α) ○ μ univ = μ univ :=
by ext; cases eq_or_ne (card α : β) 0; simp [mu_apply, dconv_eq_sum_add, card_univ, *]

lemma expect_conv (f g : α → β) : 𝔼 a, (f ∗ g) a = (∑ a, f a) * 𝔼 a, g a :=
by simp_rw [expect, sum_conv, mul_div_assoc]

lemma expect_dconv (f g : α → β) : 𝔼 a, (f ○ g) a = (∑ a, f a) * 𝔼 a, conj (g a) :=
by simp_rw [expect, sum_dconv, mul_div_assoc]

lemma expect_conv' (f g : α → β) : 𝔼 a, (f ∗ g) a = (𝔼 a, f a) * ∑ a, g a :=
by simp_rw [expect, sum_conv, mul_div_right_comm]

lemma expect_dconv' (f g : α → β) : 𝔼 a, (f ○ g) a = (𝔼 a, f a) * ∑ a, conj (g a) :=
by simp_rw [expect, sum_dconv, mul_div_right_comm]

end semifield

section field
variables [field β] [star_ring β] [char_zero β]

@[simp] lemma balance_conv (f g : α → β) : balance (f ∗ g) = balance f ∗ balance g :=
by simp [balance, conv_sub, sub_conv, expect_conv]

@[simp] lemma balance_dconv (f g : α → β) : balance (f ○ g) = balance f ○ balance g :=
by simp [balance, dconv_sub, sub_dconv, expect_dconv, map_expect]

end field

namespace is_R_or_C
variables {𝕜 : Type} [is_R_or_C 𝕜] (f g : α → ℝ) (a : α)

@[simp, norm_cast] lemma coe_conv : (↑((f ∗ g) a) : 𝕜) = (coe ∘ f ∗ coe ∘ g) a :=
map_conv (algebra_map ℝ 𝕜) _ _ _

@[simp, norm_cast] lemma coe_dconv : (↑((f ○ g) a) : 𝕜) = (coe ∘ f ○ coe ∘ g) a :=
by simp [dconv_apply, coe_sum]

@[simp] lemma coe_comp_conv : (coe : ℝ → 𝕜) ∘ (f ∗ g) = coe ∘ f ∗ coe ∘ g := funext $ coe_conv _ _
@[simp] lemma coe_comp_dconv : (coe : ℝ → 𝕜) ∘ (f ○ g) = coe ∘ f ○ coe ∘ g := funext $ coe_dconv _ _

end is_R_or_C

namespace nnreal
variables (f g : α → ℝ≥0) (a : α)

@[simp, norm_cast] lemma coe_conv : (↑((f ∗ g) a) : ℝ) = (coe ∘ f ∗ coe ∘ g) a :=
map_conv nnreal.to_real_hom _ _ _

@[simp, norm_cast] lemma coe_dconv : (↑((f ○ g) a) : ℝ) = (coe ∘ f ○ coe ∘ g) a :=
by simp [dconv_apply, coe_sum]

@[simp] lemma coe_comp_conv : (coe : _ → ℝ) ∘ (f ∗ g) = coe ∘ f ∗ coe ∘ g := funext $ coe_conv _ _
@[simp] lemma coe_comp_dconv : (coe : _ → ℝ) ∘ (f ○ g) = coe ∘ f ○ coe ∘ g := funext $ coe_dconv _ _

end nnreal

/-! ### Iterated convolution -/

section comm_semiring
variables [comm_semiring β] [star_ring β] {f g : α → β} {n : ℕ}

/-- Iterated convolution. -/
def iter_conv (f : α → β) : ℕ → α → β
| 0 := triv_char
| (n + 1) := f ∗ iter_conv n

infix  ` ∗^ `:78 := iter_conv

@[simp] lemma iter_conv_zero (f : α → β) : f ∗^ 0 = triv_char := rfl
@[simp] lemma iter_conv_one (f : α → β) : f ∗^ 1 = f := conv_triv_char _

lemma iter_conv_succ (f : α → β) (n : ℕ) : f ∗^ (n + 1) = f ∗ f ∗^ n := rfl
lemma iter_conv_succ' (f : α → β) (n : ℕ) : f ∗^ (n + 1) = f ∗^ n ∗ f := conv_comm _ _

lemma iter_conv_add (f : α → β) (m : ℕ) : ∀ n, f ∗^ (m + n) = f ∗^ m ∗ f ∗^ n
| 0 := by simp
| (n + 1) := by simp [←add_assoc, iter_conv_succ, iter_conv_add, conv_left_comm]

lemma iter_conv_mul (f : α → β) (m : ℕ) : ∀ n, f ∗^ (m * n) = (f ∗^ m) ∗^ n
| 0 := rfl
| (n + 1) := by simp [mul_add_one, iter_conv_succ, iter_conv_add, iter_conv_mul]

lemma iter_conv_mul' (f : α → β) (m n : ℕ) : f ∗^ (m * n) = (f ∗^ n) ∗^ m :=
by rw [mul_comm, iter_conv_mul]

@[simp] lemma conj_iter_conv (f : α → β) : ∀ n, conj (f ∗^ n) = conj f ∗^ n
| 0 := by ext; simp
| (n + 1) := by simp [iter_conv_succ, conj_iter_conv]

@[simp] lemma conjneg_iter_conv (f : α → β) : ∀ n, conjneg (f ∗^ n) = conjneg f ∗^ n
| 0 := by ext; simp
| (n + 1) := by simp [iter_conv_succ, conjneg_iter_conv]

lemma iter_conv_conv_distrib (f g : α → β) : ∀ n, (f ∗ g) ∗^ n = f ∗^ n ∗ g ∗^ n
| 0 := (conv_triv_char _).symm
| (n + 1) := by simp_rw [iter_conv_succ, iter_conv_conv_distrib, conv_conv_conv_comm]

lemma iter_conv_dconv_distrib (f g : α → β) : ∀ n, (f ○ g) ∗^ n = f ∗^ n ○ g ∗^ n
| 0 := (dconv_triv_char _).symm
| (n + 1) := by simp_rw [iter_conv_succ, iter_conv_dconv_distrib, conv_dconv_conv_comm]

@[simp] lemma zero_iter_conv : ∀ {n}, n ≠ 0 → (0 : α → β) ∗^ n = 0
| 0 hn := by cases hn rfl
| (n + 1) _ := zero_conv _

@[simp] lemma smul_iter_conv [monoid γ] [distrib_mul_action γ β] [is_scalar_tower γ β β]
  [smul_comm_class γ β β] (c : γ) (f : α → β) : ∀ n, (c • f) ∗^ n = c ^ n • f ∗^ n
| 0 := by simp
| (n + 1) := by simp_rw [iter_conv_succ, smul_iter_conv n, pow_succ, mul_smul_conv_comm]

lemma comp_iter_conv {γ} [comm_semiring γ] [star_ring γ] (m : β →+* γ) (f : α → β) :
  ∀ n, m ∘ (f ∗^ n) = (m ∘ f) ∗^ n
| 0 := by ext; simp
| (n + 1) := by simp [iter_conv_succ, comp_conv, comp_iter_conv]

lemma map_iter_conv {γ} [comm_semiring γ] [star_ring γ] (m : β →+* γ) (f : α → β) (a : α) (n : ℕ) :
  m ((f ∗^ n) a) = ((m ∘ f) ∗^ n) a :=
congr_fun (comp_iter_conv m _ _) _

lemma sum_iter_conv (f : α → β) : ∀ n, ∑ a, (f ∗^ n) a = (∑ a, f a) ^ n
| 0 := by simp [filter_eq']
| (n + 1) := by simp only [iter_conv_succ, sum_conv, sum_iter_conv, pow_succ]

@[simp] lemma iter_conv_triv_char :
  ∀ n, (triv_char : α → β) ∗^ n = triv_char
| 0 := rfl
| (n + 1) := (triv_char_conv _).trans $ iter_conv_triv_char _

lemma support_iter_conv_subset (f : α → β) : ∀ n, support (f ∗^ n) ⊆ n • support f
| 0 := by simp only [iter_conv_zero, zero_smul, support_subset_iff, ne.def, ite_eq_right_iff,
  not_forall, exists_prop, set.mem_zero, and_imp, forall_eq, eq_self_iff_true, implies_true_iff,
  triv_char_apply]
| (n + 1) := (support_conv_subset _ _).trans $ set.add_subset_add_left $ support_iter_conv_subset _

lemma indicate_iter_conv_apply (s : finset α) (n : ℕ) (a : α) :
  (𝟭_[ℝ] s ∗^ n) a = ((pi_finset $ λ i, s).filter $ λ x : fin n → α, ∑ i, x i = a).card :=
begin
  induction n with n ih generalizing a,
  { simp [apply_ite card, eq_comm] },
  simp_rw [iter_conv_succ, conv_eq_sum_sub', ih, indicate_apply, boole_mul, sum_ite,
    filter_mem_univ, sum_const_zero, add_zero, ←nat.cast_sum, ←finset.card_sigma, nat.cast_inj],
  refine finset.card_congr (λ f _, fin.cons f.1 f.2) _ _ _,
  { simp only [fin.sum_cons, eq_sub_iff_add_eq', mem_sigma, mem_filter, mem_pi_finset, and_imp],
    refine λ bf hb hf ha, ⟨fin.cases _ _, ha⟩,
    { exact hb },
    { simpa only [fin.cons_succ] } },
  { simp only [sigma.ext_iff, fin.cons_eq_cons, heq_iff_eq, imp_self, implies_true_iff,
      forall_const, sigma.forall] },
  { simp only [mem_filter, mem_pi_finset, mem_sigma, exists_prop, sigma.exists, and_imp,
      eq_sub_iff_add_eq', and_assoc],
    exact λ f hf ha, ⟨f 0, fin.tail f, hf _, λ _, hf _, (fin.sum_univ_succ _).symm.trans ha,
      fin.cons_self_tail _⟩ }
end

end comm_semiring

section field
variables [field β] [star_ring β] [char_zero β]

@[simp] lemma balance_iter_conv (f : α → β) : ∀ {n}, n ≠ 0 → balance (f ∗^ n) = balance f ∗^ n
| 0 h := by cases h rfl
| 1 h := by simp
| (n + 2) h := by simp [iter_conv_succ _ (n + 1), balance_iter_conv n.succ_ne_zero]

end field

namespace nnreal
variables {f : α → ℝ≥0}

@[simp, norm_cast] lemma coe_iter_conv (f : α → ℝ≥0) (n : ℕ) (a : α) :
  (↑((f ∗^ n) a) : ℝ) = (coe ∘ f ∗^ n) a :=
map_iter_conv nnreal.to_real_hom _ _ _

end nnreal
