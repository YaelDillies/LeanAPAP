import algebra.star.pi
import algebra.star.pointwise
import mathlib.algebra.big_operators.basic
import mathlib.algebra.star.order
import prereqs.lp_norm

/-!
# Convolution

## Notes

Some lemmas could technically be generalised to a non-commutative semiring domain. Doesn't seem very
useful given that the codomain in applications is either `ℝ`, `ℝ≥0` or `ℂ`.

Similarly we could drop the commutativity assumption on the domain, but this is unneeded at this
point in time.

## TODO

Multiplicativise? Probably ugly and not very useful.

-/

open finset function real
open_locale big_operators complex_conjugate nnreal pointwise

variables {ι α β γ : Type*} [fintype α] [decidable_eq α] [add_comm_group α]

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

namespace nnreal
variables {f g : α → ℝ≥0}

@[simp, norm_cast] lemma coe_conv (x : α) : (↑((f ∗ g) x) : ℝ) = (coe ∘ f ∗ coe ∘ g) x :=
by simp [conv_apply, coe_sum]

@[simp, norm_cast] lemma coe_dconv (x : α) : (↑((f ○ g) x) : ℝ) = (coe ∘ f ○ coe ∘ g) x :=
by simp [dconv_apply, coe_sum]

end nnreal

/-!
### Order properties

In this section, we prove order results about the convolution and difference convolution, in
particular Young's convolution inequality.
-/

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

end comm_semiring

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

section is_R_or_C
variables [is_R_or_C β]

lemma conv_eq_inner (f g : α → β) (a : α) : (f ∗ g) a = ⟪conj f, τ a (λ x, g (-x))⟫_[β] :=
by simp [L2inner_eq_sum, conv_eq_sum_sub', map_sum]

lemma dconv_eq_inner (f g : α → β) (a : α) : (f ○ g) a = conj ⟪f, τ a g⟫_[β] :=
by simp [L2inner_eq_sum, dconv_eq_sum_sub, map_sum]

-- TODO: This proof would feel much less painful if we had `ℝ≥0`-valued Lp-norms.
/-- A special case of **Young's convolution inequality**. -/
lemma Lpnorm_conv_le {p : ℝ≥0} (hp : 1 ≤ p) (f g : α → β) : ‖f ∗ g‖_[p] ≤ ‖f‖_[p] * ‖g‖_[1] :=
begin
  obtain rfl | hp := hp.eq_or_lt,
  { simp_rw [ennreal.coe_one, L1norm_eq_sum, sum_mul_sum, conv_eq_sum_sub'],
    calc
        ∑ x, ‖∑ y, f y * g (x - y)‖ ≤ ∑ x, ∑ y, ‖f y * g (x - y)‖
          : sum_le_sum $ λ x _, norm_sum_le _ _
      ... = _ : _,
    rw sum_comm,
    simp_rw [norm_mul, sum_product],
    exact sum_congr rfl (λ x _, fintype.sum_equiv (equiv.sub_right x) _ _ $ λ _, rfl) },
  have hp₀ := zero_lt_one.trans hp,
  rw [←rpow_le_rpow_iff _ (mul_nonneg _ _) hp₀, mul_rpow],
  any_goals { exact Lpnorm_nonneg },
  simp_rw [Lpnorm_rpow_eq_sum hp₀.ne', conv_eq_sum_sub'],
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
    { exact rpow_nonneg (sum_nonneg $ λ _ _, norm_nonneg _) },
    { exact mul_nonneg (sum_nonneg $ λ _ _, by positivity)
        (rpow_nonneg $ sum_nonneg $ λ _ _, norm_nonneg _) },
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

/-- A special case of **Young's convolution inequality**. -/
lemma Lpnorm_dconv_le {p : ℝ≥0} (hp : 1 ≤ p) (f g : α → β) : ‖f ○ g‖_[p] ≤ ‖f‖_[p] * ‖g‖_[1] :=
by simpa only [conv_conjneg, Lpnorm_conjneg] using Lpnorm_conv_le hp f (conjneg g)

end is_R_or_C

section real
variables {f g : α → ℝ} --TODO: Include `f : α → ℂ`

lemma L1norm_conv (hf : 0 ≤ f) (hg : 0 ≤ g) : ‖f ∗ g‖_[1] = ‖f‖_[1] * ‖g‖_[1] :=
begin
  have : ∀ x, 0 ≤ ∑ y, f y * g (x - y) := λ x, sum_nonneg (λ y _, mul_nonneg (hf _) (hg _)),
  simp only [L1norm_eq_sum, ←sum_conv, conv_eq_sum_sub', norm_of_nonneg (this _),
    norm_of_nonneg (hf _), norm_of_nonneg (hg _)],
end

lemma L1norm_dconv (hf : 0 ≤ f) (hg : 0 ≤ g) : ‖f ○ g‖_[1] = ‖f‖_[1] * ‖g‖_[1] :=
by simpa using L1norm_conv hf (conjneg_nonneg.2 hg)

end real

/-!
### The ring of functions under convolution

In this section, for a finite group `α`, we define a type synonym `with_conv α β` of the functions
`α → β`. We endow that type synonym with the ring structure given by pointwise addition and
convolution as multiplication.
-/

/-- Type synonym for the functions `α → β` where multiplication is given by convolution. -/
def with_conv (α β : Type*) : Type* := α → β

/-- `to_conv` is the "identity" function from `α → β` to `with_conv α β`. -/
@[nolint unused_arguments]
def to_conv : (α → β) ≃ with_conv α β := equiv.refl _

/-- `of_conv` is the "identity" function from `with_conv α β` to `α → β`. -/
@[nolint unused_arguments]
def of_conv : with_conv α β ≃ (α → β) := equiv.refl _

@[simp] lemma to_conv_symm_eq : (to_conv : (α → β) ≃ with_conv α β).symm = of_conv := rfl
@[simp] lemma of_conv_symm_eq : (of_conv : with_conv α β ≃ (α → β)).symm = to_conv := rfl
@[simp] lemma to_conv_of_conv (f : with_conv α β) : to_conv (of_conv f) = f := rfl
@[simp] lemma of_conv_to_conv (f : α → β) : of_conv (to_conv f) = f := rfl
@[simp] lemma to_conv_inj {f g : α → β} : to_conv f = to_conv g ↔ f = g := iff.rfl
@[simp] lemma of_conv_inj {f g : with_conv α β} : of_conv f = of_conv g ↔ f = g := iff.rfl

@[simp] lemma to_conv_apply (f : α → β) (a : α) : to_conv f a = f a := rfl
@[simp] lemma of_conv_apply (f : with_conv α β) (a : α) : of_conv f a = f a := rfl

@[nolint unused_arguments fintype_finite decidable_classical]
instance [nonempty β] : nonempty (with_conv α β) := pi.nonempty

section comm_semiring
variables [comm_semiring β] [star_ring β]

instance : comm_semiring (with_conv α β) :=
{ one := to_conv (pi.single 0 1 : α → β),
  mul := λ f g, to_conv $ of_conv f ∗ of_conv g,
  mul_assoc := conv_assoc,
  mul_comm := conv_comm,
  mul_zero := conv_zero,
  zero_mul := zero_conv,
  mul_one := λ f, funext $ λ a, by simp [conv_eq_sum_sub, pi.single_apply],
  one_mul := λ f, funext $ λ a, by simp [conv_eq_sum_sub', pi.single_apply],
  left_distrib := conv_add,
  right_distrib := add_conv,
  ..pi.add_comm_monoid }

@[nolint unused_arguments]
instance [has_smul γ β] : has_smul γ (with_conv α β) := pi.has_smul

@[simp] lemma to_conv_zero : to_conv (0 : α → β) = 0 := rfl
@[simp] lemma of_conv_zero : (of_conv 0 : α → β) = 0 := rfl
@[simp] lemma to_conv_add (f g : α → β) : to_conv (f + g) = to_conv f + to_conv g := rfl
@[simp] lemma of_conv_add (f g : with_conv α β) : of_conv (f + g) = of_conv f + of_conv g := rfl
@[simp] lemma to_conv_smul [has_smul γ β] (c : γ) (f : α → β) : to_conv (c • f) = c • f := rfl
@[simp] lemma of_conv_smul [has_smul γ β] (c : γ) (f : with_conv α β) :
  of_conv (c • f) = c • of_conv f := rfl

@[simp] lemma of_conv_mul (f g : with_conv α β) : of_conv (f * g) = of_conv f ∗ of_conv g := rfl
@[simp] lemma to_conv_conv (f g : α → β) : to_conv (f ∗ g) = to_conv f * to_conv g := rfl

end comm_semiring

section comm_ring
variables [comm_ring β] [star_ring β]

instance : comm_ring (with_conv α β) := { ..with_conv.comm_semiring, ..pi.add_comm_group }

@[simp] lemma to_conv_neg (f : α → β) : to_conv (-f) = -to_conv f := rfl
@[simp] lemma of_conv_neg (f : with_conv α β) : of_conv (-f) = -of_conv f := rfl
@[simp] lemma to_conv_sub (f g : α → β) : to_conv (f - g) = to_conv f - to_conv g := rfl
@[simp] lemma of_conv_sub (f g : with_conv α β) : of_conv (f - g) = of_conv f - of_conv g := rfl

end comm_ring
