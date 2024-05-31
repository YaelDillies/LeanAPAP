import LeanAPAP.Prereqs.Discrete.Convolution.Basic
import LeanAPAP.Prereqs.Expect.Complex

/-!
# Convolution in the compact normalisation

This file defines several versions of the discrete convolution of functions with the compact
normalisation.

## Main declarations

* `nconv`: Discrete convolution of two functions in the compact normalisation
* `ndconv`: Discrete difference convolution of two functions in the compact normalisation
* `iterNConv`: Iterated convolution of a function in the compact normalisation

## Notation

* `f ∗ₙ g`: Convolution
* `f ○ₙ g`: Difference convolution
* `f ∗^ₙ n`: Iterated convolution

## Notes

Some lemmas could technically be generalised to a non-commutative semiring domain. Doesn't seem very
useful given that the codomain in applications is either `ℝ`, `ℝ≥0` or `ℂ`.

Similarly we could drop the commutativity asexpectption on the domain, but this is unneeded at this
point in time.

## TODO

Multiplicativise? Probably ugly and not very useful.
-/

open Finset Fintype Function
open scoped BigOperators ComplexConjugate NNReal Pointwise NNRat

variable {α β γ : Type*} [Fintype α] [DecidableEq α] [AddCommGroup α]

/-!
### Convolution of functions

In this section, we define the convolution `f ∗ₙ g` and difference convolution `f ○ₙ g` of functions
`f g : α → β`, and show how they interact.
-/

section Semifield
variable [Semifield β] [CharZero β] [StarRing β] {f g : α → β}

/-- Convolution -/
def nconv (f g : α → β) : α → β := fun a ↦ 𝔼 x : α × α with x.1 + x.2 = a , f x.1 * g x.2

/-- Difference convolution -/
def ndconv (f g : α → β) : α → β := fun a ↦ 𝔼 x : α × α with x.1 - x.2 = a, f x.1 * conj g x.2

/-- The trivial character. -/
def trivNChar : α → β := fun a ↦ if a = 0 then card α else 0

infixl:71 " ∗ₙ " => nconv
infixl:71 " ○ₙ " => ndconv

lemma nconv_apply (f g : α → β) (a : α) :
    (f ∗ₙ g) a = 𝔼 x : α × α with x.1 + x.2 = a, f x.1 * g x.2 := rfl

lemma ndconv_apply (f g : α → β) (a : α) :
    (f ○ₙ g) a = 𝔼 x : α × α with x.1 - x.2 = a , f x.1 * conj g x.2 := rfl

lemma nconv_apply_eq_smul_conv (f g : α → β) (a : α) :
    (f ∗ₙ g) a = (f ∗ g) a /ℚ Fintype.card α := by
  rw [nconv_apply, expect, eq_comm]
  congr 3
  refine card_nbij' (fun b ↦ (b, a - b)) Prod.fst ?_ ?_ ?_ ?_ <;> simp [eq_sub_iff_add_eq', eq_comm]

lemma ndconv_apply_eq_smul_dconv (f g : α → β) (a : α) :
    (f ○ₙ g) a = (f ○ g) a /ℚ Fintype.card α := by
  rw [ndconv_apply, expect, eq_comm]
  congr 3
  refine card_nbij' (fun b ↦ (a + b, b)) Prod.snd ?_ ?_ ?_ ?_ <;> simp [eq_sub_iff_add_eq, eq_comm]

lemma nconv_eq_smul_conv (f g : α → β) : f ∗ₙ g = (f ∗ g) /ℚ Fintype.card α :=
  funext $ nconv_apply_eq_smul_conv _ _

lemma ndconv_eq_smul_dconv (f g : α → β) : (f ○ₙ g) = (f ○ g) /ℚ Fintype.card α :=
  funext $ ndconv_apply_eq_smul_dconv _ _

@[simp] lemma trivNChar_apply (a : α) : (trivNChar a : β) = if a = 0 then (card α : β) else 0 := rfl

@[simp] lemma nconv_conjneg (f g : α → β) : f ∗ₙ conjneg g = f ○ₙ g :=
  funext fun a ↦ expect_bij (fun x _ ↦ (x.1, -x.2)) (fun x hx ↦ by simpa using hx) (fun x _ ↦ rfl)
    (fun x y _ _ h ↦ by simpa [Prod.ext_iff] using h) fun x hx ↦
      ⟨(x.1, -x.2), by simpa [sub_eq_add_neg] using hx, by simp⟩

@[simp] lemma ndconv_conjneg (f g : α → β) : f ○ₙ conjneg g = f ∗ₙ g := by
  rw [←nconv_conjneg, conjneg_conjneg]

@[simp] lemma translate_nconv (a : α) (f g : α → β) : τ a f ∗ₙ g = τ a (f ∗ₙ g) :=
  funext fun b ↦ expect_equiv ((Equiv.subRight a).prodCongr $ Equiv.refl _)
    (by simp [sub_add_eq_add_sub]) (by simp)

@[simp] lemma translate_ndconv (a : α) (f g : α → β) : τ a f ○ₙ g = τ a (f ○ₙ g) :=
  funext fun b ↦ expect_equiv ((Equiv.subRight a).prodCongr $ Equiv.refl _)
    (by simp [sub_right_comm _ a]) (by simp)

@[simp] lemma nconv_translate (a : α) (f g : α → β) : f ∗ₙ τ a g = τ a (f ∗ₙ g) :=
  funext fun b ↦ expect_equiv ((Equiv.refl _).prodCongr $ Equiv.subRight a)
    (by simp [← add_sub_assoc]) (by simp)

@[simp] lemma ndconv_translate (a : α) (f g : α → β) : f ○ₙ τ a g = τ (-a) (f ○ₙ g) :=
  funext fun b ↦ expect_equiv ((Equiv.refl _).prodCongr $ Equiv.subRight a)
    (by simp [sub_sub_eq_add_sub, ← sub_add_eq_add_sub]) (by simp)

lemma nconv_comm (f g : α → β) : f ∗ₙ g = g ∗ₙ f :=
  funext fun a ↦ Finset.expect_equiv (Equiv.prodComm _ _) (by simp [add_comm]) (by simp [mul_comm])

@[simp] lemma conj_nconv (f g : α → β) : conj (f ∗ₙ g) = conj f ∗ₙ conj g :=
  funext fun a ↦ by simp only [Pi.conj_apply, nconv_apply, map_expect, map_mul]

@[simp] lemma conj_ndconv (f g : α → β) : conj (f ○ₙ g) = conj f ○ₙ conj g := by
  simp_rw [← nconv_conjneg, conj_nconv, conjneg_conj]

@[simp] lemma conj_trivNChar : conj (trivNChar : α → β) = trivNChar := by
  ext; simp; split_ifs <;> simp

lemma IsSelfAdjoint.nconv (hf : IsSelfAdjoint f) (hg : IsSelfAdjoint g) : IsSelfAdjoint (f ∗ₙ g) :=
  (conj_nconv _ _).trans $ congr_arg₂ _ hf hg

lemma IsSelfAdjoint.ndconv (hf : IsSelfAdjoint f) (hg : IsSelfAdjoint g) : IsSelfAdjoint (f ○ₙ g) :=
  (conj_ndconv _ _).trans $ congr_arg₂ _ hf hg

@[simp] lemma isSelfAdjoint_trivNChar : IsSelfAdjoint (trivChar : α → β) := conj_trivChar

@[simp]lemma conjneg_nconv (f g : α → β) : conjneg (f ∗ₙ g) = conjneg f ∗ₙ conjneg g := by
  funext a
  simp only [nconv_apply, conjneg_apply, map_expect, map_mul]
  exact Finset.expect_equiv (Equiv.neg (α × α)) (by simp [eq_comm, ← neg_eq_iff_eq_neg, add_comm])
    (by simp)

@[simp] lemma conjneg_ndconv (f g : α → β) : conjneg (f ○ₙ g) = g ○ₙ f := by
  simp_rw [←nconv_conjneg, conjneg_nconv, conjneg_conjneg, nconv_comm]

@[simp] lemma conjneg_trivNChar : conjneg (trivNChar : α → β) = trivNChar := by
  ext; simp; split_ifs <;> simp

@[simp] lemma nconv_zero (f : α → β) : f ∗ₙ 0 = 0 := by ext; simp [nconv_apply]
@[simp] lemma zero_nconv (f : α → β) : 0 ∗ₙ f = 0 := by ext; simp [nconv_apply]
@[simp] lemma ndconv_zero (f : α → β) : f ○ₙ 0 = 0 := by simp [←nconv_conjneg]
@[simp] lemma zero_ndconv (f : α → β) : 0 ○ₙ f = 0 := by rw [←nconv_conjneg]; simp [-nconv_conjneg]

lemma nconv_add (f g h : α → β) : f ∗ₙ (g + h) = f ∗ₙ g + f ∗ₙ h := by
  ext; simp only [nconv_apply, mul_add, expect_add_distrib, Pi.add_apply]

lemma add_nconv (f g h : α → β) : (f + g) ∗ₙ h = f ∗ₙ h + g ∗ₙ h := by
  ext; simp only [nconv_apply, add_mul, expect_add_distrib, Pi.add_apply]

lemma ndconv_add (f g h : α → β) : f ○ₙ (g + h) = f ○ₙ g + f ○ₙ h := by
  simp_rw [←nconv_conjneg, conjneg_add, nconv_add]

lemma add_ndconv (f g h : α → β) : (f + g) ○ₙ h = f ○ₙ h + g ○ₙ h := by
  simp_rw [←nconv_conjneg, add_nconv]

lemma smul_nconv [DistribSMul γ β] [IsScalarTower γ β β] [SMulCommClass γ β β] (c : γ)
    (f g : α → β) : c • f ∗ₙ g = c • (f ∗ₙ g) := by
  have := SMulCommClass.symm γ β β
  ext a
  simp only [Pi.smul_apply, smul_expect, nconv_apply, smul_mul_assoc]

lemma smul_ndconv [DistribSMul γ β] [IsScalarTower γ β β] [SMulCommClass γ β β] (c : γ)
    (f g : α → β) : c • f ○ₙ g = c • (f ○ₙ g) := by
  have := SMulCommClass.symm γ β β
  ext a
  simp only [Pi.smul_apply, smul_expect, ndconv_apply, smul_mul_assoc]

lemma nconv_smul [DistribSMul γ β] [IsScalarTower γ β β] [SMulCommClass γ β β] (c : γ)
    (f g : α → β) : f ∗ₙ c • g = c • (f ∗ₙ g) := by
  have := SMulCommClass.symm γ β β
  ext a
  simp only [Pi.smul_apply, smul_expect, nconv_apply, mul_smul_comm]

lemma ndconv_smul [Star γ] [DistribSMul γ β] [IsScalarTower γ β β] [SMulCommClass γ β β]
    [StarModule γ β] (c : γ) (f g : α → β) : f ○ₙ c • g = star c • (f ○ₙ g) := by
  have := SMulCommClass.symm γ β β
  ext a
  simp only [Pi.smul_apply, smul_expect, ndconv_apply, mul_smul_comm, starRingEnd_apply, star_smul]

alias smul_nconv_assoc := smul_nconv
alias smul_ndconv_assoc := smul_ndconv
alias smul_nconv_left_comm := nconv_smul
alias smul_ndconv_left_comm := ndconv_smul

lemma mul_smul_nconv_comm [Monoid γ] [DistribMulAction γ β] [IsScalarTower γ β β]
    [SMulCommClass γ β β] (c d : γ) (f g : α → β) : (c * d) • (f ∗ₙ g) = c • f ∗ₙ d • g := by
  rw [smul_nconv, nconv_smul, mul_smul]

lemma nconv_assoc (f g h : α → β) : f ∗ₙ g ∗ₙ h = f ∗ₙ (g ∗ₙ h) := by
  simp only [nconv_eq_smul_conv, smul_conv, conv_smul, conv_assoc]

lemma nconv_right_comm (f g h : α → β) : f ∗ₙ g ∗ₙ h = f ∗ₙ h ∗ₙ g := by
  rw [nconv_assoc, nconv_assoc, nconv_comm g]

lemma nconv_left_comm (f g h : α → β) : f ∗ₙ (g ∗ₙ h) = g ∗ₙ (f ∗ₙ h) := by
  rw [←nconv_assoc, ←nconv_assoc, nconv_comm g]

lemma nconv_nconv_nconv_comm (f g h i : α → β) : f ∗ₙ g ∗ₙ (h ∗ₙ i) = f ∗ₙ h ∗ₙ (g ∗ₙ i) := by
  rw [nconv_assoc, nconv_assoc, nconv_left_comm g]

lemma nconv_ndconv_nconv_comm (f g h i : α → β) : f ∗ₙ g ○ₙ (h ∗ₙ i) = f ○ₙ h ∗ₙ (g ○ₙ i) := by
  simp_rw [←nconv_conjneg, conjneg_nconv, nconv_nconv_nconv_comm]

lemma ndconv_nconv_ndconv_comm (f g h i : α → β) : f ○ₙ g ∗ₙ (h ○ₙ i) = f ∗ₙ h ○ₙ (g ∗ₙ i) := by
  simp_rw [←nconv_conjneg, conjneg_nconv, nconv_nconv_nconv_comm]

lemma ndconv_ndconv_ndconv_comm (f g h i : α → β) : f ○ₙ g ○ₙ (h ○ₙ i) = f ○ₙ h ○ₙ (g ○ₙ i) := by
  simp_rw [←nconv_conjneg, conjneg_nconv, nconv_nconv_nconv_comm]

lemma map_nconv {γ} [Semifield γ] [CharZero γ] [StarRing γ] (m : β →+* γ) (f g : α → β) (a : α) : m
    ((f ∗ₙ g) a) = (m ∘ f ∗ₙ m ∘ g) a := by
  simp_rw [nconv_apply, map_expect, map_mul, Function.comp_apply]

lemma comp_nconv {γ} [Semifield γ] [CharZero γ] [StarRing γ] (m : β →+* γ) (f g : α → β) :
    m ∘ (f ∗ₙ g) = m ∘ f ∗ₙ m ∘ g := funext $ map_nconv _ _ _

--TODO: Can we generalise to star ring homs?
-- lemma map_ndconv (f g : α → ℝ≥0) (a : α) : (↑((f ○ₙ g) a) : ℝ) = ((↑) ∘ f ○ₙ (↑) ∘ g) a := by
--   simp_rw [ndconv_apply, NNReal.coe_expect, NNReal.coe_mul, starRingEnd_apply, star_trivial,
--     Function.comp_apply]

lemma nconv_eq_expect_sub (f g : α → β) (a : α) : (f ∗ₙ g) a = 𝔼 t, f (a - t) * g t := by
  rw [nconv_apply]
  refine expect_nbij (fun x ↦ x.2) (fun x _ ↦ mem_univ _) ?_ ?_ fun b _ ↦
    ⟨(a - b, b), mem_filter.2 ⟨mem_univ _, sub_add_cancel _ _⟩, rfl⟩
  any_goals unfold Set.InjOn
  all_goals aesop

lemma nconv_eq_expect_add (f g : α → β) (a : α) : (f ∗ₙ g) a = 𝔼 t, f (a + t) * g (-t) :=
  (nconv_eq_expect_sub _ _ _).trans $ Fintype.expect_equiv (Equiv.neg _) _ _ fun t ↦ by
    simp only [sub_eq_add_neg, Equiv.neg_apply, neg_neg]

lemma ndconv_eq_expect_add (f g : α → β) (a : α) : (f ○ₙ g) a = 𝔼 t, f (a + t) * conj (g t) := by
  simp [←nconv_conjneg, nconv_eq_expect_add]

lemma nconv_eq_expect_sub' (f g : α → β) (a : α) : (f ∗ₙ g) a = 𝔼 t, f t * g (a - t) := by
  rw [nconv_comm, nconv_eq_expect_sub]; simp_rw [mul_comm]

lemma ndconv_eq_expect_sub (f g : α → β) (a : α) : (f ○ₙ g) a = 𝔼 t, f t * conj (g (t - a)) := by
  simp [←nconv_conjneg, nconv_eq_expect_sub']

lemma nconv_eq_expect_add' (f g : α → β) (a : α) : (f ∗ₙ g) a = 𝔼 t, f (-t) * g (a + t) := by
  rw [nconv_comm, nconv_eq_expect_add]; simp_rw [mul_comm]

lemma nconv_apply_add (f g : α → β) (a b : α) : (f ∗ₙ g) (a + b) = 𝔼 t, f (a + t) * g (b - t) :=
  (nconv_eq_expect_sub _ _ _).trans $ Fintype.expect_equiv (Equiv.subLeft b) _ _ fun t ↦ by
    simp [add_sub_assoc, ←sub_add]

lemma ndconv_apply_neg (f g : α → β) (a : α) : (f ○ₙ g) (-a) = conj ((g ○ₙ f) a) := by
  rw [←conjneg_ndconv f, conjneg_apply, Complex.conj_conj]

lemma ndconv_apply_sub (f g : α → β) (a b : α) :
    (f ○ₙ g) (a - b) = 𝔼 t, f (a + t) * conj (g (b + t)) := by
  simp [←nconv_conjneg, sub_eq_add_neg, nconv_apply_add, add_comm]

lemma expect_nconv_mul (f g h : α → β) :
    𝔼 a, (f ∗ₙ g) a * h a = 𝔼 a, 𝔼 b, f a * g b * h (a + b) := by
  simp_rw [nconv_eq_expect_sub', expect_mul]
  rw [expect_comm]
  exact expect_congr rfl fun x _ ↦ Fintype.expect_equiv (Equiv.subRight x) _ _ fun y ↦ by simp

lemma expect_ndconv_mul (f g h : α → β) :
    𝔼 a, (f ○ₙ g) a * h a = 𝔼 a, 𝔼 b, f a * conj (g b) * h (a - b) := by
  simp_rw [ndconv_eq_expect_sub, expect_mul]
  rw [expect_comm]
  exact expect_congr rfl fun x _ ↦ Fintype.expect_equiv (Equiv.subLeft x) _ _ fun y ↦ by simp

lemma expect_nconv (f g : α → β) : 𝔼 a, (f ∗ₙ g) a = (𝔼 a, f a) * 𝔼 a, g a := by
  simpa only [expect_mul_expect, Pi.one_apply, mul_one] using expect_nconv_mul f g 1

lemma expect_ndconv (f g : α → β) : 𝔼 a, (f ○ₙ g) a = (𝔼 a, f a) * 𝔼 a, conj (g a) := by
  simpa only [expect_mul_expect, Pi.one_apply, mul_one] using expect_ndconv_mul f g 1

@[simp] lemma nconv_const (f : α → β) (b : β) : f ∗ₙ const _ b = const _ ((𝔼 x, f x) * b) := by
  ext; simp [nconv_eq_expect_sub', expect_mul]

@[simp] lemma const_nconv (b : β) (f : α → β) : const _ b ∗ₙ f = const _ (b * 𝔼 x, f x) := by
  ext; simp [nconv_eq_expect_sub, mul_expect]

@[simp]
lemma ndconv_const (f : α → β) (b : β) : f ○ₙ const _ b = const _ ((𝔼 x, f x) * conj b) := by
  ext; simp [ndconv_eq_expect_sub, expect_mul]

@[simp]
lemma const_ndconv (b : β) (f : α → β) : const _ b ○ₙ f = const _ (b * 𝔼 x, conj (f x)) := by
  ext; simp [ndconv_eq_expect_add, mul_expect]

@[simp] lemma nconv_trivNChar [CharZero β] (f : α → β) : f ∗ₙ trivNChar = f := by
  ext a; simp [nconv_eq_expect_sub, card_univ, NNRat.smul_def, mul_comm]

@[simp] lemma trivNChar_nconv [CharZero β] (f : α → β) : trivNChar ∗ₙ f = f := by
  rw [nconv_comm, nconv_trivNChar]

@[simp] lemma ndconv_trivNChar [CharZero β] (f : α → β) : f ○ₙ trivNChar = f := by
  rw [← nconv_conjneg, conjneg_trivNChar, nconv_trivNChar]

@[simp] lemma trivNChar_ndconv [CharZero β] (f : α → β) : trivNChar ○ₙ f = conjneg f := by
  rw [← nconv_conjneg, trivNChar_nconv]

lemma support_nconv_subset (f g : α → β) : support (f ∗ₙ g) ⊆ support f + support g := by
  rintro a ha
  obtain ⟨x, hx, h⟩ := exists_ne_zero_of_expect_ne_zero ha
  exact ⟨_, left_ne_zero_of_mul h, _, right_ne_zero_of_mul h, (mem_filter.1 hx).2⟩

lemma support_ndconv_subset (f g : α → β) : support (f ○ₙ g) ⊆ support f - support g := by
  simpa [sub_eq_add_neg] using support_nconv_subset f (conjneg g)

-- lemma indicate_nconv_indicate_apply (s t : Finset α) (a : α) :
--     (𝟭_[β] s ∗ₙ 𝟭 t) a = ((s ×ˢ t).filter fun x : α × α ↦ x.1 + x.2 = a).card := by
--   simp only [nconv_apply, indicate_apply, ←ite_and, filter_comm, boole_mul, expect_boole]
--   simp_rw [←mem_product, filter_univ_mem]

-- lemma indicate_ndconv_indicate_apply (s t : Finset α) (a : α) :
--     (𝟭_[β] s ○ₙ 𝟭 t) a = ((s ×ˢ t).filter fun x : α × α ↦ x.1 - x.2 = a).card := by
--   simp only [ndconv_apply, indicate_apply, ←ite_and, filter_comm, boole_mul, expect_boole,
--     apply_ite conj, map_one, map_zero, Pi.conj_apply]
--   simp_rw [←mem_product, filter_univ_mem]

end Semifield

section Field
variable [Field β] [CharZero β] [StarRing β]

@[simp] lemma nconv_neg (f g : α → β) : f ∗ₙ -g = -(f ∗ₙ g) := by ext; simp [nconv_apply]
@[simp] lemma neg_nconv (f g : α → β) : -f ∗ₙ g = -(f ∗ₙ g) := by ext; simp [nconv_apply]
@[simp] lemma ndconv_neg (f g : α → β) : f ○ₙ -g = -(f ○ₙ g) := by ext; simp [ndconv_apply]
@[simp] lemma neg_ndconv (f g : α → β) : -f ○ₙ g = -(f ○ₙ g) := by ext; simp [ndconv_apply]

lemma nconv_sub (f g h : α → β) : f ∗ₙ (g - h) = f ∗ₙ g - f ∗ₙ h := by
  simp only [sub_eq_add_neg, nconv_add, nconv_neg]

lemma sub_nconv (f g h : α → β) : (f - g) ∗ₙ h = f ∗ₙ h - g ∗ₙ h := by
  simp only [sub_eq_add_neg, add_nconv, neg_nconv]

lemma ndconv_sub (f g h : α → β) : f ○ₙ (g - h) = f ○ₙ g - f ○ₙ h := by
  simp only [sub_eq_add_neg, ndconv_add, ndconv_neg]

lemma sub_ndconv (f g h : α → β) : (f - g) ○ₙ h = f ○ₙ h - g ○ₙ h := by
  simp only [sub_eq_add_neg, add_ndconv, neg_ndconv]

end Field

section Semifield
variable [Semifield β] [StarRing β] [SMul ℚ≥0 β] [CharZero β]

@[simp] lemma indicate_univ_nconv_indicate_univ : 𝟭_[β] (univ : Finset α) ∗ₙ 𝟭 univ = 𝟭 univ := by
  ext; simp [indicate_apply, nconv_eq_expect_add, card_univ, *]

@[simp] lemma indicate_univ_ndconv_mu_univ : 𝟭_[β] (univ : Finset α) ○ₙ 𝟭 univ = 𝟭 univ := by
  ext; simp [indicate_apply, ndconv_eq_expect_add, card_univ, *]

end Semifield

section Field
variable [Field β] [StarRing β] [CharZero β]

@[simp] lemma balance_nconv (f g : α → β) : balance (f ∗ₙ g) = balance f ∗ₙ balance g := by
  simp [balance, nconv_sub, sub_nconv, expect_nconv, expect_sub_distrib]

@[simp] lemma balance_ndconv (f g : α → β) : balance (f ○ₙ g) = balance f ○ₙ balance g := by
  simp [balance, ndconv_sub, sub_ndconv, expect_ndconv, map_expect, expect_sub_distrib]

end Field

namespace RCLike
variable {𝕜 : Type} [RCLike 𝕜] (f g : α → ℝ) (a : α)

@[simp, norm_cast]
lemma coe_nconv : (f ∗ₙ g) a = ((↑) ∘ f ∗ₙ (↑) ∘ g : α → 𝕜) a := map_nconv (algebraMap ℝ 𝕜) _ _ _

@[simp, norm_cast]
lemma coe_ndconv : (f ○ₙ g) a = ((↑) ∘ f ○ₙ (↑) ∘ g : α → 𝕜) a := by simp [ndconv_apply, coe_expect]

@[simp]
lemma coe_comp_nconv : ofReal ∘ (f ∗ₙ g) = ((↑) ∘ f ∗ₙ (↑) ∘ g : α → 𝕜) := funext $ coe_nconv _ _

@[simp]
lemma coe_comp_ndconv : ofReal ∘ (f ○ₙ g) = ((↑) ∘ f ○ₙ (↑) ∘ g : α → 𝕜) := funext $ coe_ndconv _ _

end RCLike

namespace Complex
variable (f g : α → ℝ) (a : α)

@[simp, norm_cast]
lemma coe_nconv : (f ∗ₙ g) a = ((↑) ∘ f ∗ₙ (↑) ∘ g : α → ℂ) a := RCLike.coe_nconv _ _ _

@[simp, norm_cast]
lemma coe_ndconv : (f ○ₙ g) a = ((↑) ∘ f ○ₙ (↑) ∘ g : α → ℂ) a := RCLike.coe_ndconv _ _ _

@[simp]
lemma coe_comp_nconv : ofReal' ∘ (f ∗ₙ g) = ((↑) ∘ f ∗ₙ (↑) ∘ g : α → ℂ) := funext $ coe_nconv _ _

@[simp]
lemma coe_comp_ndconv : ofReal' ∘ (f ○ₙ g) = ((↑) ∘ f ○ₙ (↑) ∘ g : α → ℂ) := funext $ coe_ndconv _ _

end Complex

namespace NNReal
variable (f g : α → ℝ≥0) (a : α)

@[simp, norm_cast]
lemma coe_nconv : (f ∗ₙ g) a = ((↑) ∘ f ∗ₙ (↑) ∘ g : α → ℝ) a := map_nconv NNReal.toRealHom _ _ _

@[simp, norm_cast]
lemma coe_ndconv : (f ○ₙ g) a = ((↑) ∘ f ○ₙ (↑) ∘ g : α → ℝ) a := by simp [ndconv_apply, coe_expect]

@[simp]
lemma coe_comp_nconv : ((↑) : _ → ℝ) ∘ (f ∗ₙ g) = (↑) ∘ f ∗ₙ (↑) ∘ g := funext $ coe_nconv _ _

@[simp]
lemma coe_comp_ndconv : ((↑) : _ → ℝ) ∘ (f ○ₙ g) = (↑) ∘ f ○ₙ (↑) ∘ g := funext $ coe_ndconv _ _

end NNReal

/-! ### Iterated convolution -/

section Semifield
variable [Semifield β] [CharZero β] [SMul ℚ≥0 β] [StarRing β] {f g : α → β} {n : ℕ}

/-- Iterated convolution. -/
def iterNConv (f : α → β) : ℕ → α → β
  | 0 => trivNChar
  | n + 1 => iterNConv f n ∗ₙ f

infixl:78 " ∗^ₙ " => iterNConv

@[simp] lemma iterNConv_zero (f : α → β) : f ∗^ₙ 0 = trivNChar := rfl
@[simp] lemma iterNConv_one [CharZero β] (f : α → β) : f ∗^ₙ 1 = f := trivNChar_nconv _

lemma iterNConv_succ (f : α → β) (n : ℕ) : f ∗^ₙ (n + 1) = f ∗^ₙ n ∗ₙ f := rfl
lemma iterNConv_succ' (f : α → β) (n : ℕ) : f ∗^ₙ (n + 1) = f ∗ₙ f ∗^ₙ n := nconv_comm _ _

lemma iterNConv_add [CharZero β] (f : α → β) (m : ℕ) : ∀ n, f ∗^ₙ (m + n) = f ∗^ₙ m ∗ₙ f ∗^ₙ n
  | 0 => by simp
  | n + 1 => by simp [←add_assoc, iterNConv_succ', iterNConv_add, nconv_left_comm]

lemma iterNConv_mul [CharZero β] (f : α → β) (m : ℕ) : ∀ n, f ∗^ₙ (m * n) = f ∗^ₙ m ∗^ₙ n
  | 0 => rfl
  | n + 1 => by simp [mul_add_one, iterNConv_succ, iterNConv_add, iterNConv_mul]

lemma iterNConv_mul' [CharZero β] (f : α → β) (m n : ℕ) : f ∗^ₙ (m * n) = f ∗^ₙ n ∗^ₙ m := by
  rw [mul_comm, iterNConv_mul]

@[simp] lemma conj_iterNConv [CharZero β] (f : α → β) : ∀ n, conj (f ∗^ₙ n) = conj f ∗^ₙ n
  | 0 => by simp
  | n + 1 => by simp [iterNConv_succ, conj_iterNConv]

@[simp]
lemma conjneg_iterNConv [CharZero β] (f : α → β) : ∀ n, conjneg (f ∗^ₙ n) = conjneg f ∗^ₙ n
  | 0 => by simp
  | n + 1 => by simp [iterNConv_succ, conjneg_iterNConv]

lemma iterNConv_nconv_distrib [CharZero β] (f g : α → β) : ∀ n, (f ∗ₙ g) ∗^ₙ n = f ∗^ₙ n ∗ₙ g ∗^ₙ n
  | 0 => (nconv_trivNChar _).symm
  | n + 1 => by simp_rw [iterNConv_succ, iterNConv_nconv_distrib, nconv_nconv_nconv_comm]

lemma iterNConv_ndconv_distrib [CharZero β] (f g : α → β) : ∀ n, (f ○ₙ g) ∗^ₙ n = f ∗^ₙ n ○ₙ g ∗^ₙ n
  | 0 => (ndconv_trivNChar _).symm
  | n + 1 => by simp_rw [iterNConv_succ, iterNConv_ndconv_distrib, nconv_ndconv_nconv_comm]

@[simp] lemma zero_iterNConv : ∀ {n}, n ≠ 0 → (0 : α → β) ∗^ₙ n = 0
  | 0, hn => by cases hn rfl
  | n + 1, _ => nconv_zero _

@[simp] lemma smul_iterNConv [Monoid γ] [DistribMulAction γ β] [IsScalarTower γ β β]
    [SMulCommClass γ β β] (c : γ) (f : α → β) : ∀ n, (c • f) ∗^ₙ n = c ^ n • f ∗^ₙ n
  | 0 => by simp
  | n + 1 => by simp_rw [iterNConv_succ, smul_iterNConv _ _ n, pow_succ, mul_smul_nconv_comm]

lemma comp_iterNConv {γ} [Semifield γ] [CharZero γ] [StarRing γ] (m : β →+* γ) (f : α → β) :
    ∀ n, m ∘ (f ∗^ₙ n) = m ∘ f ∗^ₙ n
  | 0 => by ext; simp; split_ifs <;> simp
  | n + 1 => by simp [iterNConv_succ, comp_nconv, comp_iterNConv]

lemma map_iterNConv {γ} [Semifield γ] [CharZero γ] [StarRing γ] (m : β →+* γ) (f : α → β) (a : α)
    (n : ℕ) : m ((f ∗^ₙ n) a) = (m ∘ f ∗^ₙ n) a := congr_fun (comp_iterNConv m _ _) _

lemma expect_iterNConv [CharZero β] (f : α → β) : ∀ n, 𝔼 a, (f ∗^ₙ n) a = (𝔼 a, f a) ^ n
  | 0 => by simp [filter_eq', card_univ, NNRat.smul_def]
  | n + 1 => by simp only [iterNConv_succ, expect_nconv, expect_iterNConv, pow_succ]

@[simp] lemma iterNConv_trivNChar [CharZero β] : ∀ n, (trivNChar : α → β) ∗^ₙ n = trivNChar
  | 0 => rfl
  | _n + 1 => (nconv_trivNChar _).trans $ iterNConv_trivNChar _

lemma support_iterNConv_subset (f : α → β) : ∀ n, support (f ∗^ₙ n) ⊆ n • support f
  | 0 => by
    simp only [iterNConv_zero, zero_smul, support_subset_iff, Ne, ite_eq_right_iff, exists_prop,
      not_forall, Set.mem_zero, and_imp, forall_eq, eq_self_iff_true, imp_true_iff, trivNChar_apply]
  | n + 1 =>
    (support_nconv_subset _ _).trans $ Set.add_subset_add_right $ support_iterNConv_subset _ _

-- lemma indicate_iterNConv_apply (s : Finset α) (n : ℕ) (a : α) :
--     (𝟭_[ℝ] s ∗^ₙ n) a = ((piFinset fun _i ↦ s).filter fun x : Fin n → α ↦ ∑ i, x i = a).card := by
--   induction' n with n ih generalizing a
--   · simp [apply_ite card, eq_comm]
--   simp_rw [iterNConv_succ, nconv_eq_expect_sub', ih, indicate_apply, boole_mul, expect_ite, filter_univ_mem,
--     expect_const_zero, add_zero, ←Nat.cast_expect, ←Finset.card_sigma, Nat.cast_inj]
--   refine' Finset.card_bij (fun f _ ↦ Fin.cons f.1 f.2) _ _ _
--   · simp only [Fin.expect_cons, eq_sub_iff_add_eq', mem_sigma, mem_filter, mem_piFinset, and_imp]
--     refine' fun bf hb hf ha ↦ ⟨Fin.cases _ _, ha⟩
--     · exact hb
--     · simpa only [Fin.cons_succ]
--   · simp only [Sigma.ext_iff, Fin.cons_eq_cons, heq_iff_eq, imp_self, imp_true_iff, forall_const,
--       Sigma.forall]
--   · simp only [mem_filter, mem_piFinset, mem_sigma, exists_prop, Sigma.exists, and_imp,
--       eq_sub_iff_add_eq', and_assoc]
--     exact fun f hf ha ↦
--       ⟨f 0, Fin.tail f, hf _, fun _ ↦ hf _, (Fin.expect_univ_succ _).symm.trans ha,
--         Fin.cons_self_tail _⟩

end Semifield

section Field
variable [Field β] [StarRing β] [CharZero β]

@[simp] lemma balance_iterNConv (f : α → β) : ∀ {n}, n ≠ 0 → balance (f ∗^ₙ n) = balance f ∗^ₙ n
  | 0, h => by cases h rfl
  | 1, _ => by simp
  | n + 2, _ => by simp [iterNConv_succ _ (n + 1), balance_iterNConv _ n.succ_ne_zero]

end Field

namespace NNReal
variable {f : α → ℝ≥0}

@[simp, norm_cast]
lemma coe_iterNConv (f : α → ℝ≥0) (n : ℕ) (a : α) : (↑((f ∗^ₙ n) a) : ℝ) = ((↑) ∘ f ∗^ₙ n) a :=
  map_iterNConv NNReal.toRealHom _ _ _

end NNReal
