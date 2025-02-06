import LeanAPAP.Mathlib.Analysis.Convolution
import LeanAPAP.Mathlib.Analysis.NormedSpace.OperatorNorm.Mul
import LeanAPAP.Mathlib.MeasureTheory.Group.Measure
import Mathlib.Algebra.Group.Translate
import Mathlib.Algebra.Star.Conjneg
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.NNReal.Star


/-!
# Convolution

This file defines several versions of the discrete convolution of functions.

## Main declarations

* `conv`: Discrete convolution of two functions
* `dconv`: Discrete difference convolution of two functions
* `iterConv`: Iterated convolution of a function

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

open Finset Fintype Function MeasureTheory
open scoped ComplexConjugate NNReal Pointwise translate

namespace Analysis.Discrete
variable {G H R S : Type*} [AddCommGroup G]

/-! ### Trivial character -/

section CommSemiring
variable [DecidableEq G] [CommSemiring R]

/-- The trivial character. -/
def trivChar : G → R := fun a ↦ if a = 0 then 1 else 0

@[simp] lemma trivChar_apply (a : G) : (trivChar a : R) = if a = 0 then 1 else 0 := rfl

variable [StarRing R]

@[simp] lemma conj_trivChar : conj (trivChar : G → R) = trivChar := by ext; simp
@[simp] lemma conjneg_trivChar : conjneg (trivChar : G → R) = trivChar := by ext; simp

@[simp] lemma isSelfAdjoint_trivChar : IsSelfAdjoint (trivChar : G → R) := conj_trivChar

end CommSemiring

/-! ### Convolution -/

section NormedRing
variable [NormedRing R] [NormedSpace ℝ R] [IsScalarTower ℝ R R] [SMulCommClass ℝ R R]
  [MeasurableSpace G] {f g : G → R}

/-- Discrete convolution -/
noncomputable abbrev conv (f g : G → R) : G → R := convolution f g (.mul ℝ _) .count

scoped infixl:71 " ∗ " => conv

-- lemma conv_apply (f g : G → R) (a : G) :
--     (f ∗ g) a = ∑ x : G × G with x.1 + x.2 = a, f x.1 * g x.2 := rfl

lemma conv_zero (f : G → R) : f ∗ 0 = 0 := convolution_zero
lemma zero_conv (f : G → R) : 0 ∗ f = 0 := zero_convolution

lemma smul_conv [DistribSMul H R] [IsScalarTower H R R] (c : H) (f g : G → R) :
    c • f ∗ g = c • (f ∗ g) := by rw [conv, smul_convolution]

lemma conv_smul [DistribSMul H R] [SMulCommClass H R R] (c : H) (f g : G → R) :
    f ∗ c • g = c • (f ∗ g) := convolution_smul

lemma mul_smul_conv_comm [Monoid H] [DistribMulAction H R] [IsScalarTower H R R]
    [SMulCommClass H R R] (c d : H) (f g : G → R) : (c * d) • (f ∗ g) = c • f ∗ d • g := by
  rw [smul_conv, conv_smul, mul_smul]

alias smul_conv_assoc := smul_conv
alias smul_conv_left_comm := conv_smul

section Discrete
variable [Finite G] [MeasurableSingletonClass G]

lemma conv_add (f g h : G → R) : f ∗ (g + h) = f ∗ g + f ∗ h :=
  ConvolutionExists.distrib_add .of_finite .of_finite

lemma add_conv (f g h : G → R) : (f + g) ∗ h = f ∗ h + g ∗ h :=
  ConvolutionExists.add_distrib .of_finite .of_finite

end Discrete

variable [MeasurableAdd G] [MeasurableNeg G]

@[simp] lemma translate_conv (a : G) (f g : G → R) : τ a f ∗ g = τ a (f ∗ g) :=
  funext fun b ↦ sum_equiv ((Equiv.subRight a).prodCongr <| Equiv.refl _)
    (by simp [sub_add_eq_add_sub]) (by simp)

@[simp] lemma conv_translate (a : G) (f g : G → R) : f ∗ τ a g = τ a (f ∗ g) :=
  funext fun b ↦ sum_equiv ((Equiv.refl _).prodCongr <| Equiv.subRight a)
    (by simp [← add_sub_assoc]) (by simp)

end NormedRing

section NormedCommRing
variable [NormedCommRing R] [NormedSpace ℝ R] [IsScalarTower ℝ R R] [SMulCommClass ℝ R R]
  [MeasurableSpace G] {f g : G → R}

variable [MeasurableAdd G] [MeasurableNeg G]

lemma conv_comm (f g : G → R) : f ∗ g = g ∗ f := .trans (by simp) (convolution_flip _)

lemma conv_assoc (f g h : G → R) : f ∗ g ∗ h = f ∗ (g ∗ h) := by
  ext a
  simp only [sum_mul, mul_sum, conv_apply, Finset.sum_sigma']
  apply sum_nbij' (fun ⟨(_b, c), (d, e)⟩ ↦ ⟨(d, e + c), (e, c)⟩)
    (fun ⟨(b, _c), (d, e)⟩ ↦ ⟨(b + d, e), (b, d)⟩) <;> aesop (add simp [add_assoc, mul_assoc])

lemma conv_right_comm (f g h : G → R) : f ∗ g ∗ h = f ∗ h ∗ g := by
  rw [conv_assoc, conv_assoc, conv_comm g]

lemma conv_left_comm (f g h : G → R) : f ∗ (g ∗ h) = g ∗ (f ∗ h) := by
  rw [← conv_assoc, ← conv_assoc, conv_comm g]

lemma conv_rotate (f g h : G → R) : f ∗ g ∗ h = g ∗ h ∗ f := by rw [conv_assoc, conv_comm]
lemma conv_rotate' (f g h : G → R) : f ∗ (g ∗ h) = g ∗ (h ∗ f) := by rw [conv_comm, ← conv_assoc]

lemma conv_conv_conv_comm (f g h i : G → R) : f ∗ g ∗ (h ∗ i) = f ∗ h ∗ (g ∗ i) := by
  rw [conv_assoc, conv_assoc, conv_left_comm g]

lemma map_conv [CommSemiring S] (m : R →+* S) (f g : G → R) (a : G) :
    m ((f ∗ g) a) = (m ∘ f ∗ m ∘ g) a := by simp [conv_apply, map_sum, map_mul]

lemma comp_conv [CommSemiring S] (m : R →+* S) (f g : G → R) : m ∘ (f ∗ g) = m ∘ f ∗ m ∘ g :=
  funext <| map_conv _ _ _

lemma conv_eq_sum_sub (f g : G → R) (a : G) : (f ∗ g) a = ∑ t, f (a - t) * g t := by
  rw [conv_apply]; apply sum_nbij' Prod.snd (fun b ↦ (a - b, b)) <;> aesop

lemma conv_eq_sum_add (f g : G → R) (a : G) : (f ∗ g) a = ∑ t, f (a + t) * g (-t) :=
  (conv_eq_sum_sub _ _ _).trans <| Fintype.sum_equiv (Equiv.neg _) _ _ fun t ↦ by
    simp only [sub_eq_add_neg, Equiv.neg_apply, neg_neg]

lemma conv_eq_sum_sub' (f g : G → R) (a : G) : (f ∗ g) a = ∑ t, f t * g (a - t) := by
  rw [conv_comm, conv_eq_sum_sub]; simp_rw [mul_comm]

lemma conv_eq_sum_add' (f g : G → R) (a : G) : (f ∗ g) a = ∑ t, f (-t) * g (a + t) := by
  rw [conv_comm, conv_eq_sum_add]; simp_rw [mul_comm]

lemma conv_apply_add (f g : G → R) (a b : G) : (f ∗ g) (a + b) = ∑ t, f (a + t) * g (b - t) :=
  (conv_eq_sum_sub _ _ _).trans <| Fintype.sum_equiv (Equiv.subLeft b) _ _ fun t ↦ by
    simp [add_sub_assoc, ← sub_add]

lemma sum_conv_mul (f g h : G → R) : ∑ a, (f ∗ g) a * h a = ∑ a, ∑ b, f a * g b * h (a + b) := by
  simp_rw [conv_eq_sum_sub', sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun x _ ↦ Fintype.sum_equiv (Equiv.subRight x) _ _ fun y ↦ by simp

lemma sum_conv (f g : G → R) : ∑ a, (f ∗ g) a = (∑ a, f a) * ∑ a, g a := by
  simpa only [Fintype.sum_mul_sum, Pi.one_apply, mul_one] using sum_conv_mul f g 1

@[simp] lemma conv_const (f : G → R) (b : R) : f ∗ const _ b = const _ ((∑ x, f x) * b) := by
  ext; simp [conv_eq_sum_sub', sum_mul]

@[simp] lemma const_conv (b : R) (f : G → R) : const _ b ∗ f = const _ (b * ∑ x, f x) := by
  ext; simp [conv_eq_sum_sub, mul_sum]

@[simp] lemma conv_trivChar (f : G → R) : f ∗ trivChar = f := by ext a; simp [conv_eq_sum_sub]
@[simp] lemma trivChar_conv (f : G → R) : trivChar ∗ f = f := by rw [conv_comm, conv_trivChar]

lemma support_conv_subset (f g : G → R) : support (f ∗ g) ⊆ support f + support g := by
  rintro a ha
  obtain ⟨x, hx, h⟩ := exists_ne_zero_of_sum_ne_zero ha
  exact ⟨_, left_ne_zero_of_mul h, _, right_ne_zero_of_mul h, (mem_filter.1 hx).2⟩

/-! ### Difference convolution -/

variable [StarRing R]

/-- Difference convolution -/
def dconv (f g : G → R) : G → R := fun a ↦ ∑ x : G × G with x.1 - x.2 = a, f x.1 * conj g x.2

infixl:71 " ○ " => dconv

lemma dconv_apply (f g : G → R) (a : G) :
    (f ○ g) a = ∑ x : G × G with x.1 - x.2 = a , f x.1 * conj g x.2 := rfl

@[simp] lemma dconv_zero (f : G → R) : f ○ 0 = 0 := by ext; simp [dconv_apply]
@[simp] lemma zero_dconv (f : G → R) : 0 ○ f = 0 := by ext; simp [dconv_apply]

lemma dconv_add (f g h : G → R) : f ○ (g + h) = f ○ g + f ○ h := by
  ext; simp [dconv_apply, mul_add, sum_add_distrib]

lemma add_dconv (f g h : G → R) : (f + g) ○ h = f ○ h + g ○ h := by
  ext; simp [dconv_apply, add_mul, sum_add_distrib]

lemma smul_dconv [DistribSMul H R] [IsScalarTower H R R] (c : H) (f g : G → R) :
    c • f ○ g = c • (f ○ g) := by ext; simp [dconv_apply, smul_sum, smul_mul_assoc]

lemma dconv_smul [Star H] [DistribSMul H R] [SMulCommClass H R R] [StarModule H R] (c : H)
    (f g : G → R) : f ○ c • g = star c • (f ○ g) := by
  ext; simp [dconv_apply, smul_sum, mul_smul_comm, starRingEnd_apply, star_smul]

@[simp] lemma translate_dconv (a : G) (f g : G → R) : τ a f ○ g = τ a (f ○ g) :=
  funext fun b ↦ sum_equiv ((Equiv.subRight a).prodCongr <| Equiv.refl _)
    (by simp [sub_right_comm _ a]) (by simp)

@[simp] lemma dconv_translate (a : G) (f g : G → R) : f ○ τ a g = τ (-a) (f ○ g) :=
  funext fun b ↦ sum_equiv ((Equiv.refl _).prodCongr <| Equiv.subRight a)
    (by simp [sub_sub_eq_add_sub, ← sub_add_eq_add_sub]) (by simp)

@[simp] lemma conv_conjneg (f g : G → R) : f ∗ conjneg g = f ○ g :=
  funext fun a ↦ sum_equiv ((Equiv.refl _).prodCongr <| Equiv.neg _) (by simp) (by simp)

@[simp] lemma dconv_conjneg (f g : G → R) : f ○ conjneg g = f ∗ g := by
  rw [← conv_conjneg, conjneg_conjneg]

@[simp] lemma conj_conv_apply (f g : G → R) (a : G) : conj ((f ∗ g) a) = (conj f ∗ conj g) a := by
  simp only [Pi.conj_apply, conv_apply, map_sum, map_mul]

@[simp] lemma conj_dconv_apply (f g : G → R) (a : G) : conj ((f ○ g) a) = (conj f ○ conj g) a := by
  simp_rw [← conv_conjneg, conj_conv_apply, conjneg_conj]

@[simp] lemma conj_conv (f g : G → R) : conj (f ∗ g) = conj f ∗ conj g :=
  funext <| conj_conv_apply _ _

@[simp] lemma conj_dconv (f g : G → R) : conj (f ○ g) = conj f ○ conj g :=
  funext <| conj_dconv_apply _ _

lemma IsSelfAdjoint.conv (hf : IsSelfAdjoint f) (hg : IsSelfAdjoint g) : IsSelfAdjoint (f ∗ g) :=
  (conj_conv _ _).trans <| congr_arg₂ _ hf hg

lemma IsSelfAdjoint.dconv (hf : IsSelfAdjoint f) (hg : IsSelfAdjoint g) : IsSelfAdjoint (f ○ g) :=
  (conj_dconv _ _).trans <| congr_arg₂ _ hf hg

@[simp]lemma conjneg_conv (f g : G → R) : conjneg (f ∗ g) = conjneg f ∗ conjneg g := by
  funext a
  simp only [conv_apply, conjneg_apply, map_sum, map_mul]
  exact sum_equiv (Equiv.neg _) (by simp [← neg_eq_iff_eq_neg, add_comm]) (by simp)

@[simp] lemma conjneg_dconv (f g : G → R) : conjneg (f ○ g) = g ○ f := by
  simp_rw [← conv_conjneg, conjneg_conv, conjneg_conjneg, conv_comm]
alias smul_dconv_assoc := smul_dconv
alias smul_dconv_left_comm := dconv_smul

lemma dconv_right_comm (f g h : G → R) : f ○ g ○ h = f ○ h ○ g := by
  simp_rw [← conv_conjneg, conv_right_comm]

lemma conv_dconv_assoc (f g h : G → R) : f ∗ g ○ h = f ∗ (g ○ h) := by
  simp_rw [← conv_conjneg, conv_assoc]

lemma conv_dconv_left_comm (f g h : G → R) : f ∗ (g ○ h) = g ∗ (f ○ h) := by
  simp_rw [← conv_conjneg, conv_left_comm]

lemma conv_dconv_right_comm (f g h : G → R) : f ∗ g ○ h = f ○ h ∗ g := by
  simp_rw [← conv_conjneg, conv_right_comm]

lemma conv_dconv_conv_comm (f g h i : G → R) : f ∗ g ○ (h ∗ i) = f ○ h ∗ (g ○ i) := by
  simp_rw [← conv_conjneg, conjneg_conv, conv_conv_conv_comm]

lemma dconv_conv_dconv_comm (f g h i : G → R) : f ○ g ∗ (h ○ i) = f ∗ h ○ (g ∗ i) := by
  simp_rw [← conv_conjneg, conjneg_conv, conv_conv_conv_comm]

lemma dconv_dconv_dconv_comm (f g h i : G → R) : f ○ g ○ (h ○ i) = f ○ h ○ (g ○ i) := by
  simp_rw [← conv_conjneg, conjneg_conv, conv_conv_conv_comm]

--TODO: Can we generalise to star ring homs?
lemma map_dconv (f g : G → ℝ≥0) (a : G) : (↑((f ○ g) a) : ℝ) = ((↑) ∘ f ○ (↑) ∘ g) a := by
  simp_rw [dconv_apply, NNReal.coe_sum, NNReal.coe_mul, starRingEnd_apply, star_trivial,
    Function.comp_apply]

lemma comp_dconv (f g : G → ℝ≥0) : ((↑) ∘ (f ○ g) : G → ℝ) = (↑) ∘ f ○ (↑) ∘ g :=
  funext <| map_dconv _ _

lemma dconv_eq_sum_sub (f g : G → R) (a : G) : (f ○ g) a = ∑ t, f (a - t) * conj (g (-t)) := by
  simp [← conv_conjneg, conv_eq_sum_sub]

lemma dconv_eq_sum_add (f g : G → R) (a : G) : (f ○ g) a = ∑ t, f (a + t) * conj (g t) := by
  simp [← conv_conjneg, conv_eq_sum_add]

lemma dconv_eq_sum_sub' (f g : G → R) (a : G) : (f ○ g) a = ∑ t, f t * conj (g (t - a)) := by
  simp [← conv_conjneg, conv_eq_sum_sub']

lemma dconv_eq_sum_add' (f g : G → R) (a : G) : (f ○ g) a = ∑ t, f (-t) * conj g (-(a + t)) := by
  simp [← conv_conjneg, conv_eq_sum_add']

lemma dconv_apply_neg (f g : G → R) (a : G) : (f ○ g) (-a) = conj ((g ○ f) a) := by
  rw [← conjneg_dconv f, conjneg_apply, Complex.conj_conj]

lemma dconv_apply_sub (f g : G → R) (a b : G) :
    (f ○ g) (a - b) = ∑ t, f (a + t) * conj (g (b + t)) := by
  simp [← conv_conjneg, sub_eq_add_neg, conv_apply_add, add_comm]

lemma sum_dconv_mul (f g h : G → R) :
    ∑ a, (f ○ g) a * h a = ∑ a, ∑ b, f a * conj (g b) * h (a - b) := by
  simp_rw [dconv_eq_sum_sub', sum_mul]
  rw [sum_comm]
  exact Fintype.sum_congr _ _ fun x ↦ Fintype.sum_equiv (Equiv.subLeft x) _ _ fun y ↦ by simp

lemma sum_dconv (f g : G → R) : ∑ a, (f ○ g) a = (∑ a, f a) * ∑ a, conj (g a) := by
  simpa only [Fintype.sum_mul_sum, Pi.one_apply, mul_one] using sum_dconv_mul f g 1

@[simp] lemma dconv_const (f : G → R) (b : R) : f ○ const _ b = const _ ((∑ x, f x) * conj b) := by
  ext; simp [dconv_eq_sum_sub', sum_mul]

@[simp] lemma const_dconv (b : R) (f : G → R) : const _ b ○ f = const _ (b * ∑ x, conj (f x)) := by
  ext; simp [dconv_eq_sum_add, mul_sum]

@[simp] lemma dconv_trivChar (f : G → R) : f ○ trivChar = f := by ext a; simp [dconv_eq_sum_add]
@[simp] lemma trivChar_dconv (f : G → R) : trivChar ○ f = conjneg f := by
  rw [← conv_conjneg, trivChar_conv]

lemma support_dconv_subset (f g : G → R) : support (f ○ g) ⊆ support f - support g := by
  simpa [sub_eq_add_neg] using support_conv_subset f (conjneg g)

end CommSemiring

section CommRing
variable [CommRing R]

@[simp] lemma conv_neg (f g : G → R) : f ∗ -g = -(f ∗ g) := by ext; simp [conv_apply]
@[simp] lemma neg_conv (f g : G → R) : -f ∗ g = -(f ∗ g) := by ext; simp [conv_apply]

lemma conv_sub (f g h : G → R) : f ∗ (g - h) = f ∗ g - f ∗ h := by
  simp only [sub_eq_add_neg, conv_add, conv_neg]

lemma sub_conv (f g h : G → R) : (f - g) ∗ h = f ∗ h - g ∗ h := by
  simp only [sub_eq_add_neg, add_conv, neg_conv]

variable [StarRing R]

@[simp] lemma dconv_neg (f g : G → R) : f ○ -g = -(f ○ g) := by ext; simp [dconv_apply]
@[simp] lemma neg_dconv (f g : G → R) : -f ○ g = -(f ○ g) := by ext; simp [dconv_apply]

lemma dconv_sub (f g h : G → R) : f ○ (g - h) = f ○ g - f ○ h := by
  simp only [sub_eq_add_neg, dconv_add, dconv_neg]

lemma sub_dconv (f g h : G → R) : (f - g) ○ h = f ○ h - g ○ h := by
  simp only [sub_eq_add_neg, add_dconv, neg_dconv]

end CommRing

namespace RCLike
variable {𝕜 : Type} [RCLike 𝕜] (f g : G → ℝ) (a : G)

@[simp, norm_cast]
lemma coe_conv : (↑((f ∗ g) a) : 𝕜) = ((↑) ∘ f ∗ (↑) ∘ g) a :=
  map_conv (algebraMap ℝ 𝕜) _ _ _

@[simp, norm_cast]
lemma coe_dconv : (↑((f ○ g) a) : 𝕜) = ((↑) ∘ f ○ (↑) ∘ g) a := by simp [dconv_apply]

@[simp] lemma coe_comp_conv : ((↑) : ℝ → 𝕜) ∘ (f ∗ g) = (↑) ∘ f ∗ (↑) ∘ g := funext <| coe_conv _ _

@[simp]
lemma coe_comp_dconv : ((↑) : ℝ → 𝕜) ∘ (f ○ g) = (↑) ∘ f ○ (↑) ∘ g := funext <| coe_dconv _ _

end RCLike

namespace Complex
variable (f g : G → ℝ) (n : ℕ) (a : G)

@[simp, norm_cast]
lemma ofReal_conv : (↑((f ∗ g) a) : ℂ) = ((↑) ∘ f ∗ (↑) ∘ g) a := RCLike.coe_conv _ _ _

@[simp, norm_cast]
lemma ofReal_dconv : (↑((f ○ g) a) : ℂ) = ((↑) ∘ f ○ (↑) ∘ g) a := RCLike.coe_dconv _ _ _

@[simp] lemma ofReal_comp_conv : ((↑) : ℝ → ℂ) ∘ (f ∗ g) = (↑) ∘ f ∗ (↑) ∘ g :=
  funext <| ofReal_conv _ _

@[simp] lemma ofReal_comp_dconv : ((↑) : ℝ → ℂ) ∘ (f ○ g) = (↑) ∘ f ○ (↑) ∘ g :=
  funext <| ofReal_dconv _ _

end Complex

namespace NNReal
variable (f g : G → ℝ≥0) (a : G)

@[simp, norm_cast]
lemma coe_conv : (↑((f ∗ g) a) : ℝ) = ((↑) ∘ f ∗ (↑) ∘ g) a := map_conv NNReal.toRealHom _ _ _

@[simp, norm_cast]
lemma coe_dconv : (↑((f ○ g) a) : ℝ) = ((↑) ∘ f ○ (↑) ∘ g) a := by simp [dconv_apply, coe_sum]

@[simp] lemma coe_comp_conv : ((↑) : _ → ℝ) ∘ (f ∗ g) = (↑) ∘ f ∗ (↑) ∘ g :=
  funext <| coe_conv _ _

@[simp] lemma coe_comp_dconv : ((↑) : _ → ℝ) ∘ (f ○ g) = (↑) ∘ f ○ (↑) ∘ g :=
  funext <| coe_dconv _ _

end NNReal

/-! ### Iterated convolution -/

section CommSemiring
variable [CommSemiring R] {f g : G → R} {n : ℕ}

/-- Iterated convolution. -/
def iterConv (f : G → R) : ℕ → G → R
  | 0 => trivChar
  | n + 1 => iterConv f n ∗ f

infixl:78 " ∗^ " => iterConv

@[simp] lemma iterConv_zero (f : G → R) : f ∗^ 0 = trivChar := rfl
@[simp] lemma iterConv_one (f : G → R) : f ∗^ 1 = f := trivChar_conv _

lemma iterConv_succ (f : G → R) (n : ℕ) : f ∗^ (n + 1) = f ∗^ n ∗ f := rfl
lemma iterConv_succ' (f : G → R) (n : ℕ) : f ∗^ (n + 1) = f ∗ f ∗^ n := conv_comm _ _

lemma iterConv_add (f : G → R) (m : ℕ) : ∀ n, f ∗^ (m + n) = f ∗^ m ∗ f ∗^ n
  | 0 => by simp
  | n + 1 => by simp [← add_assoc, iterConv_succ', iterConv_add, conv_left_comm]

lemma iterConv_mul (f : G → R) (m : ℕ) : ∀ n, f ∗^ (m * n) = f ∗^ m ∗^ n
  | 0 => rfl
  | n + 1 => by simp [mul_add_one, iterConv_succ, iterConv_add, iterConv_mul]

lemma iterConv_mul' (f : G → R) (m n : ℕ) : f ∗^ (m * n) = f ∗^ n ∗^ m := by
  rw [mul_comm, iterConv_mul]

lemma iterConv_conv_distrib (f g : G → R) : ∀ n, (f ∗ g) ∗^ n = f ∗^ n ∗ g ∗^ n
  | 0 => (conv_trivChar _).symm
  | n + 1 => by simp_rw [iterConv_succ, iterConv_conv_distrib, conv_conv_conv_comm]

@[simp] lemma zero_iterConv : ∀ {n}, n ≠ 0 → (0 : G → R) ∗^ n = 0
  | 0, hn => by cases hn rfl
  | n + 1, _ => conv_zero _

@[simp] lemma smul_iterConv [Monoid H] [DistribMulAction H R] [IsScalarTower H R R]
    [SMulCommClass H R R] (c : H) (f : G → R) : ∀ n, (c • f) ∗^ n = c ^ n • f ∗^ n
  | 0 => by simp
  | n + 1 => by simp_rw [iterConv_succ, smul_iterConv _ _ n, pow_succ, mul_smul_conv_comm]

lemma comp_iterConv [CommSemiring S] (m : R →+* S) (f : G → R) :
    ∀ n, m ∘ (f ∗^ n) = m ∘ f ∗^ n
  | 0 => by ext; simp
  | n + 1 => by simp [iterConv_succ, comp_conv, comp_iterConv]

lemma map_iterConv [CommSemiring S] (m : R →+* S) (f : G → R) (a : G) (n : ℕ) :
    m ((f ∗^ n) a) = (m ∘ f ∗^ n) a := congr_fun (comp_iterConv m _ _) _

lemma sum_iterConv (f : G → R) : ∀ n, ∑ a, (f ∗^ n) a = (∑ a, f a) ^ n
  | 0 => by simp [filter_eq']
  | n + 1 => by simp only [iterConv_succ, sum_conv, sum_iterConv, pow_succ]

@[simp] lemma iterConv_trivChar : ∀ n, (trivChar : G → R) ∗^ n = trivChar
  | 0 => rfl
  | _n + 1 => (conv_trivChar _).trans <| iterConv_trivChar _

lemma support_iterConv_subset (f : G → R) : ∀ n, support (f ∗^ n) ⊆ n • support f
  | 0 => by
    simp only [iterConv_zero, zero_smul, support_subset_iff, Ne, ite_eq_right_iff, not_forall,
      exists_prop, Set.mem_zero, and_imp, forall_eq, eq_self_iff_true, imp_true_iff, trivChar_apply]
  | n + 1 =>
    (support_conv_subset _ _).trans <| Set.add_subset_add_right <| support_iterConv_subset _ _

variable [StarRing R]

lemma iterConv_dconv_distrib (f g : G → R) : ∀ n, (f ○ g) ∗^ n = f ∗^ n ○ g ∗^ n
  | 0 => (dconv_trivChar _).symm
  | n + 1 => by simp_rw [iterConv_succ, iterConv_dconv_distrib, conv_dconv_conv_comm]

@[simp] lemma conj_iterConv (f : G → R) : ∀ n, conj (f ∗^ n) = conj f ∗^ n
  | 0 => by ext; simp
  | n + 1 => by simp [iterConv_succ, conj_iterConv]

@[simp] lemma conj_iterConv_apply (f : G → R) (n : ℕ) (a : G) :
    conj ((f ∗^ n) a) = (conj f ∗^ n) a := congr_fun (conj_iterConv _ _) _

lemma IsSelfAdjoint.iterConv (hf : IsSelfAdjoint f) (n : ℕ) : IsSelfAdjoint (f ∗^ n) :=
  (conj_iterConv _ _).trans <| congr_arg (· ∗^ n) hf

@[simp]
lemma conjneg_iterConv (f : G → R) : ∀ n, conjneg (f ∗^ n) = conjneg f ∗^ n
  | 0 => by ext; simp
  | n + 1 => by simp [iterConv_succ, conjneg_iterConv]

end CommSemiring

namespace NNReal

@[simp, norm_cast]
lemma ofReal_iterConv (f : G → ℝ≥0) (n : ℕ) (a : G) : (↑((f ∗^ n) a) : ℝ) = ((↑) ∘ f ∗^ n) a :=
  map_iterConv NNReal.toRealHom _ _ _

end NNReal

namespace Complex

@[simp, norm_cast]
lemma ofReal_iterConv (f : G → ℝ) (n : ℕ) (a : G) : (↑((f ∗^ n) a) : ℂ) = ((↑) ∘ f ∗^ n) a :=
  map_iterConv ofRealHom _ _ _

end Complex
