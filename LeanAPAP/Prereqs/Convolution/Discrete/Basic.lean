import Mathlib.Algebra.Module.Pi
import Mathlib.Analysis.Complex.Basic
import LeanAPAP.Mathlib.Data.Fintype.Pi
import LeanAPAP.Prereqs.Function.Indicator.Basic
import LeanAPAP.Prereqs.Convolution.Discrete.Defs

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

open Finset Fintype Function
open scoped BigOperators ComplexConjugate NNReal Pointwise

variable {α β γ : Type*} [Fintype α] [DecidableEq α] [AddCommGroup α]

/-!
### Convolution of functions

In this section, we define the convolution `f ∗ g` and difference convolution `f ○ g` of functions
`f g : α → β`, and show how they interact.
-/

section CommSemiring
variable [CommSemiring β] [StarRing β] {f g : α → β}

lemma indicate_conv_indicate_apply (s t : Finset α) (a : α) :
    (𝟭_[β] s ∗ 𝟭 t) a = ((s ×ˢ t).filter fun x : α × α ↦ x.1 + x.2 = a).card := by
  simp only [conv_apply, indicate_apply, ←ite_and, filter_comm, boole_mul, sum_boole]
  simp_rw [←mem_product, filter_univ_mem]

lemma indicate_dconv_indicate_apply (s t : Finset α) (a : α) :
    (𝟭_[β] s ○ 𝟭 t) a = ((s ×ˢ t).filter fun x : α × α ↦ x.1 - x.2 = a).card := by
  simp only [dconv_apply, indicate_apply, ←ite_and, filter_comm, boole_mul, sum_boole,
    apply_ite conj, map_one, map_zero, Pi.conj_apply]
  simp_rw [←mem_product, filter_univ_mem]

lemma indicate_conv (s : Finset α) (f : α → β) : 𝟭 s ∗ f = ∑ a ∈ s, τ a f := by
  ext; simp [conv_eq_sum_sub', indicate_apply]

lemma conv_indicate (f : α → β) (s : Finset α) : f ∗ 𝟭 s = ∑ a ∈ s, τ a f := by
  ext; simp [conv_eq_sum_sub, indicate_apply]

lemma indicate_dconv (s : Finset α) (f : α → β) : 𝟭 s ○ f = ∑ a ∈ s, τ a (conjneg f) := by
  ext; simp [dconv_eq_sum_sub', indicate_apply]

lemma dconv_indicate (f : α → β) (s : Finset α) : f ○ 𝟭 s = ∑ a ∈ s, τ (-a) f := by
  ext; simp [dconv_eq_sum_add, indicate_apply]

end CommSemiring

section Semifield
variable [Semifield β] [CharZero β] [StarRing β]

@[simp] lemma mu_univ_conv_mu_univ : μ_[β] (univ : Finset α) ∗ μ univ = μ univ := by
  ext; cases eq_or_ne (card α : β) 0 <;> simp [mu_apply, conv_eq_sum_add, card_univ, *]

@[simp] lemma mu_univ_dconv_mu_univ : μ_[β] (univ : Finset α) ○ μ univ = μ univ := by
  ext; cases eq_or_ne (card α : β) 0 <;> simp [mu_apply, dconv_eq_sum_add, card_univ, *]

lemma expect_conv (f g : α → β) : 𝔼 a, (f ∗ g) a = (∑ a, f a) * 𝔼 a, g a := by
  simp_rw [expect, sum_conv, mul_smul_comm]

lemma expect_dconv (f g : α → β) : 𝔼 a, (f ○ g) a = (∑ a, f a) * 𝔼 a, conj (g a) := by
  simp_rw [expect, sum_dconv, mul_smul_comm]

lemma expect_conv' (f g : α → β) : 𝔼 a, (f ∗ g) a = (𝔼 a, f a) * ∑ a, g a := by
  simp_rw [expect, sum_conv, smul_mul_assoc]

lemma expect_dconv' (f g : α → β) : 𝔼 a, (f ○ g) a = (𝔼 a, f a) * ∑ a, conj (g a) := by
  simp_rw [expect, sum_dconv, smul_mul_assoc]

lemma mu_conv (s : Finset α) (f : α → β) : μ s ∗ f = (s.card : β)⁻¹ • ∑ a ∈ s, τ a f := by
  simp [mu, indicate_conv, smul_conv]

lemma conv_mu (f : α → β) (s : Finset α) : f ∗ μ s = (s.card : β)⁻¹ • ∑ a ∈ s, τ a f := by
  simp [mu, conv_indicate, conv_smul]

lemma mu_dconv (s : Finset α) (f : α → β) :
    μ s ○ f = (s.card : β)⁻¹ • ∑ a ∈ s, τ a (conjneg f) := by
  simp [mu, indicate_dconv, smul_dconv]

lemma dconv_mu (f : α → β) (s : Finset α) : f ○ μ s = (s.card : β)⁻¹ • ∑ a ∈ s, τ (-a) f := by
  simp [mu, dconv_indicate, dconv_smul]

end Semifield

section Field
variable [Field β] [StarRing β] [CharZero β]

@[simp] lemma balance_conv (f g : α → β) : balance (f ∗ g) = balance f ∗ balance g := by
  simpa [balance, conv_sub, sub_conv, expect_conv]
    using (mul_smul_comm _ _ _).trans (smul_mul_assoc _ _ _).symm

@[simp] lemma balance_dconv (f g : α → β) : balance (f ○ g) = balance f ○ balance g := by
  simpa [balance, dconv_sub, sub_dconv, expect_dconv, map_expect]
    using (mul_smul_comm _ _ _).trans (smul_mul_assoc _ _ _).symm

end Field

/-! ### Iterated convolution -/

section CommSemiring
variable [CommSemiring β] [StarRing β] {f g : α → β} {n : ℕ}

lemma indicate_iterConv_apply (s : Finset α) (n : ℕ) (a : α) :
    (𝟭_[β] s ∗^ n) a = ((s ^^ n).filter fun x : Fin n → α ↦ ∑ i, x i = a).card := by
  induction' n with n ih generalizing a
  · simp [apply_ite card, eq_comm]
  simp_rw [iterConv_succ', conv_eq_sum_sub', ih, indicate_apply, boole_mul, sum_ite,
    filter_univ_mem, sum_const_zero, add_zero, ←Nat.cast_sum, ←Finset.card_sigma]
  congr 1
  refine card_equiv ((Equiv.sigmaEquivProd ..).trans (Equiv.piFinSucc ..).symm) ?_
  aesop (add simp [Fin.sum_cons, Fin.forall_fin_succ])

lemma indicate_iterConv_conv (s : Finset α) (n : ℕ) (f : α → β) :
    𝟭 s ∗^ n ∗ f = ∑ a ∈ s ^^ n, τ (∑ i, a i) f := by
  ext b
  simp only [conv_eq_sum_sub', indicate_iterConv_apply, mem_piFinset, Finset.sum_apply,
    translate_apply, ← nsmul_eq_mul, ← sum_const, Finset.sum_fiberwise']

lemma conv_indicate_iterConv (f : α → β) (s : Finset α) (n : ℕ) :
    f ∗ 𝟭 s ∗^ n = ∑ a ∈ s ^^ n, τ (∑ i, a i) f := by
  ext b
  simp only [conv_eq_sum_sub, indicate_iterConv_apply, mem_piFinset, Finset.sum_apply,
    translate_apply, ← nsmul_eq_mul', ← sum_const, Finset.sum_fiberwise']

lemma indicate_iterConv_dconv (s : Finset α) (n : ℕ) (f : α → β) :
    𝟭 s ∗^ n ○ f = ∑ a ∈ s ^^ n, τ (∑ i, a i) (conjneg f) := by
  rw [← conv_conjneg, indicate_iterConv_conv]

lemma dconv_indicate_iterConv (f : α → β) (s : Finset α) (n : ℕ) :
    f ○ 𝟭 s ∗^ n = ∑ a ∈ s ^^ n, τ (-∑ i, a i) f := by
  simp [← conv_conjneg, conjneg_iterConv, conv_indicate_iterConv, piFinset_neg]

end CommSemiring

section Semifield
variable [Semifield β] [CharZero β] [Module ℚ≥0 β] [StarRing β]

lemma mu_iterConv_conv (s : Finset α) (n : ℕ) (f : α → β) :
    μ s ∗^ n ∗ f = 𝔼 a ∈ piFinset (fun _ : Fin n ↦ s), τ (∑ i, a i) f := by
  simp only [mu, smul_iterConv, inv_pow, smul_conv, indicate_iterConv_conv, expect,
    card_piFinsetConst, Nat.cast_pow]
  rw [← nnratCast_smul_eq_nnqsmul β]
  push_cast
  rfl

lemma conv_mu_iterConv (f : α → β) (s : Finset α) (n : ℕ) :
    f ∗ μ s ∗^ n = 𝔼 a ∈ piFinset (fun _ : Fin n ↦ s), τ (∑ i, a i) f := by
  rw [conv_comm, mu_iterConv_conv]

lemma mu_iterConv_dconv (s : Finset α) (n : ℕ) (f : α → β) :
    μ s ∗^ n ○ f = 𝔼 a ∈ piFinset (fun _ : Fin n ↦ s), τ (∑ i, a i) (conjneg f) := by
  rw [← conv_conjneg, mu_iterConv_conv]

lemma dconv_mu_iterConv (f : α → β) (s : Finset α) (n : ℕ) :
    f ○ μ s ∗^ n = 𝔼 a ∈ piFinset (fun _ : Fin n ↦ s), τ (-∑ i, a i) f := by
  simp_rw [← conv_conjneg, conjneg_iterConv, conjneg_mu, conv_mu_iterConv, piFinset_neg,
    expect_neg_index, Pi.neg_apply, sum_neg_distrib]

end Semifield

section Field
variable [Field β] [StarRing β] [CharZero β]

@[simp] lemma balance_iterConv (f : α → β) : ∀ {n}, n ≠ 0 → balance (f ∗^ n) = balance f ∗^ n
  | 0, h => by cases h rfl
  | 1, _ => by simp
  | n + 2, _ => by simp [iterConv_succ _ (n + 1), balance_iterConv _ n.succ_ne_zero]

end Field
