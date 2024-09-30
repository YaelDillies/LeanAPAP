import Mathlib.Algebra.BigOperators.Expect

/-!
# Balancing a function
-/

open Function
open Fintype (card)
open scoped BigOperators Pointwise NNRat

variable {ι α β : Type*}

namespace Finset

section AddCommGroup
variable [AddCommGroup α] [Module ℚ≥0 α] [Field β] [Module ℚ≥0 β] {s : Finset ι}

variable [Fintype ι]

def balance (f : ι → α) : ι → α := f - Function.const _ (𝔼 y, f y)

lemma balance_apply (f : ι → α) (x : ι) : balance f x = f x - 𝔼 y, f y := rfl

@[simp] lemma balance_zero : balance (0 : ι → α) = 0 := by simp [balance]

@[simp] lemma balance_add (f g : ι → α) : balance (f + g) = balance f + balance g := by
  simp only [balance, expect_add_distrib, ← const_add, add_sub_add_comm, Pi.add_apply]

@[simp] lemma balance_sub (f g : ι → α) : balance (f - g) = balance f - balance g := by
  simp only [balance, expect_sub_distrib, const_sub, sub_sub_sub_comm, Pi.sub_apply]

@[simp] lemma balance_neg (f : ι → α) : balance (-f) = -balance f := by
  simp only [balance, expect_neg_distrib, const_neg, neg_sub', Pi.neg_apply]

@[simp] lemma sum_balance (f : ι → α) : ∑ x, balance f x = 0 := by
  cases isEmpty_or_nonempty ι <;> simp [balance_apply]

@[simp] lemma expect_balance (f : ι → α) : 𝔼 x, balance f x = 0 := by simp [expect]

@[simp] lemma balance_idem (f : ι → α) : balance (balance f) = balance f := by
  cases isEmpty_or_nonempty ι <;> ext x <;> simp [balance, expect_sub_distrib]

@[simp] lemma map_balance {F : Type*} [FunLike F α β] [LinearMapClass F ℚ≥0 α β] (g : F) (f : ι → α)
    (a : ι) : g (balance f a) = balance (g ∘ f) a := by simp [balance, map_expect]

end AddCommGroup
