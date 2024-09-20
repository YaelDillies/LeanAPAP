/-
Copyright (c) 2024 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Finset.Density

/-!
# Average over a finset

This file defines `Finset.expect`, the average (aka expectation) of a function over a finset.

## Notation

* `𝔼 i ∈ s, f i` is notation for `Finset.expect s f`. It is the expectation of `f i` where `i`
  ranges over the finite set `s` (either a `Finset` or a `Set` with a `Fintype` instance).
* `𝔼 i, f i` is notation for `Finset.expect Finset.univ f`. It is the expectation of `f i` where `i`
  ranges over the finite domain of `f`.
* `𝔼 i ∈ s with p i, f i` is notation for `Finset.expect (Finset.filter p s) f`. This is referred to
  as `expectWith` in lemma names.
* `𝔼 (i ∈ s) (j ∈ t), f i j` is notation for `Finset.expect (s ×ˢ t) (fun ⟨i, j⟩ ↦ f i j)`.

## TODO

Connect `Finset.expect` with the expectation over `s` in the probability theory sense.
-/

open Finset Function
open Fintype (card)
open scoped BigOperators Pointwise

variable {ι κ M N : Type*}

namespace Finset
section AddCommMonoid
variable [AddCommMonoid M] [Module ℚ≥0 M] [AddCommMonoid N] [Module ℚ≥0 N] {s t : Finset ι}
  {f g : ι → M} {m : N → M} {p q : ι → Prop} [DecidablePred p] [DecidablePred q]

section DecidableEq
variable [DecidableEq ι]

@[simp] lemma expect_ite_mem (s t : Finset ι) (f : ι → M) :
    𝔼 i ∈ s, (if i ∈ t then f i else 0) = ((s ∩ t).card / s.card : ℚ≥0) • 𝔼 i ∈ s ∩ t, f i := by
  obtain hst | hst := (s ∩ t).eq_empty_or_nonempty
  · simp [expect, hst]
  · simp [expect, smul_smul, ← inv_mul_eq_div, hst.card_ne_zero]

end DecidableEq
end AddCommMonoid

@[simp] lemma expect_apply {α : Type*} {π : α → Type*} [∀ a, CommSemiring (π a)]
    [∀ a, Module ℚ≥0 (π a)] (s : Finset ι) (f : ι → ∀ a, π a) (a : α) :
    (𝔼 i ∈ s, f i) a = 𝔼 i ∈ s, f i a := by simp [expect]

end Finset

namespace Fintype
variable [Fintype ι] [Fintype κ]

section AddCommMonoid
variable [AddCommMonoid M] [Module ℚ≥0 M] {f : ι → M} [DecidableEq ι]

@[simp] lemma expect_ite_mem (s : Finset ι) (f : ι → M) :
    𝔼 i, (if i ∈ s then f i else 0) = s.dens • 𝔼 i ∈ s, f i := by
  simp [Finset.expect_ite_mem, dens]

end AddCommMonoid

section Semiring
variable [Semiring M] [Module ℚ≥0 M]

lemma expect_mul_expect [IsScalarTower ℚ≥0 M M] [SMulCommClass ℚ≥0 M M] (f : ι → M)
    (g : κ → M) : (𝔼 i, f i) * 𝔼 j, g j = 𝔼 i, 𝔼 j, f i * g j :=
  Finset.expect_mul_expect ..

end Semiring
end Fintype
