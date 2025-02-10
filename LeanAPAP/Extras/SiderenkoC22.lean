import LeanAPAP.Prereqs.Expect.Order
import Mathlib.Data.NNReal.Basic

/-!
# Siderenko's conjecture for $$C_{2, 2}$$
-/

open Finset
open scoped BigOperators NNReal

variable {α : Type*} [Fintype α] [Nonempty α]

lemma siderenko_c22 (f : α → α → ℝ) (f_comm : ∀ a b, f a b = f b a) :
    (𝔼 a, 𝔼 b, f a b) ^ 4 ≤ 𝔼 x₁, 𝔼 x₂, 𝔼 x₃, 𝔼 x₄, f x₁ x₂ * f x₂ x₃ * f x₃ x₄ * f x₄ x₁ :=
  calc
    _ ≤ 𝔼 x₁, 𝔼 x₃, (𝔼 x, f x₁ x * f x x₃) ^ 2 * 1 := _
    _ ≤ 𝔼 x₁, (𝔼 x₃, (𝔼 x, f x₁ x * f x x₃) ^ 2) * 𝔼 x₃ : α, 1 ^ 2 := by
      gcongr with x₁
      exact expect_mul_sq_le_sq_mul_sq ..
    _ = 𝔼 x₁, 𝔼 x₃, (𝔼 x, f x₁ x * f x x₃) ^ 2 := by simp
    _ = 𝔼 x₁, 𝔼 x₂, 𝔼 x₃, 𝔼 x₄, f x₁ x₂ * f x₂ x₃ * f x₃ x₄ * f x₄ x₁ := by
      simp_rw [pow_two, Fintype.expect_mul_expect]
      change 𝔼 x₁, 𝔼 x₃, 𝔼 x₂, 𝔼 x₄, _ = _
      congr with x₁
      rw [expect_comm]
      simp [f_comm]
      congr with x₂
      congr with x₃
      congr with x₄
      ring
