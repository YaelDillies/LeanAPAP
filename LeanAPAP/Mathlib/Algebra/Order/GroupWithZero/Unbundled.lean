import Mathlib.Algebra.Order.GroupWithZero.Unbundled

@[bound] alias ⟨_, Bound.one_le_inv₀⟩ := one_le_inv₀

attribute [bound] mul_le_one₀

@[bound]
protected lemma Bound.one_lt_mul {M₀ : Type*} [MonoidWithZero M₀] [Preorder M₀] [ZeroLEOneClass M₀]
    [PosMulMono M₀] [MulPosMono M₀] {a b : M₀} : 1 ≤ a ∧ 1 < b ∨ 1 < a ∧ 1 ≤ b → 1 < a * b := by
  rintro (⟨ha, hb⟩ | ⟨ha, hb⟩); exacts [one_lt_mul ha hb, one_lt_mul_of_lt_of_le ha hb]
