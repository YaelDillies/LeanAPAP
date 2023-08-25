import Mathbin.Analysis.InnerProductSpace.PiL2

#align_import mathlib.analysis.inner_product_space.pi_L2

open scoped BigOperators

variable {𝕜 ι : Type _} [AddCommMonoid 𝕜] [Fintype ι] {α : ι → Type _} [∀ i, Inner 𝕜 (α i)]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

instance PiLp.innerProductSpace' : Inner 𝕜 (PiLp 2 α) :=
  ⟨fun x y => ∑ i, inner (x i) (y i)⟩

@[simp]
theorem PiLp.inner_apply' (x y : PiLp 2 α) : ⟪x, y⟫ = ∑ i, ⟪x i, y i⟫ :=
  rfl

