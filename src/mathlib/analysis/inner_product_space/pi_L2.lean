import analysis.inner_product_space.pi_L2

open_locale big_operators

variables {𝕜 ι : Type*} [add_comm_monoid 𝕜] [fintype ι] {α : ι → Type*} [Π i, has_inner 𝕜 (α i)]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

instance pi_Lp.inner_product_space' : has_inner 𝕜 (pi_Lp 2 α) :=
⟨λ x y, ∑ i, inner (x i) (y i)⟩

@[simp] lemma pi_Lp.inner_apply' (x y : pi_Lp 2 α) : ⟪x, y⟫ = ∑ i, ⟪x i, y i⟫ := rfl
