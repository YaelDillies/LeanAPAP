import LeanAPAP.Mathlib.Data.ZMod.Basic

variable {S G : Type*} [AddCommGroup G] {N : ℕ} [Module (ZMod N) G] [SetLike S G]
  [AddSubgroupClass S G] {K : S} {x : G}

lemma zmod_smul_mem (hx : x ∈ K) : ∀ n : ZMod N, n • x ∈ K := by
  simpa [ZMod.forall, Int.cast_smul_eq_zsmul] using zsmul_mem hx

namespace AddSubgroupClass

instance instZModSMul : SMul (ZMod N) K where
  smul n x := ⟨n • x, zmod_smul_mem x.2 _⟩

@[simp, norm_cast] lemma coe_zmod_smul (n : ZMod N) (x : K) : ↑(n • x) = (n • x : G) := rfl

instance instZModModule : Module (ZMod N) K :=
  Subtype.coe_injective.module _ (AddSubmonoidClass.subtype K) coe_zmod_smul

end AddSubgroupClass
