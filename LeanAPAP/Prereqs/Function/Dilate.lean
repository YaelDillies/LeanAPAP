import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Data.ZMod.Basic

/-!
# Dilation operator
-/

variable {G 𝕜 : Type*} [AddCommGroup G]

noncomputable def dilate (f : G → 𝕜) (n : ℕ) : G → 𝕜 :=
  fun a ↦ f ((n⁻¹ : ZMod (Nat.card G)).val • a)

variable [Star 𝕜] {f : G → 𝕜}

protected lemma IsSelfAdjoint.dilate (hf : IsSelfAdjoint f) (n : ℕ) : IsSelfAdjoint (dilate f n) :=
  Pi.isSelfAdjoint.2 fun _g ↦ hf.apply _
