import LeanAPAP.Prereqs.AddChar.Basic

open AddChar Complex Function
open scoped NNReal

/-- A *Bohr set* `B` on an additive group `G` is a set of characters of `G`, called the *frequencies*, along with a real number for each frequency `ψ`, called the *width of `B` at `ψ`*.

A Bohr set `B` is thought of as the set `{x | ∀ ψ ∈ B.frequencies, ‖1 - ψ x‖ ≤ B.width ψ}`. This is
the *chord-length* convention. The arc-length convention would instead be
`{x | ∀ ψ ∈ B.frequencies, |arg (ψ x)| ≤ B.width ψ}`.

Note that this set **does not** uniquely determine `B` (in particular, it does not uniquely
determine either `B.frequencies` or `B.width`). -/
@[ext]
structure BohrSet (G : Type*) [AddCommGroup G] where
  /-- The set of frequencies of a Bohr set. -/
  frequencies : Finset (AddChar G ℂ)
  /-- The width of a Bohr set at a frequency. Note that this width corresponds to chord-length. -/
  width : frequencies → ℝ≥0

namespace BohrSet
variable {G : Type*} [AddCommGroup G] [Finite G] {B : BohrSet G} {x : G}

/-! ### Coercion, membership -/

instance instMem : Membership G (BohrSet G) := ⟨fun x B ↦ ∀ ψ, ‖1 - ψ.1 x‖ ≤ B.width ψ⟩

/-- The set corresponding to a Bohr set `B` is `{x | ∀ ψ ∈ B.frequencies, ‖1 - ψ x‖ ≤ B.width ψ}`.
This is the *chord-length* convention. The arc-length convention would instead be
`{x | ∀ ψ ∈ B.frequencies, |arg (ψ x)| ≤ B.width ψ}`.

Note that this set **does not** uniquely determine `B`. -/
@[coe] def toSet (B : BohrSet G) : Set G := {x | ∀ ψ, ‖1 - ψ.1 x‖ ≤ B.width ψ}

/-- Given the Bohr set `B`, `B.Elem` is the `Type` of elements of `B`. -/
@[coe, reducible] def Elem (B : BohrSet G) : Type _ := {x // x ∈ B}

instance instCoe : Coe (BohrSet G) (Set G) := ⟨toSet⟩
instance instCoeSort : CoeSort (BohrSet G) (Type _) := ⟨Elem⟩

lemma coe_def (B : BohrSet G) : B = {x | ∀ ψ, ‖1 - ψ.1 x‖ ≤ B.width ψ} := rfl
lemma mem_def : x ∈ B ↔ ∀ ψ, ‖1 - ψ.1 x‖ ≤ B.width ψ := Iff.rfl

@[simp, norm_cast] lemma mem_coe : x ∈ (B : Set G) ↔ x ∈ B := Iff.rfl
@[simp, norm_cast] lemma coeSort_coe (B : BohrSet G) : ↥(B : Set G) = B := rfl

@[simp] lemma zero_mem : 0 ∈ B := by simp [mem_def]
@[simp] lemma neg_mem : -x ∈ B ↔ x ∈ B :=
  forall_congr' fun ψ ↦ by rw [Iff.comm, ← RCLike.norm_conj, map_sub, map_one, map_neg_eq_conj]

/-! ### Width, frequencies, rank -/

attribute [pp_dot] frequencies width

/-- The rank of a Bohr set is the number of characters which have width strictly less than `2`. -/
@[pp_dot] def rank (B : BohrSet G) : ℕ := B.frequencies.card

lemma card_frequencies (B : BohrSet G) : B.frequencies.card = B.rank := rfl

/-! ### Dilation -/

section smul
variable {ρ : ℝ}

noncomputable instance instSMul : SMul ℝ (BohrSet G) where
  smul ρ B := ⟨B.frequencies, fun ψ ↦ Real.nnabs ρ • B.width ψ⟩

lemma smul_def (ρ : ℝ) (B : BohrSet G) :
    ρ • B = ⟨B.frequencies, fun ψ ↦ Real.nnabs ρ • B.width ψ⟩ := rfl

@[simp] lemma frequencies_smul (ρ : ℝ) (B : BohrSet G) : (ρ • B).frequencies = B.frequencies := rfl
@[simp] lemma rank_smul (ρ : ℝ) (B : BohrSet G) : (ρ • B).rank = B.rank := rfl

@[simp] lemma width_smul (ρ : ℝ) (B : BohrSet G) (ψ : B.frequencies) :
    (ρ • B).width ψ = Real.nnabs ρ • B.width ψ := rfl

noncomputable instance instMulAction : MulAction ℝ (BohrSet G) where
  one_smul B := by simp [smul_def]
  mul_smul ρ φ B := by simp [smul_def, mul_smul, mul_assoc]

end smul

variable {ρ : ℝ}

lemma le_card_smul (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) :
    (ρ / 4) ^ B.rank * Nat.card B ≤ Nat.card ↥(ρ • B) := by
  sorry

end BohrSet
