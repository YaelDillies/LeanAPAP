import LeanAPAP.Prereqs.AddChar.Basic

open AddChar Complex Function
open scoped NNReal

/-- A *Bohr set* `B` on an additive group `G` is the data of a real number for each character `ψ` of
`G`, called the *width of `B` at `ψ`*.

A Bohr set `B` is thought of as the set `{x | ∀ ψ, ‖1 - ψ x‖ ≤ B.width ψ}`. Note that this set
**does not** uniquely determine `B`. -/
structure BohrSet (G : Type*) [AddCommGroup G] where
  /-- The width of a Bohr set at a character. -/
  width : AddChar G ℂ → ℝ≥0

namespace BohrSet
variable {G : Type*} [AddCommGroup G] [Finite G] {B : BohrSet G} {x : G}

/-! ### Coercion, membership -/

instance instMem : Membership G (BohrSet G) := ⟨fun x B ↦ ∀ ψ, ‖1 - ψ x‖ ≤ B.width ψ⟩

/-- The set corresponding to a Bohr set `B` is `{x | ∀ ψ, ‖1 - ψ x‖ ≤ B.width ψ}`. Note that this
set **does not** uniquely determine `B`. -/
@[coe] def toSet (B : BohrSet G) : Set G := {x | ∀ ψ, ‖1 - ψ x‖ ≤ B.width ψ}

/-- Given the Bohr set `B`, `B.Elem` is the `Type` of elements of `B`. -/
@[coe, reducible] def Elem (B : BohrSet G) : Type _ := {x // x ∈ B}

instance instCoe : Coe (BohrSet G) (Set G) := ⟨toSet⟩
instance instCoeSort : CoeSort (BohrSet G) (Type _) := ⟨Elem⟩

lemma coe_def (B : BohrSet G) : B = {x | ∀ ψ, ‖1 - ψ x‖ ≤ B.width ψ} := rfl
lemma mem_def : x ∈ B ↔ ∀ ψ, ‖1 - ψ x‖ ≤ B.width ψ := Iff.rfl

@[simp, norm_cast] lemma mem_coe : x ∈ (B : Set G) ↔ x ∈ B := Iff.rfl
@[simp, norm_cast] lemma coeSort_coe (B : BohrSet G) : ↥(B : Set G) = B := rfl

@[simp] lemma zero_mem : 0 ∈ B := by simp [mem_def]
@[simp] lemma neg_mem : -x ∈ B ↔ x ∈ B :=
  forall_congr' fun ψ ↦ by rw [Iff.comm, ← IsROrC.norm_conj, map_sub, map_one, map_neg_eq_conj]

/-! ### Width, frequencies, rank -/

attribute [pp_dot] width

@[ext] lemma width_injective : Injective (width : BohrSet G → AddChar G ℂ → ℝ≥0) :=
  fun B₁ B₂ h ↦ by cases B₁; cases B₂; congr

/-- The rank of a Bohr set is the number of characters which have width strictly less than `2`. -/
@[pp_dot] noncomputable def rank (B : BohrSet G) : ℕ := Nat.card {ψ | B.width ψ < 2}

/-! ### Dilation -/

section smul
variable {ρ : ℝ}

noncomputable instance instSMul : SMul ℝ (BohrSet G) where
  smul ρ B := ⟨fun ψ ↦ Real.nnabs ρ • B.width ψ⟩

lemma smul_def (ρ : ℝ) (B : BohrSet G) : ρ • B = ⟨fun ψ ↦ Real.nnabs ρ • B.width ψ⟩ := rfl

@[simp] lemma width_smul (ρ : ℝ) (B : BohrSet G) (ψ : AddChar G ℂ) :
  (ρ • B).width ψ = Real.nnabs ρ • B.width ψ := rfl

noncomputable instance instMulAction : MulAction ℝ (BohrSet G) where
  one_smul B := by simp [smul_def]
  mul_smul ρ φ B := by ext ψ; simp [smul_def, mul_smul, mul_assoc]

lemma le_rank_smul (hρ : |ρ| ≤ 1) : B.rank ≤ (ρ • B).rank :=
  Nat.card_mono (Set.toFinite _) fun ψ ↦ by
    simpa using (mul_le_of_le_one_left (zero_le _) hρ).trans_lt

end smul

variable {ρ : ℝ}

lemma le_card_smul (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) :
    (ρ / 4) ^ B.rank * Nat.card B ≤ Nat.card ↥(ρ • B) := by
  sorry

end BohrSet
