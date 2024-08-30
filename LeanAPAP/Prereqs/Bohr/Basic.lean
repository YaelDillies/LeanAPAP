<<<<<<< HEAD
import Mathlib.Analysis.Complex.Basic
import LeanAPAP.Prereqs.AddChar.PontryaginDuality

open AddChar Function
open scoped NNReal ENNReal
=======
import LeanAPAP.Mathlib.Analysis.Normed.Field.Basic
import LeanAPAP.Mathlib.Data.ENNReal.Operations
import LeanAPAP.Mathlib.Order.ConditionallyCompleteLattice.Basic
import LeanAPAP.Prereqs.AddChar.PontryaginDuality

open AddChar Function
open scoped NNReal ENNReal Pointwise
>>>>>>> c88269882e68b9316c3a26cc19a33bee405c07c3

/-- A *Bohr set* `B` on an additive group `G` is a finite set of characters of `G`, called the
*frequencies*, along with an extended non-negative real number for each frequency `ψ`, called the
*width of `B` at `ψ`*.

A Bohr set `B` is thought of as the set `{x | ∀ ψ ∈ B.frequencies, ‖1 - ψ x‖ ≤ B.width ψ}`. This is
the *chord-length* convention. The arc-length convention would instead be
`{x | ∀ ψ ∈ B.frequencies, |arg (ψ x)| ≤ B.width ψ}`.

Note that this set **does not** uniquely determine `B` (in particular, it does not uniquely
determine either `B.frequencies` or `B.width`). -/
@[ext]
structure BohrSet (G : Type*) [AddCommGroup G] where
  frequencies : Finset (AddChar G ℂ)
  /-- The width of a Bohr set at a frequency.

  Note that this width corresponds to chord-length under `BohrSet.toSet`, which is registered as the
  coercion `BohrSet G → Set G`. For arc-length, use `BohrSet.arcSet` instead. -/
  ewidth : AddChar G ℂ → ℝ≥0∞
  mem_frequencies : ∀ ψ, ψ ∈ frequencies ↔ ewidth ψ < ⊤

namespace BohrSet
variable {G : Type*} [AddCommGroup G] {B B₁ B₂ : BohrSet G} {ψ : AddChar G ℂ} {x : G}

  /-- The width of a Bohr set at a frequency. Note that this width corresponds to chord-length. -/
def width (B : BohrSet G) (ψ : AddChar G ℂ) : ℝ≥0 := (B.ewidth ψ).toNNReal

lemma width_def : B.width ψ = (B.ewidth ψ).toNNReal := rfl

lemma coe_width (hψ : ψ ∈ B.frequencies) : B.width ψ = B.ewidth ψ :=
  ENNReal.coe_toNNReal <| by rwa [← lt_top_iff_ne_top, ← B.mem_frequencies]

lemma ewidth_eq_top_iff : ψ ∉ B.frequencies ↔ B.ewidth ψ = ⊤ := by
  simp [B.mem_frequencies]

alias ⟨ewidth_eq_top_of_not_mem_frequencies, _⟩ := ewidth_eq_top_iff

lemma width_eq_zero_of_not_mem_frequencies (hψ : ψ ∉ B.frequencies) : B.width ψ = 0 := by
  rw [width_def, ewidth_eq_top_of_not_mem_frequencies hψ, ENNReal.top_toNNReal]

lemma ewidth_injective : Injective (BohrSet.ewidth (G := G)) :=
  fun B₁ B₂ h ↦ by ext <;> simp [B₁.mem_frequencies, B₂.mem_frequencies, h]

/-- Construct a Bohr set on a finite group given an extended width function. -/
noncomputable def ofEWidth [Finite G] (ewidth : AddChar G ℂ → ℝ≥0∞) : BohrSet G where
  frequencies := {ψ | ewidth ψ < ⊤}
  ewidth := ewidth
  mem_frequencies := fun ψ => by simp

/-- Construct a Bohr set on a finite group given a width function and a frequency set. -/
noncomputable def ofWidth (width : AddChar G ℂ → ℝ≥0) (freq : Finset (AddChar G ℂ)) :
    BohrSet G where
  frequencies := freq
  ewidth ψ := if ψ ∈ freq then width ψ else ⊤
  mem_frequencies := fun ψ => by simp [lt_top_iff_ne_top]

@[ext]
lemma ext_width {B B' : BohrSet G} (freq : B.frequencies = B'.frequencies)
    (width : ∀ ψ : AddChar G ℂ, ψ ∈ B.frequencies → B.width ψ = B'.width ψ) :
    B = B' := by
  ext
  case frequencies => rw [freq]
  case ewidth ψ =>
    by_cases hψ : ψ ∈ B.frequencies
    case pos =>
      rw [←coe_width hψ, width _ hψ, coe_width]
      rwa [←freq]
    case neg =>
      rw [ewidth_eq_top_of_not_mem_frequencies hψ, ewidth_eq_top_of_not_mem_frequencies]
      rwa [←freq]

/-! ### Coercion, membership -/

instance instMem : Membership G (BohrSet G) where
  mem x B := ∀ ⦃ψ⦄, ψ ∈ B.frequencies → ‖1 - ψ x‖₊ ≤ B.width ψ

/-- The set corresponding to a Bohr set `B` is `{x | ∀ ψ ∈ B.frequencies, ‖1 - ψ x‖ ≤ B.width ψ}`.
This is the *chord-length* convention. The arc-length convention would instead be
`{x | ∀ ψ ∈ B.frequencies, |arg (ψ x)| ≤ B.width ψ}`.

Note that this set **does not** uniquely determine `B`. -/
@[coe] def toSet (B : BohrSet G) : Set G := {x | x ∈ B}

/-- Given the Bohr set `B`, `B.Elem` is the `Type` of elements of `B`. -/
@[coe, reducible] def Elem (B : BohrSet G) : Type _ := {x // x ∈ B}

instance instCoe : Coe (BohrSet G) (Set G) := ⟨toSet⟩
instance instCoeSort : CoeSort (BohrSet G) (Type _) := ⟨Elem⟩

lemma coe_def (B : BohrSet G) : B = {x | ∀ ⦃ψ⦄, ψ ∈ B.frequencies → ‖1 - ψ x‖₊ ≤ B.width ψ} := rfl
lemma mem_iff_nnnorm_width : x ∈ B ↔ ∀ ⦃ψ⦄, ψ ∈ B.frequencies → ‖1 - ψ x‖₊ ≤ B.width ψ := Iff.rfl
lemma mem_iff_norm_width : x ∈ B ↔ ∀ ⦃ψ⦄, ψ ∈ B.frequencies → ‖1 - ψ x‖ ≤ B.width ψ := Iff.rfl

@[simp, norm_cast] lemma mem_coe : x ∈ (B : Set G) ↔ x ∈ B := Iff.rfl
@[simp, norm_cast] lemma coeSort_coe (B : BohrSet G) : ↥(B : Set G) = B := rfl

@[simp] lemma zero_mem : 0 ∈ B := by simp [mem_iff_nnnorm_width]
@[simp] lemma neg_mem [Finite G] : -x ∈ B ↔ x ∈ B :=
  forall₂_congr fun ψ hψ ↦ by sorry
    -- rw [Iff.comm, ← RCLike.nnnorm_conj, map_sub, map_one, map_neg_eq_conj]

/-! ### Lattice structure -/

noncomputable instance : Sup (BohrSet G) where
  sup B₁ B₂ :=
    { frequencies := B₁.frequencies ∩ B₂.frequencies,
      ewidth := fun ψ => B₁.ewidth ψ ⊔ B₂.ewidth ψ,
      mem_frequencies := fun ψ => by simp [mem_frequencies] }

noncomputable instance : Inf (BohrSet G) where
  inf B₁ B₂ :=
    { frequencies := B₁.frequencies ∪ B₂.frequencies,
      ewidth := fun ψ => B₁.ewidth ψ ⊓ B₂.ewidth ψ,
      mem_frequencies := fun ψ => by simp [mem_frequencies] }

noncomputable instance [Finite G] : Bot (BohrSet G) where
  bot.frequencies := ⊤
  bot.ewidth := 0
  bot.mem_frequencies := by simp

noncomputable instance : Top (BohrSet G) where
  top.frequencies := ⊥
  top.ewidth := ⊤
  top.mem_frequencies := by simp

@[simp] lemma frequencies_top : (⊤ : BohrSet G).frequencies = ∅ := rfl
@[simp] lemma frequencies_bot [Finite G] : (⊥ : BohrSet G).frequencies = .univ := rfl

@[simp] lemma frequencies_sup (B₁ B₂ : BohrSet G) :
    (B₁ ⊔ B₂).frequencies = B₁.frequencies ∩ B₂.frequencies := rfl

@[simp] lemma frequencies_inf (B₁ B₂ : BohrSet G) :
    (B₁ ⊓ B₂).frequencies = B₁.frequencies ∪ B₂.frequencies := rfl

@[simp] lemma ewidth_top_apply (ψ : AddChar G ℂ) : (⊤ : BohrSet G).ewidth ψ = ∞ := rfl
@[simp] lemma ewidth_bot_apply [Finite G] (ψ : AddChar G ℂ) : (⊥ : BohrSet G).ewidth ψ = 0 := rfl
@[simp] lemma ewidth_sup_apply (B₁ B₂ : BohrSet G) (ψ : AddChar G ℂ) :
    (B₁ ⊔ B₂).ewidth ψ = B₁.ewidth ψ ⊔ B₂.ewidth ψ := rfl
@[simp] lemma ewidth_inf_apply (B₁ B₂ : BohrSet G) (ψ : AddChar G ℂ) :
    (B₁ ⊓ B₂).ewidth ψ = B₁.ewidth ψ ⊓ B₂.ewidth ψ := rfl

@[simp] lemma width_top_apply (ψ : AddChar G ℂ) : (⊤ : BohrSet G).width ψ = 0 := rfl
@[simp] lemma width_bot_apply [Finite G] (ψ : AddChar G ℂ) : (⊥ : BohrSet G).width ψ = 0 := rfl
@[simp] lemma width_sup_apply (h₁ : ψ ∈ B₁.frequencies) (h₂ : B₂.frequencies) :
    (B₁ ⊔ B₂).width ψ = B₁.width ψ ⊔ B₂.width ψ := sorry
@[simp] lemma width_inf_apply (h₁ : ψ ∈ B₁.frequencies) (h₂ : B₂.frequencies) :
    (B₁ ⊓ B₂).width ψ = B₁.width ψ ⊓ B₂.width ψ := sorry

lemma ewidth_top : (⊤ : BohrSet G).ewidth = ⊤ := rfl
lemma ewidth_bot [Finite G] : (⊥ : BohrSet G).ewidth = 0 := rfl
lemma ewidth_sup (B₁ B₂ : BohrSet G) : (B₁ ⊔ B₂).ewidth = B₁.ewidth ⊔ B₂.ewidth := rfl
lemma ewidth_inf (B₁ B₂ : BohrSet G) : (B₁ ⊓ B₂).ewidth = B₁.ewidth ⊓ B₂.ewidth := rfl

lemma width_top : (⊤ : BohrSet G).width = 0 := rfl
lemma width_bot [Finite G] : (⊥ : BohrSet G).width = 0 := rfl
lemma width_sup (h₁ : ψ ∈ B₁.frequencies) (h₂ : B₂.frequencies) :
    (B₁ ⊔ B₂).width = B₁.width ⊔ B₂.width := sorry
lemma width_inf (h₁ : ψ ∈ B₁.frequencies) (h₂ : B₂.frequencies) :
    (B₁ ⊓ B₂).width = B₁.width ⊓ B₂.width := sorry

noncomputable instance : DistribLattice (BohrSet G) :=
  ewidth_injective.distribLattice BohrSet.ewidth ewidth_sup ewidth_inf

noncomputable instance : OrderTop (BohrSet G) := OrderTop.lift BohrSet.ewidth (fun _ _ h ↦ h) rfl

lemma le_iff_ewidth : B₁ ≤ B₂ ↔ ∀ ⦃ψ⦄, B₁.ewidth ψ ≤ B₂.ewidth ψ := Iff.rfl

@[gcongr] lemma frequencies_anti (h : B₁ ≤ B₂) : B₂.frequencies ⊆ B₁.frequencies :=
  fun ψ ↦ by simpa only [mem_frequencies] using (h ψ).trans_lt

lemma frequencies_antitone : Antitone (frequencies : BohrSet G → _) := fun _ _ ↦ frequencies_anti

lemma le_iff_width :
    B₁ ≤ B₂ ↔
      B₂.frequencies ⊆ B₁.frequencies ∧ ∀ ⦃ψ⦄, ψ ∈ B₂.frequencies → B₁.width ψ ≤ B₂.width ψ := by
  constructor
  case mp =>
    intro h
    refine ⟨frequencies_anti h, fun ψ hψ => ?_⟩
    rw [←ENNReal.coe_le_coe, coe_width hψ, coe_width (frequencies_anti h hψ)]
    exact h ψ
  case mpr =>
    rintro ⟨h₁, h₂⟩ ψ
    by_cases ψ ∈ B₂.frequencies
    case neg h' => simp [ewidth_eq_top_of_not_mem_frequencies h']
    case pos h' =>
      rw [←coe_width h', ←coe_width (h₁ h'), ENNReal.coe_le_coe]
      exact h₂ h'

@[gcongr] lemma ewidth_mono (h : B₁ ≤ B₂) : B₁.ewidth ψ ≤ B₂.ewidth ψ := h ψ

@[gcongr]
lemma width_mono (h : B₁ ≤ B₂) (hψ : ψ ∈ B₂.frequencies) : B₁.width ψ ≤ B₂.width ψ :=
  (le_iff_width.1 h).2 hψ

open scoped Classical in
noncomputable instance [Finite G] : SupSet (BohrSet G) where
  sSup B :=
    { frequencies := {ψ | ⨆ i ∈ B, i.ewidth ψ < ⊤},
      ewidth := fun ψ => ⨆ i ∈ B, ewidth i ψ
      mem_frequencies := fun ψ => by simp [mem_frequencies] }

open scoped Classical in
noncomputable instance [Finite G] : InfSet (BohrSet G) where
  sInf B :=
    { frequencies := {ψ | ∃ i ∈ B, i.ewidth ψ < ⊤},
      ewidth := fun ψ => ⨅ i ∈ B, ewidth i ψ
      mem_frequencies := by simp [iInf_lt_top] }

noncomputable def minimalAxioms [Finite G] : CompletelyDistribLattice.MinimalAxioms (BohrSet G) :=
  ewidth_injective.completelyDistribLatticeMinimalAxioms .of BohrSet.ewidth ewidth_sup ewidth_inf
    (fun B => by ext ψ; simp only [iSup_apply]; rfl)
    (fun B => by ext ψ; simp only [iInf_apply]; rfl)
    rfl
    rfl

noncomputable instance [Finite G] : CompletelyDistribLattice (BohrSet G) :=
  .ofMinimalAxioms BohrSet.minimalAxioms

/-! ### Width, frequencies, rank -/

/-- The rank of a Bohr set is the number of characters which have finite width. -/
def rank (B : BohrSet G) : ℕ := B.frequencies.card

@[simp] lemma card_frequencies (B : BohrSet G) : B.frequencies.card = B.rank := rfl

/-! ### Dilation -/

section smul
variable {ρ : ℝ}

noncomputable instance instSMul : SMul ℝ (BohrSet G) where
  smul ρ B := BohrSet.mk B.frequencies
      (fun ψ => if ψ ∈ B.frequencies then Real.nnabs ρ * B.width ψ else ⊤) fun ψ => by
        simp [lt_top_iff_ne_top, ←ENNReal.coe_mul]

@[simp] lemma frequencies_smul (ρ : ℝ) (B : BohrSet G) : (ρ • B).frequencies = B.frequencies := rfl
@[simp] lemma rank_smul (ρ : ℝ) (B : BohrSet G) : (ρ • B).rank = B.rank := rfl

@[simp] lemma ewidth_smul (ρ : ℝ) (B : BohrSet G) (ψ) :
    (ρ • B).ewidth ψ = if ψ ∈ B.frequencies then (Real.nnabs ρ * B.width ψ : ℝ≥0∞) else ⊤ :=
  rfl

@[simp] lemma width_smul_apply (ρ : ℝ) (B : BohrSet G) (ψ) :
    (ρ • B).width ψ = Real.nnabs ρ * B.width ψ := by
  rw [width_def, ewidth_smul]
  split
  case isTrue h => simp
  case isFalse h => simp [width_eq_zero_of_not_mem_frequencies h]

lemma width_smul (ρ : ℝ) (B : BohrSet G) : (ρ • B).width = Real.nnabs ρ • B.width := by
  ext ψ; simp [width_smul_apply]

noncomputable instance instMulAction : MulAction ℝ (BohrSet G) where
  one_smul B := by ext <;> simp
  mul_smul ρ φ B := by ext <;> simp [mul_assoc]

end smul

-- Note it is not sufficient to say B.width = 0.
lemma eq_zero_of_ewidth_eq_zero {B : BohrSet G} [Finite G] (h : B.ewidth = 0) :
    (B : Set G) = {0} := by
  rw [Set.eq_singleton_iff_unique_mem]
  simp only [mem_coe, zero_mem, true_and, mem_iff_nnnorm_width, map_zero_eq_one, sub_self,
    norm_zero, true_and, NNReal.zero_le_coe, implies_true, nnnorm_zero, zero_le]
  intro x hx
  by_contra!
  rw [←AddChar.exists_apply_ne_zero] at this
  obtain ⟨ψ, hψ⟩ := this
  apply hψ
  have hψ' : ψ ∈ B.frequencies := by simp [B.mem_frequencies, h]
  specialize hx hψ'
  rwa [B.width_def, h, Pi.zero_apply, ENNReal.zero_toNNReal, nonpos_iff_eq_zero, nnnorm_eq_zero,
    sub_eq_zero, eq_comm] at hx

@[simp] lemma AddChar.nnnorm_apply {α G : Type*}
    [NormedDivisionRing α] [AddLeftCancelMonoid G] [Finite G] (ψ : AddChar G α)
    (x : G) : ‖ψ x‖₊ = 1 :=
  NNReal.coe_injective (by simp)

lemma eq_top_of_two_le_width {B : BohrSet G} [Finite G] (h : ∀ ψ, 2 ≤ B.width ψ) :
    (B : Set G) = Set.univ := by
  simp only [Set.eq_univ_iff_forall, mem_coe, mem_iff_nnnorm_width]
  intro i ψ _
  calc ‖1 - ψ i‖₊ ≤ ‖(1 : ℂ)‖₊ + ‖ψ i‖₊ := nnnorm_sub_le _ _
    _ = 2 := by norm_num
    _ ≤ B.width ψ := h _

lemma toSet_mono {B₁ B₂ : BohrSet G} (h : B₁ ≤ B₂) :
    B₁.toSet ⊆ B₂.toSet := fun _ hx _ hψ =>
  (hx (frequencies_anti h hψ)).trans (width_le_width h hψ)

lemma toSet_monotone : Monotone (toSet : BohrSet G → Set G) := fun _ _ => toSet_mono

open Pointwise

lemma norm_one_sub_mul {R : Type*} [SeminormedRing R] {a b c : R} (ha : ‖a‖ ≤ 1) :
    ‖c - a * b‖ ≤ ‖c - a‖ + ‖1 - b‖ := by
  calc ‖c - a * b‖ = ‖(c - a) + a * (1 - b)‖ := by noncomm_ring
    _ ≤ ‖c - a‖ + ‖a * (1 - b)‖ := norm_add_le _ _
    _ ≤ ‖c - a‖ + ‖a‖ * ‖1 - b‖ := add_le_add_left (norm_mul_le _ _) _
    _ ≤ ‖c - a‖ + 1 * ‖1 - b‖ := by gcongr
    _ = ‖c - a‖ + ‖1 - b‖ := by simp

lemma norm_one_sub_mul' {R : Type*} [SeminormedRing R] {a b c : R} (hb : ‖b‖ ≤ 1) :
    ‖c - a * b‖ ≤ ‖1 - a‖ + ‖c - b‖ :=
  (norm_one_sub_mul (R := Rᵐᵒᵖ) hb).trans_eq (add_comm _ _)

lemma nnnorm_one_sub_mul {R : Type*} [SeminormedRing R] {a b c : R} (ha : ‖a‖₊ ≤ 1) :
    ‖c - a * b‖₊ ≤ ‖c - a‖₊ + ‖1 - b‖₊ :=
  norm_one_sub_mul ha

lemma nnnorm_one_sub_mul' {R : Type*} [SeminormedRing R] {a b c : R} (hb : ‖b‖₊ ≤ 1) :
    ‖c - a * b‖₊ ≤ ‖1 - a‖₊ + ‖c - b‖₊ :=
  norm_one_sub_mul' hb

lemma smul_add_smul_subset [Finite G] {B : BohrSet G} {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 ≤ ρ₁) (hρ₂ : 0 ≤ ρ₂) :
    (ρ₁ • B).toSet + (ρ₂ • B).toSet ⊆ ((ρ₁ + ρ₂) • B).toSet := by
  intro x
  simp only [Set.mem_add, mem_coe, mem_iff_norm_width, frequencies_smul, width_smul_apply,
    NNReal.coe_mul, Real.coe_nnabs, forall_exists_index, and_imp]
  rintro y h₁ z h₂ rfl ψ hψ
  rw [AddChar.map_add_eq_mul]
  refine (norm_one_sub_mul (by simp)).trans ?_
  simp only [abs_of_nonneg, add_nonneg, hρ₁, hρ₂] at h₁ h₂ ⊢
  linarith [h₁ hψ, h₂ hψ]

variable {ρ : ℝ}

lemma le_card_smul (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) :
    (ρ / 4) ^ B.rank * Nat.card B ≤ Nat.card ↥(ρ • B) := by
  sorry

end BohrSet
