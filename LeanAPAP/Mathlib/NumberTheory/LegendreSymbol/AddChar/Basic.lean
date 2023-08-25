import LeanAPAP.Mathlib.Algebra.DirectSum.Basic
import LeanAPAP.Mathlib.Analysis.Normed.Field.Basic
import LeanAPAP.Mathlib.Data.IsROrC.Basic
import LeanAPAP.Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import LeanAPAP.Prereqs.Convolution.Basic
import LeanAPAP.Prereqs.LpNorm

#align_import mathlib.number_theory.legendre_symbol.add_char.basic

/-!
### TODO

Rename
* `map_add_mul` → `map_add_eq_mul`
* `map_zero_one` → `map_zero_eq_one`
* `map_nsmul_pow` → `map_nsmul_eq_pow`
* `coe_to_fun_apply` → whatever is better, maybe change to `ψ.to_monoid_hom a = ψ (of_mul a)`.

Kill the evil instance `add_char.monoid_hom_class`. It creates a diamond for
`fun_like (add_char G R) _ _`.
-/

--TODO: This instance is evil
attribute [-instance] AddChar.monoidHomClass

open Finset hiding card

open Fintype (card)

open Function

open scoped BigOperators ComplexConjugate DirectSum

variable {G H R : Type*}

namespace AddChar

section AddMonoid
variable [AddMonoid G] [AddMonoid H] [CommMonoid R] {ψ : AddChar G R}

instance : AddCommMonoid (AddChar G R) :=
  Additive.addCommMonoid

instance funLike : FunLike (AddChar G R) G λ _ => R
    where
  coe := coeFn
  coe_injective' ψ χ h := by cases ψ <;> cases χ <;> congr

#print AddChar.ext /-
@[ext]
lemma ext {ψ χ : AddChar G R} : (ψ : G → R) = χ → ψ = χ :=
  FunLike.ext'
-/

-- TODO: Replace `add_char.to_monoid_hom`
/-- Interpret an additive character as a monoid homomorphism. -/
def toMonoidHom' : AddChar G R ≃ (Multiplicative G →* R) :=
  Equiv.refl _

@[simp, norm_cast]
lemma coe_toMonoid_hom (ψ : AddChar G R) : ⇑ψ.toMonoidHom' = ψ ∘ Multiplicative.toAdd := rfl

@[simp, norm_cast]
lemma coe_toMonoid_hom_symm (ψ : Multiplicative G →* R) :
    ⇑(toMonoidHom'.symm ψ) = ψ ∘ Multiplicative.ofAdd := rfl

@[simp]
lemma toMonoid_hom_apply (ψ : AddChar G R) (a : Multiplicative G) :
    ψ.toMonoidHom' a = ψ (Multiplicative.toAdd a) := rfl

@[simp]
lemma toMonoid_hom_symm_apply (ψ : Multiplicative G →* R) (a : G) :
    toMonoidHom'.symm ψ a = ψ (Multiplicative.ofAdd a) := rfl

/-- Interpret an additive character as a monoid homomorphism. -/
def toAddMonoidHom : AddChar G R ≃ (G →+ Additive R) :=
  MonoidHom.toAdditive

@[simp, norm_cast]
lemma coe_toAddMonoidHom (ψ : AddChar G R) : ⇑ψ.toAddMonoidHom = Additive.ofMul ∘ ψ := rfl

@[simp, norm_cast]
lemma coe_toAddMonoidHom_symm (ψ : G →+ Additive R) :
    ⇑(toAddMonoidHom.symm ψ) = Additive.toMul ∘ ψ := rfl

@[simp]
lemma toAddMonoidHom_apply (ψ : AddChar G R) (a : G) :
    ψ.toAddMonoidHom a = Additive.ofMul (ψ a) := rfl

@[simp]
lemma toAddMonoidHom_symm_apply (ψ : G →+ Additive R) (a : G) :
    toAddMonoidHom.symm ψ a = Additive.toMul (ψ a) := rfl

lemma eq_one_iff : ψ = 0 ↔ ∀ x, ψ x = 1 :=
  FunLike.ext_iff

lemma ne_one_iff : ψ ≠ 0 ↔ ∃ x, ψ x ≠ 1 :=
  FunLike.ne_iff

@[simp, norm_cast]
lemma coe_one : ⇑(1 : AddChar G R) = 1 := rfl

#print AddChar.one_apply /-
lemma one_apply (a : G) : (1 : AddChar G R) a = 1 := rfl
-/

@[simp, norm_cast]
lemma coe_mul (ψ χ : AddChar G R) : ⇑(ψ * χ) = ψ * χ := rfl

lemma mul_apply (ψ χ : AddChar G R) (a : G) : (ψ * χ) a = ψ a * χ a := rfl

@[simp, norm_cast]
lemma coe_pow (n : ℕ) (ψ : AddChar G R) : ⇑(ψ ^ n) = ψ ^ n := rfl

lemma pow_apply (n : ℕ) (ψ : AddChar G R) (a : G) : (ψ ^ n) a = ψ a ^ n := rfl

lemma eq_zero_iff : ψ = 0 ↔ ∀ x, ψ x = 1 :=
  FunLike.ext_iff

lemma ne_zero_iff : ψ ≠ 0 ↔ ∃ x, ψ x ≠ 1 :=
  FunLike.ne_iff

@[simp, norm_cast]
lemma coe_zero : ⇑(0 : AddChar G R) = 1 := rfl

lemma zero_apply (a : G) : (0 : AddChar G R) a = 1 := rfl

@[simp, norm_cast]
lemma coe_eq_zero : ⇑ψ = 1 ↔ ψ = 0 := by rw [← coe_zero, FunLike.coe_fn_eq]

@[simp, norm_cast]
lemma coe_add (ψ χ : AddChar G R) : ⇑(ψ + χ) = ψ * χ := rfl

lemma add_apply (ψ χ : AddChar G R) (a : G) : (ψ + χ) a = ψ a * χ a := rfl

@[simp, norm_cast]
lemma coe_nsmul (n : ℕ) (ψ : AddChar G R) : ⇑(n • ψ) = ψ ^ n := rfl

lemma nsmul_apply (n : ℕ) (ψ : AddChar G R) (a : G) : (ψ ^ n) a = ψ a ^ n := rfl

variable {ι : Type*}

@[simp, norm_cast]
lemma coe_sum (s : Finset ι) (ψ : ι → AddChar G R) : ⇑(∑ i in s, ψ i) = ∏ i in s, ψ i := by
  induction s using Finset.cons_induction <;> simp [*]

lemma sum_apply (s : Finset ι) (ψ : ι → AddChar G R) (a : G) :
    (∑ i in s, ψ i) a = ∏ i in s, ψ i a := by rw [coe_sum, Finset.prod_apply]

noncomputable instance : DecidableEq (AddChar G R) :=
  Classical.decEq _

/-- Precompose a `R`-valued character of `H` with a homomorphism `G → H` to get a `R`-valued
character of `G`. -/
def compAddMonoidHom (ψ : AddChar H R) (f : G →+ H) : AddChar G R :=
  toMonoidHom'.symm <| ψ.toMonoidHom'.comp f.toMultiplicative

@[simp]
lemma compAddMonoidHom_apply (ψ : AddChar H R) (f : G →+ H) (a : G) :
    ψ.compAddMonoidHom f a = ψ (f a) := rfl

@[simp, norm_cast]
lemma coe_compAddMonoidHom (ψ : AddChar H R) (f : G →+ H) : ⇑(ψ.compAddMonoidHom f) = ψ ∘ f := rfl

lemma compAddMonoidHom_injective_left (f : G →+ H) (hf : Surjective f) :
    Injective λ ψ : AddChar H R => ψ.compAddMonoidHom f := by
  rintro ψ χ h
  rw [FunLike.ext'_iff] at h
  dsimp at h
  exact FunLike.ext' (hf.injective_comp_right h)

/-- The double dual embedding. -/
def doubleDualEmb : G →+ AddChar (AddChar G R) R :=
  MonoidHom.eval.toAdditive

@[simp]
lemma doubleDualEmb_apply (a : G) (ψ : AddChar G R) : doubleDualEmb a ψ = ψ a := rfl

end AddMonoid

section AddGroup
variable [AddGroup G]

section DivisionCommMonoid
variable [DivisionCommMonoid R]

lemma map_sub_eq_div (ψ : AddChar G R) (x y : G) : ψ (x - y) = ψ x / ψ y := by
  rw [coe_to_fun_apply, coe_to_fun_apply _ x, coe_to_fun_apply _ y, ofAdd_sub, map_div]

lemma injective_iff {ψ : AddChar G R} : Injective ψ ↔ ∀ ⦃x⦄, ψ x = 1 → x = 0 :=
  ψ.ker_eq_bot_iff.symm.trans eq_bot_iff

end DivisionCommMonoid

section NormedField
variable [Finite G] [NormedField R]

@[simp]
lemma norm_apply (ψ : AddChar G R) (x : G) : ‖ψ x‖ = 1 :=
  (ψ.IsOfFinOrder <| exists_pow_eq_one _).norm_eq_one

@[simp]
lemma coe_ne_zero (ψ : AddChar G R) : (ψ : G → R) ≠ 0 :=
  Function.ne_iff.2 ⟨0, λ h => by simpa [h] using ψ.norm_apply 0⟩

end NormedField

section IsROrC
variable [IsROrC R]

lemma inv_apply_eq_conj [Finite G] (ψ : AddChar G R) (x : G) : (ψ x)⁻¹ = conj (ψ x) :=
  IsROrC.inv_eq_conj <| norm_apply _ _

@[simp]
protected lemma l2inner_self [Fintype G] (ψ : AddChar G R) :
    ⟪(ψ : G → R), ψ⟫_[R] = Fintype.card G :=
  l2inner_self_of_norm_eq_one ψ.norm_apply

end IsROrC

variable [Fintype G] [CommSemiring R] [IsDomain R] [CharZero R] {ψ : AddChar G R}

lemma sum_eq_ite [DecidableEq G] (ψ : AddChar G R) : ∑ a, ψ a = if ψ = 0 then card G else 0 := by
  split_ifs
  · simp [h, card_univ]
  obtain ⟨x, hx⟩ := ne_one_iff.1 h
  refine' eq_zero_of_mul_eq_self_left hx _
  rw [Finset.mul_sum]
  exact Fintype.sum_equiv (Equiv.addLeft x) _ _ λ y => (map_add_mul _ _ _).symm

lemma sum_eq_zero_iff_ne_zero : ∑ x, ψ x = 0 ↔ ψ ≠ 0 := by
  classical
  rw [sum_eq_ite, Ne.ite_eq_right_iff]
  exact Nat.cast_ne_zero.2 Fintype.card_ne_zero

lemma sum_ne_zero_iff_eq_zero : ∑ x, ψ x ≠ 0 ↔ ψ = 0 :=
  sum_eq_zero_iff_ne_zero.not_left

end AddGroup

section AddCommGroup
variable [AddCommGroup G]

section CommMonoid
variable [CommMonoid R]

/-- The additive characters on a commutative additive group form a commutative group. -/
instance : AddCommGroup (AddChar G R) :=
  @Additive.addCommGroup (AddChar G R) _

@[simp]
lemma neg_apply (ψ : AddChar G R) (a : G) : (-ψ) a = ψ (-a) := rfl

@[simp]
lemma sub_apply (ψ χ : AddChar G R) (a : G) : (ψ - χ) a = ψ a * χ (-a) := rfl

end CommMonoid

section DivisionCommMonoid
variable [DivisionCommMonoid R]

-- TODO: Replace `map_zsmul_zpow`
@[simp]
lemma map_zsmul_eq_zpow (ψ : AddChar G R) (n : ℤ) (a : G) : ψ (n • a) = ψ a ^ n :=
  map_zpow ψ.toMonoidHom _ _

lemma map_neg_eq_inv (ψ : AddChar G R) (x : G) : ψ (-x) = (ψ x)⁻¹ :=
  eq_inv_of_mul_eq_one_left <| by simp [← map_add_mul]

lemma inv_apply' (ψ : AddChar G R) (x : G) : ψ⁻¹ x = (ψ x)⁻¹ :=
  map_neg_eq_inv _ _

lemma neg_apply' (ψ : AddChar G R) (x : G) : (-ψ) x = (ψ x)⁻¹ :=
  map_neg_eq_inv _ _

lemma sub_apply' (ψ χ : AddChar G R) (a : G) : (ψ - χ) a = ψ a / χ a := by
  rw [sub_apply, map_neg_eq_inv, div_eq_mul_inv]

end DivisionCommMonoid

section IsROrC
variable [IsROrC R] {ψ₁ ψ₂ : AddChar G R}

lemma l2inner_eq [Fintype G] (ψ₁ ψ₂ : AddChar G R) :
    ⟪(ψ₁ : G → R), ψ₂⟫_[R] = if ψ₁ = ψ₂ then Fintype.card G else 0 := by
  split_ifs
  · rw [h, AddChar.l2inner_self]
  have : ψ₁⁻¹ * ψ₂ ≠ 1 := by rwa [Ne.def, inv_mul_eq_one]
  simp_rw [l2inner_eq_sum, ← inv_apply_eq_conj]
  simpa [inv_apply'] using sum_eq_zero_iff_ne_zero.2 this

lemma l2inner_eq_zero_iff_ne [Fintype G] : ⟪(ψ₁ : G → R), ψ₂⟫_[R] = 0 ↔ ψ₁ ≠ ψ₂ := by
  rw [L2inner_eq, Ne.ite_eq_right_iff (Nat.cast_ne_zero.2 Fintype.card_ne_zero)] <;> infer_instance

lemma l2inner_eq_card_iff_eq [Fintype G] : ⟪(ψ₁ : G → R), ψ₂⟫_[R] = Fintype.card G ↔ ψ₁ = ψ₂ := by
  rw [L2inner_eq, Ne.ite_eq_left_iff (Nat.cast_ne_zero.2 Fintype.card_ne_zero)] <;> infer_instance

variable (G R)

protected lemma linearIndependent [Finite G] :
    LinearIndependent R (coeFn : AddChar G R → G → R) := by
  cases nonempty_fintype G
  exact
    linearIndependent_of_ne_zero_of_l2inner_eq_zero AddChar.coe_ne_zero λ ψ₁ ψ₂ =>
      L2inner_eq_zero_iff_ne.2

noncomputable instance [Finite G] : Fintype (AddChar G R) :=
  @Fintype.ofFinite _ (AddChar.linearIndependent G R).finite'

@[simp]
lemma card_addChar_le [Fintype G] : card (AddChar G R) ≤ card G := by
  simpa only [FiniteDimensional.finrank_fintype_fun_eq_card] using
    FiniteDimensional.fintype_card_le_finrank_of_linearIndependent (AddChar.linearIndependent G R)

end IsROrC

end AddCommGroup

section DirectSum
variable {ι : Type*} {π : ι → Type*} [DecidableEq ι] [∀ i, AddCommGroup (π i)] [CommMonoid R]

/-- Direct sum of additive characters. -/
protected def directSum (ψ : ∀ i, AddChar (π i) R) : AddChar (⨁ i, π i) R :=
  AddChar.toAddMonoidHom.symm
    (DirectSum.toAddMonoid λ i => (ψ i).toAddMonoidHom : (⨁ i, π i) →+ Additive R)

lemma directSum_injective :
    Injective (AddChar.directSum : (∀ i, AddChar (π i) R) → AddChar (⨁ i, π i) R) := by
  refine' add_char.to_add_monoid_hom.symm.injective.comp (direct_sum.to_add_monoid_injective.comp _)
  rintro ψ χ h
  simpa [Function.funext_iff] using h

end DirectSum

end AddChar
