import Mathlib.Algebra.Group.AddChar

/-!
### TODO

Rename
* `map_add_mul` → `map_add_eq_mul`
* `map_zero_one` → `map_zero_eq_one`
* `map_nsmul_pow` → `map_nsmul_eq_pow`
-/

open Finset hiding card
open Fintype (card)
open Function
open scoped BigOperators ComplexConjugate NNRat

variable {G H R : Type*}

namespace AddChar
section AddMonoid
variable [AddMonoid G] [AddMonoid H] [CommMonoid R] {ψ : AddChar G R}

instance instAddCommMonoid : AddCommMonoid (AddChar G R) := Additive.addCommMonoid

attribute [simp, norm_cast] mul_apply one_apply MonoidHom.coe_compAddChar coe_compAddMonoidHom

-- TODO: Replace `AddChar.toMonoidHomEquiv`
/-- Interpret an additive character as a monoid homomorphism. -/
def toMonoidHomEquiv' : AddChar G R ≃ (Multiplicative G →* R) := toMonoidHomEquiv _ _

@[simp, norm_cast]
lemma coe_toMonoidHomEquiv' (ψ : AddChar G R) : ⇑(toMonoidHomEquiv' ψ) = ψ ∘ Multiplicative.toAdd := rfl

@[simp, norm_cast] lemma coe_toMonoidHomEquiv'_symm (ψ : Multiplicative G →* R) :
    ⇑(toMonoidHomEquiv'.symm ψ) = ψ ∘ Multiplicative.ofAdd := rfl

@[simp] lemma toMonoidHomEquiv'_apply (ψ : AddChar G R) (a : Multiplicative G) :
    toMonoidHomEquiv' ψ a = ψ (Multiplicative.toAdd a) := rfl

@[simp] lemma toMonoidHomEquiv'_symm_apply (ψ : Multiplicative G →* R) (a : G) :
    toMonoidHomEquiv'.symm ψ a = ψ (Multiplicative.ofAdd a) := rfl

@[simp] lemma toMonoidHomEquiv'_zero : toMonoidHomEquiv' (0 : AddChar G R) = 1 := rfl
@[simp] lemma toMonoidHomEquiv'_symm_one : toMonoidHomEquiv'.symm (1 : Multiplicative G →* R) = 0 := rfl

@[simp] lemma toMonoidHomEquiv'_add (ψ φ : AddChar G R) :
    toMonoidHomEquiv' (ψ + φ) = toMonoidHomEquiv' ψ * toMonoidHomEquiv' φ := rfl
@[simp] lemma toMonoidHomEquiv'_symm_mul (ψ φ : Multiplicative G →* R) :
  toMonoidHomEquiv'.symm (ψ * φ) = toMonoidHomEquiv'.symm ψ + toMonoidHomEquiv'.symm φ := rfl

/-- Interpret an additive character as a monoid homomorphism. -/
def toAddMonoidHomEquiv' : AddChar G R ≃ (G →+ Additive R) := toAddMonoidHomEquiv _ _

@[simp, norm_cast]
lemma coe_toAddMonoidHomEquiv' (ψ : AddChar G R) : ⇑(toAddMonoidHomEquiv' ψ) = Additive.ofMul ∘ ψ := rfl

@[simp, norm_cast] lemma coe_toAddMonoidHomEquiv'_symm (ψ : G →+ Additive R) :
    ⇑(toAddMonoidHomEquiv'.symm ψ) = Additive.toMul ∘ ψ := rfl

@[simp] lemma toAddMonoidHomEquiv'_apply (ψ : AddChar G R) (a : G) :
    toAddMonoidHomEquiv' ψ a = Additive.ofMul (ψ a) := rfl

@[simp] lemma toAddMonoidHomEquiv'_symm_apply (ψ : G →+ Additive R) (a : G) :
    toAddMonoidHomEquiv'.symm ψ a = Additive.toMul (ψ a) := rfl

lemma eq_one_iff : ψ = 0 ↔ ∀ x, ψ x = 1 := DFunLike.ext_iff
lemma ne_one_iff : ψ ≠ 0 ↔ ∃ x, ψ x ≠ 1 := DFunLike.ne_iff

@[simp, norm_cast] lemma coe_one : ⇑(1 : AddChar G R) = 1 := rfl
@[simp, norm_cast] lemma coe_mul (ψ χ : AddChar G R) : ⇑(ψ * χ) = ψ * χ := rfl

@[simp, norm_cast] lemma coe_pow (n : ℕ) (ψ : AddChar G R) : ⇑(ψ ^ n) = ψ ^ n := rfl

lemma eq_zero_iff : ψ = 0 ↔ ∀ x, ψ x = 1 := DFunLike.ext_iff
lemma ne_zero_iff : ψ ≠ 0 ↔ ∃ x, ψ x ≠ 1 := DFunLike.ne_iff

@[simp, norm_cast] lemma coe_zero : ⇑(0 : AddChar G R) = 1 := rfl

lemma zero_apply (a : G) : (0 : AddChar G R) a = 1 := rfl

@[simp, norm_cast] lemma coe_eq_zero : ⇑ψ = 1 ↔ ψ = 0 := by rw [← coe_zero, DFunLike.coe_fn_eq]
@[simp, norm_cast] lemma coe_add (ψ χ : AddChar G R) : ⇑(ψ + χ) = ψ * χ := rfl

lemma add_apply (ψ χ : AddChar G R) (a : G) : (ψ + χ) a = ψ a * χ a := rfl

@[simp, norm_cast] lemma coe_nsmul (n : ℕ) (ψ : AddChar G R) : ⇑(n • ψ) = ψ ^ n := rfl

lemma nsmul_apply (n : ℕ) (ψ : AddChar G R) (a : G) : (ψ ^ n) a = ψ a ^ n := rfl

variable {ι : Type*}

@[simp, norm_cast]
lemma coe_sum (s : Finset ι) (ψ : ι → AddChar G R) : ∑ i in s, ψ i = ∏ i in s, ⇑(ψ i) := by
  induction s using Finset.cons_induction <;> simp [*]

lemma sum_apply (s : Finset ι) (ψ : ι → AddChar G R) (a : G) :
    (∑ i in s, ψ i) a = ∏ i in s, ψ i a := by rw [coe_sum, Finset.prod_apply]

noncomputable instance : DecidableEq (AddChar G R) := Classical.decEq _

@[simp] lemma compAddMonoidHom_apply (ψ : AddChar H R) (f : G →+ H) (a : G) :
    (ψ.compAddMonoidHom f) a = ψ (f a) := rfl

lemma compAddMonoidHom_injective_left (f : G →+ H) (hf : Surjective f) :
    Injective fun ψ : AddChar H R ↦ ψ.compAddMonoidHom f := by
  rintro ψ χ h
  rw [DFunLike.ext'_iff] at h ⊢
  exact hf.injective_comp_right h

lemma compAddMonoidHom_injective_right (ψ : AddChar H R) (hψ : Injective ψ) :
    Injective fun f : G →+ H ↦ ψ.compAddMonoidHom f := by
  rintro f g h
  rw [DFunLike.ext'_iff] at h ⊢
  exact hψ.comp_left h

/-- The double dual embedding. -/
def doubleDualEmb : G →+ AddChar (AddChar G R) R where
  toFun a := { toFun := fun ψ ↦ ψ a
               map_zero_one' := by simp
               map_add_mul' := by simp }
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp [map_add_mul]

@[simp] lemma doubleDualEmb_apply (a : G) (ψ : AddChar G R) : doubleDualEmb a ψ = ψ a := rfl

end AddMonoid

section AddGroup
variable [AddGroup G]

section DivisionCommMonoid
variable [DivisionCommMonoid R]

lemma map_sub_eq_div (ψ : AddChar G R) (x y : G) : ψ (x - y) = ψ x / ψ y :=
  ψ.toMonoidHom.map_div _ _

lemma injective_iff {ψ : AddChar G R} : Injective ψ ↔ ∀ ⦃x⦄, ψ x = 1 → x = 0 :=
  ψ.toMonoidHom.ker_eq_bot_iff.symm.trans eq_bot_iff

end DivisionCommMonoid

section CommSemiring
variable [Fintype G] [CommSemiring R] [IsDomain R] [CharZero R] {ψ : AddChar G R}

lemma sum_eq_ite (ψ : AddChar G R) : ∑ a, ψ a = if ψ = 0 then ↑(card G) else 0 := by
  split_ifs with h
  · simp [h, card_univ]
  obtain ⟨x, hx⟩ := ne_one_iff.1 h
  refine' eq_zero_of_mul_eq_self_left hx _
  rw [Finset.mul_sum]
  exact Fintype.sum_equiv (Equiv.addLeft x) _ _ fun y ↦ (map_add_mul _ _ _).symm

lemma sum_eq_zero_iff_ne_zero : ∑ x, ψ x = 0 ↔ ψ ≠ 0 := by
  rw [sum_eq_ite, Ne.ite_eq_right_iff]
  exact Nat.cast_ne_zero.2 Fintype.card_ne_zero

lemma sum_ne_zero_iff_eq_zero : ∑ x, ψ x ≠ 0 ↔ ψ = 0 :=
  sum_eq_zero_iff_ne_zero.not_left

end CommSemiring
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
  eq_inv_of_mul_eq_one_left $ by simp [← map_add_mul]

lemma neg_apply' (ψ : AddChar G R) (x : G) : (-ψ) x = (ψ x)⁻¹ :=
  map_neg_eq_inv _ _

lemma sub_apply' (ψ χ : AddChar G R) (a : G) : (ψ - χ) a = ψ a / χ a := by
  rw [sub_apply, map_neg_eq_inv, div_eq_mul_inv]

end DivisionCommMonoid
end AddCommGroup
end AddChar
