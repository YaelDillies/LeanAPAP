import Project.Mathlib.Algebra.Group.TypeTags
import Project.Mathlib.Analysis.Complex.Circle
import Project.Mathlib.Data.Zmod.Basic
import Project.Mathlib.GroupTheory.FiniteAbelian

#align_import mathlib.number_theory.legendre_symbol.add_char.duality

/-!
# Pontryagin duality for finite abelian groups

This file proves the Pontryagin duality in case of finite abelian groups. This states that any
finite abelian group is canonically isomorphic to its double dual (the space of complex-valued
characters of its space of complex_valued characters).

We first prove it for `zmod n` and then extend to all finite abelian groups using the
Structure Theorem.

## TODO

Add `double_dual_equiv`, the `mul_equiv` extending `double_dual_emb`.
-/


--TODO: This instance is evil
attribute [-instance] AddChar.monoidHomClass

noncomputable section

open circle Finset

open Fintype (card)

open Function

open scoped BigOperators DirectSum

variable {α : Type _} [AddCommGroup α] {n : ℕ} {a b : α}

namespace AddChar

private def zmod_aux_aux (n : ℕ) : ℤ →+ Additive circle
    where
  toFun x := Additive.ofMul (e <| x / n)
  map_zero' := by rw [Int.cast_zero, zero_div, ofMul_eq_zero, map_zero_one]
  map_add' x y := by rw [← ofMul_mul, Equiv.apply_eq_iff_eq, Int.cast_add, add_div, map_add_mul]

@[simp]
theorem zmodAuxAux_apply (n : ℕ) (z : ℤ) : zmodAuxAux n z = Additive.ofMul (e <| z / n) :=
  rfl

/-- The character sending `k : zmod n` to `e ^ (2 * π * i * k / n)`. -/
private def zmod_aux (n : ℕ) : AddChar (ZMod n) circle :=
  AddChar.toMonoidHom'.symm <|
    AddMonoidHom.toMultiplicative'' <|
      (ZMod.lift n
          ⟨zmodAuxAux n, by obtain hn | hn := eq_or_ne (n : ℝ) 0 <;> simp [hn, zmod_aux_aux]⟩ :
        ZMod n →+ Additive circle)

--TODO: Heavily generalise. Yaël's attempts at generalising failed :(
@[simp]
theorem aux (n : ℕ) (h) :
    ⇑(⟨zmodAuxAux n, h⟩ : { f : ℤ →+ Additive circle // f n = 0 }) = zmodAuxAux n :=
  rfl

@[simp]
theorem zmodAux_apply (n : ℕ) (z : ℤ) : zmodAux n z = e (z / n) := by simp [zmod_aux]

-- probably an evil lemma
-- @[simp] lemma zmod_aux_apply (n : ℕ) (x : zmod n) : zmod_aux n x = e (x / n) :=
-- by simp [zmod_aux]
theorem zmodAux_injective (hn : n ≠ 0) : Injective (zmodAux n) :=
  by
  replace hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  simp [zmod_aux, ZMod.lift_injective, CharP.int_cast_eq_zero_iff _ n, e_eq_one, div_eq_iff hn,
    mul_comm _ (n : ℝ), -forall_exists_index]
  norm_cast
  exact fun _ => id

/-- Indexing of the complex characters of `zmod n`. `add_char.zmod n x` is the character sending `y`
to `e ^ (2 * π * i * x * y / n)`. -/
protected def zmod (n : ℕ) (x : ZMod n) : AddChar (ZMod n) circle :=
  (zmodAux n).compAddMonoidHom <| AddMonoidHom.mulLeft x

@[simp]
theorem zMod_apply (n : ℕ) (x y : ℤ) : AddChar.zmod n x y = e (x * y / n) := by
  simp [AddChar.zmod, ← Int.cast_mul]

-- probably an evil lemma
-- @[simp] lemma add_char_apply (n : ℕ) (x y : zmod n) : add_char.zmod n x y = e (x * y / n) :=
-- by simp [add_char.zmod, zmod.coe_mul]
theorem zMod_injective (hn : n ≠ 0) : Injective (AddChar.zmod n) := fun x y h => by
  have := FunLike.congr_fun h (1 : ZMod n) <;> simpa using zmod_aux_injective hn this

@[simp]
theorem zMod_inj (hn : n ≠ 0) {x y : ZMod n} : AddChar.zmod n x = AddChar.zmod n y ↔ x = y :=
  (zMod_injective hn).eq_iff

def zmodHom (n : ℕ) : AddChar (ZMod n) (AddChar (ZMod n) circle) :=
  AddChar.toMonoidHom'.symm
    { toFun := fun x => AddChar.toMonoidHom' (AddChar.zmod n x.toAdd)
      map_one' :=
        FunLike.ext _ _
          (by
            rw [Multiplicative.forall, zmod.int_cast_surjective.forall]
            rintro m
            simp [AddChar.zmod])
      map_mul' :=
        by
        --TODO: Why do we need to intro for `simp` to see the middle `forall`?
        simp only [Multiplicative.forall, zmod.int_cast_surjective.forall, FunLike.ext_iff]
        rintro x
        simp only [Multiplicative.forall, zmod.int_cast_surjective.forall, FunLike.ext_iff]
        rintro y z
        simp [← Int.cast_add, ← add_mul, ← add_div, ← AddChar.map_add_mul] }

def mkZmodAux {ι : Type} [DecidableEq ι] (n : ι → ℕ) (u : ∀ i, ZMod (n i)) :
    AddChar (⨁ i, ZMod (n i)) circle :=
  AddChar.directSum fun i => AddChar.zmod (n i) (u i)

theorem mkZmodAux_injective {ι : Type} [DecidableEq ι] {n : ι → ℕ} (hn : ∀ i, n i ≠ 0) :
    Injective (mkZmodAux n) :=
  AddChar.directSum_injective.comp fun f g h => by simpa [Function.funext_iff, hn] using h

/-- The circle-valued characters of a finite abelian group are the same as its complex-valued
characters. -/
def circleEquivComplex [Finite α] : AddChar α circle ≃+ AddChar α ℂ
    where
  toFun := circle.Subtype.comp
  invFun ψ :=
    AddChar.toMonoidHom'.symm
      { toFun := fun a => (⟨ψ a.toAdd, mem_circle_iff_abs.2 <| ψ.norm_apply _⟩ : circle)
        map_one' := by simp
        map_mul' := fun a b => by ext <;> simp }
  left_inv ψ := by ext <;> simp
  right_inv ψ := by ext <;> simp
  map_add' ψ χ := rfl

@[simp]
theorem card_eq [Fintype α] : card (AddChar α ℂ) = card α :=
  by
  obtain ⟨ι, hi, n, hn, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zMod_of_finite α
  skip
  classical
  have hn' : ∀ i, n i ≠ 0 := fun i => by have := hn i; positivity
  let f : α → AddChar α ℂ := fun a =>
    circle.subtype.comp ((mk_zmod_aux n <| e <| Additive.ofMul a).compAddMonoidHom e)
  have hf : injective f :=
    circle_equiv_complex.injective.comp
      ((comp_add_monoid_hom_injective_left _ <| e.surjective).comp <|
        (mk_zmod_aux_injective hn').comp <|
          fun_like.coe_injective.comp <| e.injective.comp additive.of_mul.injective)
  exact (card_add_char_le _ _).antisymm (Fintype.card_le_of_injective _ hf)

/-- `zmod n` is (noncanonically) isomorphic to its group of characters. -/
def zmodAddEquiv (hn : n ≠ 0) : ZMod n ≃+ AddChar (ZMod n) ℂ :=
  by
  haveI : NeZero n := ⟨hn⟩
  refine'
    AddEquiv.ofBijective
      (circle_equiv_complex.to_add_monoid_hom.comp (AddChar.zmodHom n).toAddMonoidHom) _
  rw [Fintype.bijective_iff_injective_and_card, card_eq]
  exact ⟨circle_equiv_complex.injective.comp <| AddChar.zMod_injective hn, rfl⟩

@[simp]
theorem zmodAddEquiv_apply [NeZero n] (x : ZMod n) :
    AddChar.zmodAddEquiv (NeZero.ne _) x = circleEquivComplex (AddChar.zmod n x) :=
  rfl

section Finite

variable (α) [Finite α]

/-- Complex-valued characters of a finite abelian group `α` form a basis of `α → ℂ`. -/
def complexBasis : Basis (AddChar α ℂ) ℂ (α → ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank (AddChar.linearIndependent _ _) <| by
    cases nonempty_fintype α <;> rw [card_eq, FiniteDimensional.finrank_fintype_fun_eq_card]

@[simp, norm_cast]
theorem coe_complexBasis : ⇑(complexBasis α) = coeFn := by
  rw [complex_basis, coe_basisOfLinearIndependentOfCardEqFinrank]

variable {α}

@[simp]
theorem complexBasis_apply (ψ : AddChar α ℂ) : complexBasis α ψ = ψ := by rw [coe_complex_basis]

theorem exists_apply_ne_zero : (∃ ψ : AddChar α ℂ, ψ a ≠ 1) ↔ a ≠ 0 :=
  by
  refine' ⟨_, fun ha => _⟩
  · rintro ⟨ψ, hψ⟩ rfl
    exact hψ ψ.map_zero_one
  classical
  by_contra' h
  let f : α → ℂ := fun b => if a = b then 1 else 0
  have h₀ := congr_fun ((complex_basis α).sum_repr f) 0
  have h₁ := congr_fun ((complex_basis α).sum_repr f) a
  simp only [complex_basis_apply, Fintype.sum_apply, Pi.smul_apply, h, smul_eq_mul, mul_one,
    map_zero_one, f, if_pos rfl, if_neg ha] at h₀ h₁ 
  exact one_ne_zero (h₁.symm.trans h₀)

theorem forall_apply_eq_zero : (∀ ψ : AddChar α ℂ, ψ a = 1) ↔ a = 0 := by
  simpa using exists_apply_ne_zero.not

theorem doubleDualEmb_injective : Injective (doubleDualEmb : α → AddChar (AddChar α ℂ) ℂ) :=
  injective_iff.2 fun a ha =>
    forall_apply_eq_zero.1 fun ψ => by simpa using FunLike.congr_fun ha (Additive.ofMul ψ)

theorem doubleDualEmb_bijective : Bijective (doubleDualEmb : α → AddChar (AddChar α ℂ) ℂ) := by
  cases nonempty_fintype α <;>
    exact
      (Fintype.bijective_iff_injective_and_card _).2
        ⟨double_dual_emb_injective, card_eq.symm.trans card_eq.symm⟩

@[simp]
theorem doubleDualEmb_inj : (doubleDualEmb a : AddChar (AddChar α ℂ) ℂ) = doubleDualEmb b ↔ a = b :=
  doubleDualEmb_injective.eq_iff

@[simp]
theorem doubleDualEmb_eq_zero : (doubleDualEmb a : AddChar (AddChar α ℂ) ℂ) = 0 ↔ a = 0 := by
  rw [← map_zero double_dual_emb, double_dual_emb_inj]

theorem doubleDualEmb_ne_zero : (doubleDualEmb a : AddChar (AddChar α ℂ) ℂ) ≠ 0 ↔ a ≠ 0 :=
  doubleDualEmb_eq_zero.Not

/-- The double dual isomorphism. -/
def doubleDualEquiv : α ≃+ AddChar (AddChar α ℂ) ℂ :=
  AddEquiv.ofBijective _ doubleDualEmb_bijective

@[simp]
theorem coe_doubleDualEquiv : ⇑(doubleDualEquiv : α ≃+ AddChar (AddChar α ℂ) ℂ) = doubleDualEmb :=
  rfl

@[simp]
theorem doubleDualEmb_doubleDualEquiv_symm_apply (a : AddChar (AddChar α ℂ) ℂ) :
    doubleDualEmb (doubleDualEquiv.symm a) = a :=
  doubleDualEquiv.apply_symm_apply _

@[simp]
theorem doubleDualEquiv_symm_doubleDualEmb_apply (a : AddChar (AddChar α ℂ) ℂ) :
    doubleDualEquiv.symm (doubleDualEmb a) = a :=
  doubleDualEquiv.symm_apply_apply _

end Finite

theorem sum_apply_eq_ite [Fintype α] [DecidableEq α] (a : α) :
    ∑ ψ : AddChar α ℂ, ψ a = if a = 0 then Fintype.card α else 0 := by
  simpa using sum_eq_ite (double_dual_emb a : AddChar (AddChar α ℂ) ℂ)

theorem sum_apply_eq_zero_iff_ne_zero [Finite α] : ∑ ψ : AddChar α ℂ, ψ a = 0 ↔ a ≠ 0 := by
  classical
  cases nonempty_fintype α
  rw [sum_apply_eq_ite, Ne.ite_eq_right_iff]
  exact Nat.cast_ne_zero.2 Fintype.card_ne_zero

theorem sum_apply_ne_zero_iff_eq_zero [Finite α] : ∑ ψ : AddChar α ℂ, ψ a ≠ 0 ↔ a = 0 :=
  sum_apply_eq_zero_iff_ne_zero.not_left

end AddChar

