import mathlib.algebra.group.type_tags
import mathlib.analysis.complex.circle
import mathlib.data.zmod.basic
import mathlib.group_theory.finite_abelian

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
local attribute [-instance] add_char.monoid_hom_class

noncomputable theory

open circle finset fintype (card) function
open_locale big_operators direct_sum

variables {α : Type*} [add_comm_group α] {n : ℕ}

namespace add_char

private def zmod_aux_aux (n : ℕ) : ℤ →+ additive circle :=
{ to_fun := λ x, additive.of_mul (e $ x / n),
  map_zero' := by rw [int.cast_zero, zero_div, of_mul_eq_zero, map_zero_one],
  map_add' := λ x y, by rw [←of_mul_mul, equiv.apply_eq_iff_eq, int.cast_add, add_div,
    map_add_mul] }

@[simp] lemma zmod_aux_aux_apply (n : ℕ) (z : ℤ) : zmod_aux_aux n z = additive.of_mul (e $ z / n) :=
rfl

/-- The character sending `k : zmod n` to `e ^ (2 * π * i * k / n)`. -/
private def zmod_aux (n : ℕ) : add_char (zmod n) circle :=
add_char.to_monoid_hom'.symm $ add_monoid_hom.to_multiplicative'' $
  (zmod.lift n ⟨zmod_aux_aux n, by obtain hn | hn := eq_or_ne (n : ℝ) 0; simp [hn, zmod_aux_aux]⟩
    : zmod n →+ additive circle)

--TODO: Heavily generalise. Yaël's attempts at generalising failed :(
@[simp] lemma aux (n : ℕ) (h) :
  ⇑(⟨zmod_aux_aux n, h⟩ : {f : ℤ →+ additive circle // f n = 0}) = zmod_aux_aux n := rfl

@[simp] lemma zmod_aux_apply (n : ℕ) (z : ℤ) : zmod_aux n z = e (z / n) :=
by simp [zmod_aux]

-- probably an evil lemma
-- @[simp] lemma zmod_aux_apply (n : ℕ) (x : zmod n) : zmod_aux n x = e (x / n) :=
-- by simp [zmod_aux]

lemma zmod_aux_injective (hn : n ≠ 0) : injective (zmod_aux n) :=
begin
  replace hn : (n : ℝ) ≠ 0 := nat.cast_ne_zero.2 hn,
  simp [zmod_aux, zmod.lift_injective, char_p.int_cast_eq_zero_iff _ n, e_eq_one,
    div_eq_iff hn, mul_comm _ (n : ℝ), -forall_exists_index],
  norm_cast,
  exact λ _, id,
end

/-- Indexing of the complex characters of `zmod n`. `add_char.zmod n x` is the character sending `y`
to `e ^ (2 * π * i * x * y / n)`. -/
protected def zmod (n : ℕ) (x : zmod n) : add_char (zmod n) circle :=
(zmod_aux n).comp_add_monoid_hom $ add_monoid_hom.mul_left x

@[simp] lemma zmod_apply (n : ℕ) (x y : ℤ) : add_char.zmod n x y = e (x * y / n) :=
by simp [add_char.zmod, ←int.cast_mul]

-- probably an evil lemma
-- @[simp] lemma add_char_apply (n : ℕ) (x y : zmod n) : add_char.zmod n x y = e (x * y / n) :=
-- by simp [add_char.zmod, zmod.coe_mul]

lemma zmod_injective (hn : n ≠ 0) : injective (add_char.zmod n) :=
λ x y h, by have := fun_like.congr_fun h (1 : zmod n); simpa using zmod_aux_injective hn this

@[simp] lemma zmod_inj (hn : n ≠ 0) {x y : zmod n} :
  add_char.zmod n x = add_char.zmod n y ↔ x = y :=
(zmod_injective hn).eq_iff

def zmod_hom (n : ℕ) : add_char (zmod n) (add_char (zmod n) circle) :=
add_char.to_monoid_hom'.symm { to_fun := λ x, add_char.to_monoid_hom' (add_char.zmod n x.to_add),
  map_one' := fun_like.ext _ _ begin
    rw [multiplicative.forall, zmod.int_cast_surjective.forall],
    rintro m,
    simp [add_char.zmod],
  end,
  map_mul' := begin
    --TODO: Why do we need to intro for `simp` to see the middle `forall`?
    simp only [multiplicative.forall, zmod.int_cast_surjective.forall, fun_like.ext_iff],
    rintro x,
    simp only [multiplicative.forall, zmod.int_cast_surjective.forall, fun_like.ext_iff],
    rintro y z,
    simp [←int.cast_add, ←add_mul, ←add_div, ←add_char.map_add_mul],
  end }

def mk_zmod_aux {ι : Type} [decidable_eq ι] (n : ι → ℕ) (u : Π i, zmod (n i)) :
  add_char (⨁ i, zmod (n i)) circle :=
add_char.direct_sum $ λ i, add_char.zmod (n i) (u i)

lemma mk_zmod_aux_injective {ι : Type} [decidable_eq ι] {n : ι → ℕ} (hn : ∀ i, n i ≠ 0) :
  injective (mk_zmod_aux n) :=
add_char.direct_sum_injective.comp $ λ f g h, by simpa [function.funext_iff, hn] using h

/-- The circle-valued characters of a finite abelian group are the same as its complex-valued
characters. -/
def circle_equiv_complex [finite α] : add_char α circle ≃* add_char α ℂ :=
{ to_fun := circle.subtype.comp,
  inv_fun := λ ψ, add_char.to_monoid_hom'.symm
    { to_fun := λ a, (⟨ψ a.to_add, mem_circle_iff_abs.2 $ ψ.norm_apply _⟩ : circle),
      map_one' := by simp,
      map_mul' := λ a b, by ext; simp },
  left_inv := λ ψ, by ext; simp,
  right_inv := λ ψ, by ext; simp,
  map_mul' := λ ψ χ, rfl }

@[simp] lemma card_eq [fintype α] : card (add_char α ℂ) = card α :=
begin
  obtain ⟨ι, hi, n, hn, ⟨e⟩⟩ := add_comm_group.equiv_direct_sum_zmod_of_finite α,
  resetI,
  classical,
  have hn' : ∀ i, n i ≠ 0 := λ i, by { have := hn i, positivity },
  let f : α → add_char α ℂ := λ a, circle.subtype.comp
    ((mk_zmod_aux n $ e $ additive.of_mul a).comp_add_monoid_hom e),
  have hf : injective f := circle_equiv_complex.injective.comp ((comp_add_monoid_hom_injective_left
    _ $ by exact e.surjective).comp $ (mk_zmod_aux_injective hn').comp $
    fun_like.coe_injective.comp $ e.injective.comp additive.of_mul.injective),
  exact (card_add_char_le _ _).antisymm (fintype.card_le_of_injective _ hf),
end

def zmod_mul_equiv (hn : n ≠ 0) : multiplicative (zmod n) ≃* add_char (zmod n) ℂ :=
begin
  haveI : ne_zero n := ⟨hn⟩,
  refine mul_equiv.of_bijective (circle_equiv_complex.to_monoid_hom.comp
    (add_char.zmod_hom n).to_monoid_hom) _,
  rw [fintype.bijective_iff_injective_and_card, card_eq],
  exact ⟨circle_equiv_complex.injective.comp $ add_char.zmod_injective hn, rfl⟩,
end

@[simp] lemma zmod_mul_equiv_apply [ne_zero n] (x : multiplicative (zmod n)) :
  add_char.zmod_mul_equiv (ne_zero.ne _) x = circle_equiv_complex (add_char.zmod n x) := rfl

section finite
variables (α) [finite α]

/-- Complex-valued characters of a finite abelian group `α` form a basis of `α → ℂ`. -/
def complex_basis : basis (add_char α ℂ) ℂ (α → ℂ) :=
basis_of_linear_independent_of_card_eq_finrank (add_char.linear_independent _ _) $
  by casesI nonempty_fintype α; rw [card_eq, finite_dimensional.finrank_fintype_fun_eq_card]

@[simp, norm_cast] lemma coe_complex_basis : ⇑(complex_basis α) = coe_fn :=
by rw [complex_basis, coe_basis_of_linear_independent_of_card_eq_finrank]

variables {α} {a b : α}

@[simp] lemma complex_basis_apply (ψ : add_char α ℂ) : complex_basis α ψ = ψ :=
by rw coe_complex_basis

lemma exists_apply_ne_zero : (∃ ψ : add_char α ℂ, ψ a ≠ 1) ↔ a ≠ 0 :=
begin
  refine ⟨_, λ ha, _⟩,
  { rintro ⟨ψ, hψ⟩ rfl,
    exact hψ ψ.map_zero_one },
  classical,
  by_contra' h,
  let f : α → ℂ := λ b, if a = b then 1 else 0,
  have h₀ := congr_fun ((complex_basis α).sum_repr f) 0,
  have h₁ := congr_fun ((complex_basis α).sum_repr f) a,
  simp only [complex_basis_apply, fintype.sum_apply, pi.smul_apply, h, smul_eq_mul, mul_one,
    map_zero_one, f, if_pos rfl, if_neg ha] at h₀ h₁,
  exact one_ne_zero (h₁.symm.trans h₀),
end

lemma forall_apply_eq_zero : (∀ ψ : add_char α ℂ, ψ a = 1) ↔ a = 0 :=
by simpa using exists_apply_ne_zero.not

lemma double_dual_emb_injective : injective (double_dual_emb : α → add_char (add_char α ℂ) ℂ) :=
injective_iff.2 $ λ a ha, forall_apply_eq_zero.1 $ λ ψ,
  by simpa using fun_like.congr_fun ha (additive.of_mul ψ)

lemma double_dual_emb_bijective : bijective (double_dual_emb : α → add_char (add_char α ℂ) ℂ) :=
by casesI nonempty_fintype α; exact (fintype.bijective_iff_injective_and_card _).2
  ⟨double_dual_emb_injective, card_eq.symm.trans card_eq.symm⟩

@[simp] lemma double_dual_emb_inj :
  (double_dual_emb a : add_char (add_char α ℂ) ℂ) = double_dual_emb b ↔ a = b :=
double_dual_emb_injective.eq_iff

@[simp] lemma double_dual_emb_eq_zero :
  (double_dual_emb a : add_char (add_char α ℂ) ℂ) = 0 ↔ a = 0 :=
by rw [←map_zero double_dual_emb, double_dual_emb_inj]

lemma double_dual_emb_ne_zero : (double_dual_emb a : add_char (add_char α ℂ) ℂ) ≠ 0 ↔ a ≠ 0 :=
double_dual_emb_eq_zero.not

/-- The double dual isomorphism. -/
def double_dual_equiv : α ≃+ add_char (add_char α ℂ) ℂ :=
add_equiv.of_bijective _ double_dual_emb_bijective

end finite

variables [fintype α] {a : α}

lemma sum_apply [decidable_eq α] (a : α) :
  ∑ ψ : add_char α ℂ, ψ a = if a = 0 then fintype.card α else 0 :=
begin
  split_ifs,
  { simp [h, card_univ, card_eq] },
  { exact sum_eq_zero_iff_ne_zero.2 (double_dual_emb_ne_zero.2 h) }
end

lemma sum_apply_eq_zero_iff_ne_zero : ∑ ψ : add_char α ℂ, ψ a = 0 ↔ a ≠ 0 :=
begin
  classical,
  rw [add_char.sum_apply, ne.ite_eq_right_iff],
  exact nat.cast_ne_zero.2 fintype.card_ne_zero,
end

end add_char
