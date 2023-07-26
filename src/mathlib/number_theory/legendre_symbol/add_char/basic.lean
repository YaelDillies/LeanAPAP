import mathlib.algebra.direct_sum.basic
import mathlib.analysis.normed.field.basic
import mathlib.data.is_R_or_C.basic
import mathlib.linear_algebra.finite_dimensional
import number_theory.legendre_symbol.add_character
import prereqs.convolution.basic
import prereqs.lp_norm

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
local attribute [-instance] add_char.monoid_hom_class

open finset (hiding card) fintype (card) function
open_locale big_operators complex_conjugate direct_sum

variables {G H R : Type*}

namespace add_char
section add_monoid
variables [add_monoid G] [add_monoid H] [comm_monoid R] {ψ : add_char G R}

instance : add_comm_monoid (add_char G R) := additive.add_comm_monoid

instance fun_like : fun_like (add_char G R) G (λ _, R) :=
{ coe := coe_fn,
  coe_injective' := λ ψ χ h, by cases ψ; cases χ; congr' }

@[ext] lemma ext {ψ χ : add_char G R} : (ψ : G → R) = χ → ψ = χ := fun_like.ext'

-- TODO: Replace `add_char.to_monoid_hom`
/-- Interpret an additive character as a monoid homomorphism. -/
def to_monoid_hom' : add_char G R ≃ (multiplicative G →* R) := equiv.refl _

@[simp, norm_cast] lemma coe_to_monoid_hom (ψ : add_char G R) :
  ⇑ψ.to_monoid_hom' = ψ ∘ multiplicative.to_add := rfl
@[simp, norm_cast] lemma coe_to_monoid_hom_symm (ψ : multiplicative G →* R) :
  ⇑(to_monoid_hom'.symm ψ) = ψ ∘ multiplicative.of_add := rfl

@[simp] lemma to_monoid_hom_apply (ψ : add_char G R) (a : multiplicative G) :
  ψ.to_monoid_hom' a = ψ (multiplicative.to_add a) := rfl
@[simp] lemma to_monoid_hom_symm_apply (ψ : multiplicative G →* R) (a : G) :
  to_monoid_hom'.symm ψ a = ψ (multiplicative.of_add a) := rfl

/-- Interpret an additive character as a monoid homomorphism. -/
def to_add_monoid_hom : add_char G R ≃ (G →+ additive R) := monoid_hom.to_additive

@[simp, norm_cast] lemma coe_to_add_monoid_hom (ψ : add_char G R) :
  ⇑ψ.to_add_monoid_hom = additive.of_mul ∘ ψ := rfl
@[simp, norm_cast] lemma coe_to_add_monoid_hom_symm (ψ : G →+ additive R) :
  ⇑(to_add_monoid_hom.symm ψ) = additive.to_mul ∘ ψ := rfl

@[simp] lemma to_add_monoid_hom_apply (ψ : add_char G R) (a : G) :
  ψ.to_add_monoid_hom a = additive.of_mul (ψ a) := rfl
@[simp] lemma to_add_monoid_hom_symm_apply (ψ : G →+ additive R) (a : G) :
  to_add_monoid_hom.symm ψ a = additive.to_mul (ψ a) := rfl

lemma eq_one_iff : ψ = 0 ↔ ∀ x, ψ x = 1 := fun_like.ext_iff
lemma ne_one_iff : ψ ≠ 0 ↔ ∃ x, ψ x ≠ 1 := fun_like.ne_iff

@[simp, norm_cast] lemma coe_one : ⇑(1 : add_char G R) = 1 := rfl
lemma one_apply (a : G) : (1 : add_char G R) a = 1 := rfl

@[simp, norm_cast] lemma coe_mul (ψ χ : add_char G R) : ⇑(ψ * χ) = ψ * χ := rfl
lemma mul_apply (ψ χ : add_char G R) (a : G) : (ψ * χ) a = ψ a * χ a := rfl

@[simp, norm_cast] lemma coe_pow (n : ℕ) (ψ : add_char G R) : ⇑(ψ ^ n) = ψ ^ n := rfl
lemma pow_apply (n : ℕ) (ψ : add_char G R) (a : G) : (ψ ^ n) a = (ψ a) ^ n := rfl

lemma eq_zero_iff : ψ = 0 ↔ ∀ x, ψ x = 1 := fun_like.ext_iff
lemma ne_zero_iff : ψ ≠ 0 ↔ ∃ x, ψ x ≠ 1 := fun_like.ne_iff

@[simp, norm_cast] lemma coe_zero : ⇑(0 : add_char G R) = 1 := rfl
lemma zero_apply (a : G) : (0 : add_char G R) a = 1 := rfl
@[simp, norm_cast] lemma coe_eq_zero : ⇑ψ = 1 ↔ ψ = 0 := by rw [←coe_zero, fun_like.coe_fn_eq]

@[simp, norm_cast] lemma coe_add (ψ χ : add_char G R) : ⇑(ψ + χ) = ψ * χ := rfl
lemma add_apply (ψ χ : add_char G R) (a : G) : (ψ + χ) a = ψ a * χ a := rfl

@[simp, norm_cast] lemma coe_nsmul (n : ℕ) (ψ : add_char G R) : ⇑(n • ψ) = ψ ^ n := rfl
lemma nsmul_apply (n : ℕ) (ψ : add_char G R) (a : G) : (ψ ^ n) a = (ψ a) ^ n := rfl

noncomputable instance : decidable_eq (add_char G R) := classical.dec_eq _

/-- Precompose a `R`-valued character of `H` with a homomorphism `G → H` to get a `R`-valued
character of `G`. -/
def comp_add_monoid_hom (ψ : add_char H R) (f : G →+ H) : add_char G R :=
to_monoid_hom'.symm $ ψ.to_monoid_hom'.comp f.to_multiplicative

@[simp] lemma comp_add_monoid_hom_apply (ψ : add_char H R) (f : G →+ H) (a : G) :
  ψ.comp_add_monoid_hom f a = ψ (f a) := rfl

@[simp, norm_cast] lemma coe_comp_add_monoid_hom (ψ : add_char H R) (f : G →+ H) :
  ⇑(ψ.comp_add_monoid_hom f) = ψ ∘ f := rfl

lemma comp_add_monoid_hom_injective_left (f : G →+ H) (hf : surjective f) :
  injective (λ ψ : add_char H R, ψ.comp_add_monoid_hom f) :=
begin
  rintro ψ χ h,
  rw fun_like.ext'_iff at h,
  dsimp at h,
  exact fun_like.ext' (hf.injective_comp_right h),
end

/-- The double dual embedding. -/
def double_dual_emb : G →+ add_char (add_char G R) R := monoid_hom.eval.to_additive

@[simp] lemma double_dual_emb_apply (a : G) (ψ : add_char G R) : double_dual_emb a ψ = ψ a := rfl

end add_monoid

section add_group
variables [add_group G]

section division_comm_monoid
variables [division_comm_monoid R]

lemma map_sub_eq_div (ψ : add_char G R) (x y : G) : ψ (x - y) = ψ x / ψ y :=
by rw [coe_to_fun_apply, coe_to_fun_apply _ x, coe_to_fun_apply _ y, of_add_sub, map_div]

lemma injective_iff {ψ : add_char G R} : injective ψ ↔ ∀ ⦃x⦄, ψ x = 1 → x = 0 :=
ψ.ker_eq_bot_iff.symm.trans eq_bot_iff

end division_comm_monoid

section normed_field
variables [finite G] [normed_field R]

@[simp] lemma norm_apply (ψ : add_char G R) (x : G) : ‖ψ x‖ = 1 :=
(ψ.is_of_fin_order $ exists_pow_eq_one _).norm_eq_one

@[simp] lemma coe_ne_zero (ψ : add_char G R) : (ψ : G → R) ≠ 0 :=
function.ne_iff.2 ⟨0, λ h, by simpa [h] using ψ.norm_apply 0⟩

end normed_field

section is_R_or_C
variables [is_R_or_C R]

lemma inv_apply_eq_conj [finite G] (ψ : add_char G R) (x : G) : (ψ x)⁻¹ = conj (ψ x) :=
is_R_or_C.inv_eq_conj $ norm_apply _ _

@[simp] protected lemma L2inner_self [fintype G] (ψ : add_char G R) :
  ⟪(ψ : G → R), ψ⟫_[R] = fintype.card G :=
L2inner_self_of_norm_eq_one ψ.norm_apply

end is_R_or_C

variables [fintype G] [comm_semiring R] [is_domain R] [char_zero R] {ψ : add_char G R}

lemma sum_eq_zero_iff_ne_zero : ∑ x, ψ x = 0 ↔ ψ ≠ 0 :=
begin
  refine ⟨_, λ h, _⟩,
  { rintro h rfl,
    simpa [card_univ, fintype.card_ne_zero] using h },
  obtain ⟨x, hx⟩ := ne_one_iff.1 h,
  refine eq_zero_of_mul_eq_self_left hx _,
  rw finset.mul_sum,
  exact fintype.sum_equiv (equiv.add_left x) _ _ (λ y, (map_add_mul _ _ _).symm),
end

lemma sum_ne_zero_iff_eq_zero : ∑ x, ψ x ≠ 0 ↔ ψ = 0 := sum_eq_zero_iff_ne_zero.not_left

end add_group

section add_comm_group
variables [add_comm_group G]

section comm_monoid
variables [comm_monoid R]

/-- The additive characters on a commutative additive group form a commutative group. -/
instance : add_comm_group (add_char G R) := @additive.add_comm_group (add_char G R) _

@[simp] lemma neg_apply (ψ : add_char G R) (a : G) : (-ψ) a = ψ (-a) := rfl

end comm_monoid

section division_comm_monoid
variables [division_comm_monoid R]

-- TODO: Replace `map_zsmul_zpow`
@[simp] lemma map_zsmul_eq_zpow (ψ : add_char G R) (n : ℤ) (a : G) : ψ (n • a) = ψ a ^ n :=
map_zpow ψ.to_monoid_hom _ _

lemma map_neg_eq_inv (ψ : add_char G R) (x : G) : ψ (-x) = (ψ x)⁻¹ :=
eq_inv_of_mul_eq_one_left $ by simp [←map_add_mul]

lemma inv_apply' (ψ : add_char G R) (x : G) : ψ⁻¹ x = (ψ x)⁻¹ := map_neg_eq_inv _ _
lemma neg_apply' (ψ : add_char G R) (x : G) : (-ψ) x = (ψ x)⁻¹ := map_neg_eq_inv _ _

end division_comm_monoid

section is_R_or_C
variables [is_R_or_C R] {ψ₁ ψ₂ : add_char G R}

lemma L2inner_eq [fintype G] (ψ₁ ψ₂ : add_char G R) :
  ⟪(ψ₁ : G → R), ψ₂⟫_[R] = if ψ₁ = ψ₂ then fintype.card G else 0 :=
begin
  split_ifs,
  { rw [h, add_char.L2inner_self] },
  have : ψ₁⁻¹ * ψ₂ ≠ 1, { rwa [ne.def, inv_mul_eq_one] },
  simp_rw [L2inner_eq_sum, ←inv_apply_eq_conj],
  simpa [inv_apply'] using sum_eq_zero_iff_ne_zero.2 this,
end

lemma L2inner_eq_zero_iff_ne [fintype G] : ⟪(ψ₁ : G → R), ψ₂⟫_[R] = 0 ↔ ψ₁ ≠ ψ₂ :=
by rw [L2inner_eq, ne.ite_eq_right_iff (nat.cast_ne_zero.2 fintype.card_ne_zero)]; apply_instance

lemma L2inner_eq_card_iff_eq [fintype G] : ⟪(ψ₁ : G → R), ψ₂⟫_[R] = fintype.card G ↔ ψ₁ = ψ₂ :=
by rw [L2inner_eq, ne.ite_eq_left_iff (nat.cast_ne_zero.2 fintype.card_ne_zero)]; apply_instance

variables (G R)

protected lemma linear_independent [finite G] :
  linear_independent R (coe_fn : add_char G R → G → R) :=
begin
  casesI nonempty_fintype G,
  exact linear_independent_of_ne_zero_of_L2inner_eq_zero add_char.coe_ne_zero
    (λ ψ₁ ψ₂, L2inner_eq_zero_iff_ne.2),
end

noncomputable instance fintype_add_char [finite G] : fintype (add_char G R) :=
@fintype.of_finite _ (add_char.linear_independent G R).finite'

@[simp] lemma card_add_char_le [fintype G] : card (add_char G R) ≤ card G :=
by simpa only [finite_dimensional.finrank_fintype_fun_eq_card] using
    finite_dimensional.fintype_card_le_finrank_of_linear_independent
      (add_char.linear_independent G R)

end is_R_or_C
end add_comm_group

section direct_sum
variables {ι : Type*} {π : ι → Type*} [decidable_eq ι] [Π i, add_comm_group (π i)] [comm_monoid R]

/-- Direct sum of additive characters. -/
protected def direct_sum (ψ : Π i, add_char (π i) R) : add_char (⨁ i, π i) R :=
add_char.to_add_monoid_hom.symm
  (direct_sum.to_add_monoid $ λ i, (ψ i).to_add_monoid_hom : (⨁ i, π i) →+ additive R)

lemma direct_sum_injective :
  injective (add_char.direct_sum : (Π i, add_char (π i) R) → add_char (⨁ i, π i) R) :=
begin
  refine add_char.to_add_monoid_hom.symm.injective.comp (direct_sum.to_add_monoid_injective.comp _),
  rintro ψ χ h,
  simpa [function.funext_iff] using h,
end

end direct_sum
end add_char
