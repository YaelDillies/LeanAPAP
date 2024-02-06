import Mathlib.Algebra.Algebra.Basic
import LeanAPAP.Prereqs.NNRat.Defs

/-!
# Casts for nonnegative rational numbers

We define the canonical injection from ℚ≥0 into an arbitrary division semiring and prove various
casting lemmas showing the well-behavedness of this injection.
-/

open scoped NNRat

section defs
variable {α β : Type*}

-- TODO: Make fields of `Field` for definitional equalities

instance [DivisionSemiring α] : NNRatCast α where nnratCast q := q.num / q.den

-- TODO: Do the `NNRat.cast` refactor to let this be an instance
-- instance [Mul α] [NNRatCast α] : SMul ℚ≥0 α where smul q a := q * a

-- TODO: Get rid of this
class CompAction (α : Type*) [Mul α] [NNRatCast α] [SMul ℚ≥0 α] : Prop :=
  nnqsmul_eq_mul' (q : ℚ≥0) (a : α) : q • a = q * a

namespace NNRat

lemma smul_def [Mul α] [NNRatCast α] [SMul ℚ≥0 α] [CompAction α] (q : ℚ≥0) (a : α) :
    q • a = q * a := CompAction.nnqsmul_eq_mul' _ _

lemma smul_one_eq_cast [MulOneClass α] [NNRatCast α] [SMul ℚ≥0 α] [CompAction α] (q : ℚ≥0) :
    q • (1 : α) = q := by rw [smul_def, mul_one]

end NNRat

end defs

variable {F ι α β : Type*}

namespace NNRat

open NNRat

section DivisionSemiring
variable [DivisionSemiring α] [Module ℚ≥0 α] {p q : ℚ≥0}

lemma cast_def (q : ℚ≥0) : (q : α) = q.num / q.den := rfl

@[simp, norm_cast] lemma cast_natCast (n : ℕ) : ((n : ℚ≥0) : α) = n := by simp [cast_def]

-- See note [no_index around OfNat.ofNat]
@[simp, norm_cast] lemma cast_ofNat (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n : ℚ≥0) : α) = OfNat.ofNat n := cast_natCast _

@[simp, norm_cast] lemma cast_zero : ((0 : ℚ≥0) : α) = 0 := (cast_natCast _).trans Nat.cast_zero
@[simp, norm_cast] lemma cast_one : ((1 : ℚ≥0) : α) = 1 := (cast_natCast _).trans Nat.cast_one

lemma cast_commute (q : ℚ≥0) (a : α) : Commute ↑q a := by
  simpa only [cast_def] using (q.num.cast_commute a).div_left (q.den.cast_commute a)

lemma cast_comm (q : ℚ≥0) (a : α) : q * a = a * q := cast_commute _ _
lemma commute_cast (a : α) (r : ℚ≥0) : Commute a r := (cast_commute _ _).symm

-- @[norm_cast]
-- lemma cast_mk_of_ne_zero (a b : ℤ) (b0 : (b : α) ≠ 0) : (a /. b : α) = a / b := by
--   have b0' : b ≠ 0 := by
--     refine' mt _ b0
--     simp (config := { contextual := true })
--   cases' e : a /. b with n d h c
--   have d0 : (d : α) ≠ 0 := by
--     intro d0
--     have dd := den_dvd a b
--     cases' show (d : ℤ) ∣ b by rwa [e] at dd with k ke
--     have : (b : α) = (d : α) * (k : α) := by rw [ke, Int.cast_mul, Int.cast_ofNat]
--     rw [d0, zero_mul] at this
--     contradiction
--   rw [num_den'] at e
--   have := congr_arg ((↑) : ℤ → α)
--     ((divInt_eq_iff b0' <| ne_of_gt <| Int.coe_nat_pos.2 h.bot_lt).1 e)
--   rw [Int.cast_mul, Int.cast_mul, Int.cast_ofNat] at this
--   -- Porting note: was `symm`
--   apply Eq.symm
--   rw [cast_def, div_eq_mul_inv, eq_div_iff_mul_eq d0, mul_assoc, (d.commute_cast _).eq, ← mul_assoc,
--     this, mul_assoc, mul_inv_cancel b0, mul_one]

@[norm_cast]
lemma cast_add_of_ne_zero (hp : (p.den : α) ≠ 0) (hq : (q.den : α) ≠ 0) :
    (p + q : ℚ≥0) = (p + q : α) := by
  simp_rw [cast_def]
  sorry

-- @[norm_cast]
-- lemma cast_add_of_ne_zero :
--     ∀ {m n : ℚ≥0}, (m.den : α) ≠ 0 → (n.den : α) ≠ 0 → ((m + n : ℚ≥0) : α) = m + n
--   | ⟨n₁, d₁, h₁, c₁⟩, ⟨n₂, d₂, h₂, c₂⟩ => fun (d₁0 : (d₁ : α) ≠ 0) (d₂0 : (d₂ : α) ≠ 0) => by
--     have d₁0' : (d₁ : ℤ) ≠ 0 :=
--       Int.coe_nat_ne_zero.2 fun e => by rw [e] at d₁0; exact d₁0 Nat.cast_zero
--     have d₂0' : (d₂ : ℤ) ≠ 0 :=
--       Int.coe_nat_ne_zero.2 fun e => by rw [e] at d₂0; exact d₂0 Nat.cast_zero
--     rw [num_den', num_den', add_def'' d₁0' d₂0']
--     suffices (n₁ * (d₂ * ((d₂ : α)⁻¹ * (d₁ : α)⁻¹)) + n₂ * (d₁ * (d₂ : α)⁻¹) * (d₁ : α)⁻¹ : α)
--         = n₁ * (d₁ : α)⁻¹ + n₂ * (d₂ : α)⁻¹ by
--       rw [cast_mk_of_ne_zero, cast_mk_of_ne_zero, cast_mk_of_ne_zero]
--       · simpa [division_def, left_distrib, right_distrib, mul_inv_rev, d₁0, d₂0, mul_assoc]
--       all_goals simp [d₁0, d₂0]
--     rw [← mul_assoc (d₂ : α), mul_inv_cancel d₂0, one_mul, (Nat.cast_commute _ _).eq]
--     simp [d₁0, mul_assoc]

@[norm_cast]
lemma cast_mul_of_ne_zero (hp : (p.den : α) ≠ 0) (hq : (q.den : α) ≠ 0) :
    (p * q : ℚ≥0) = (p * q : α) := sorry

-- @[norm_cast]
-- lemma cast_mul_of_ne_zero :
--     ∀ {p q : ℚ≥0}, (p.den : α) ≠ 0 → (q.den : α) ≠ 0 → ((p * q : ℚ≥0) : α) = p * q
--   | ⟨n₁, d₁, h₁, c₁⟩, ⟨n₂, d₂, h₂, c₂⟩ => fun (d₁0 : (d₁ : α) ≠ 0) (d₂0 : (d₂ : α) ≠ 0) => by
--     have d₁0' : (d₁ : ℤ) ≠ 0 :=
--       Int.coe_nat_ne_zero.2 fun e => by rw [e] at d₁0; exact d₁0 Nat.cast_zero
--     have d₂0' : (d₂ : ℤ) ≠ 0 :=
--       Int.coe_nat_ne_zero.2 fun e => by rw [e] at d₂0; exact d₂0 Nat.cast_zero
--     rw [num_den', num_den', mul_def' d₁0' d₂0']
--     suffices (n₁ * (n₂ * (d₂ : α)⁻¹ * (d₁ : α)⁻¹) : α) = n₁ * ((d₁ : α)⁻¹ * (n₂ * (d₂ : α)⁻¹)) by
--       rw [cast_mk_of_ne_zero, cast_mk_of_ne_zero, cast_mk_of_ne_zero]
--       · simpa [division_def, mul_inv_rev, d₁0, d₂0, mul_assoc]
--       all_goals simp [d₁0, d₂0]
--     rw [(d₁.commute_cast (_ : α)).inv_right₀.eq]

@[norm_cast]
lemma cast_inv_of_ne_zero (hp : (p.den : α) ≠ 0) : (p⁻¹ : ℚ≥0) = (p⁻¹ : α) := sorry

-- @[norm_cast]
-- lemma cast_inv_of_ne_zero :
--     ∀ {q : ℚ≥0}, (q.num : α) ≠ 0 → (q.den : α) ≠ 0 → ((n⁻¹ : ℚ≥0) : α) = (q : α)⁻¹
--   | ⟨q, d, h, c⟩ => fun (n0 : (q : α) ≠ 0) (d0 : (d : α) ≠ 0) => by
--     have _ : (q : ℤ) ≠ 0 := fun e => by rw [e] at n0; exact n0 Int.cast_zero
--     have _ : (d : ℤ) ≠ 0 :=
--       Int.coe_nat_ne_zero.2 fun e => by rw [e] at d0; exact d0 Nat.cast_zero
--     rw [num_den', inv_def']
--     rw [cast_mk_of_ne_zero, cast_mk_of_ne_zero, inv_div] <;> simp [n0, d0]

@[norm_cast]
lemma cast_div_of_ne_zero (hp : (p.den : α) ≠ 0) (hq : (q.den : α) ≠ 0) :
    (p / q : ℚ≥0) = (p / q : α) := sorry

-- @[norm_cast]
-- lemma cast_div_of_ne_zero {p q : ℚ≥0} (md : (p.den : α) ≠ 0) (nn : (q.num : α) ≠ 0)
--     (nd : (q.den : α) ≠ 0) : ((p / q : ℚ≥0) : α) = p / q := by
--   have : (n⁻¹.den : ℤ) ∣ q.num := by
--     conv in n⁻¹.den => rw [← @num_den q, inv_def']
--     apply den_dvd
--   have : (n⁻¹.den : α) = 0 → (q.num : α) = 0 := fun h => by
--     let ⟨k, e⟩ := this
--     have := congr_arg ((↑) : ℤ → α) e; rwa [Int.cast_mul, Int.cast_ofNat, h, zero_mul] at this
--   rw [division_def, cast_mul_of_ne_zero md (mt this nn), cast_inv_of_ne_zero nn nd, division_def]

end DivisionSemiring

instance [DivisionRing α] [CharZero α] : CompAction α where
  nnqsmul_eq_mul' q a := (Rat.smul_def _ _).trans $ by
    simp [NNRat.cast_def, Rat.cast_def, NNRat.num_coe]

-- Porting note: statement made more explicit
@[norm_cast] lemma cast_id (n : ℚ≥0) : NNRat.cast n = n := rfl
@[simp] lemma cast_eq_id : ((↑) : ℚ≥0 → ℚ≥0) = id := rfl

end NNRat

open NNRat

@[simp] lemma map_nnratCast [DivisionSemiring α] [DivisionSemiring β] [FunLike F α β]
    [RingHomClass F α β] (f : F) (q : ℚ≥0) : f q = q := by simp_rw [cast_def, map_div₀, map_natCast]

-- TODO: This proof will change once the diamond for `NNRatCast ℚ≥0` is fixed
@[simp]
lemma eq_nnratCast [DivisionSemiring α] [FunLike F ℚ≥0 α] [RingHomClass F ℚ≥0 α] (f : F) (r : ℚ≥0) :
    f r = r := by rw [← map_nnratCast f]; congr; symm; exact num_div_den _

namespace MonoidWithZeroHom
variable {M₀ : Type*} [MonoidWithZero M₀] [FunLike F ℚ≥0 M₀] [MonoidWithZeroHomClass F ℚ≥0 M₀]
  {f g : F}

/-- If `f` and `g` agree on the naturals then they are equal `φ`. -/
lemma ext_nnrat' (h : ∀ n : ℕ, f n = g n) : f = g :=
  (DFunLike.ext f g) fun r => by
    rw [← r.num_div_den, div_eq_mul_inv, map_mul, map_mul, h, eq_on_inv₀ f g]
    apply h

/-- If `f` and `g` agree on the integers then they are equal `φ`.

See note [partially-applied ext lemmas] for why `comp` is used here. -/
@[ext]
lemma ext_nnrat {f g : ℚ≥0 →*₀ M₀}
    (h : f.comp (Nat.castRingHom ℚ≥0 : ℕ →*₀ ℚ≥0) = g.comp (Nat.castRingHom ℚ≥0)) : f = g :=
  ext_nnrat' <| DFunLike.congr_fun h

-- /-- Positive integer values of a morphism `φ` and its value on `-1` completely determine `φ`. -/
-- lemma ext_nnrat_on_pnat (same_on_pnat : ∀ n : ℕ, 0 < n → f n = g n) : f = g :=
--   ext_nnrat' <| FunLike.congr_fun <|
--       show
--         (f : ℚ≥0 →*₀ M₀).comp (Nat.castRingHom ℚ≥0 : ℕ →*₀ ℚ≥0) =
--           (g : ℚ≥0 →*₀ M₀).comp (Nat.castRingHom ℚ≥0 : ℕ →*₀ ℚ≥0)
--         from ext_nat'' (by simpa) (by simpa) (same_on_pnat _)

end MonoidWithZeroHom

-- /-- Any two ring homomorphisms from `ℚ≥0` to a semiring are equal. If the codomain is a division ring,
-- then this lemma follows from `eq_ratCast`. -/
-- lemma RingHom.ext_nnrat {R : Type*} [Semiring R] [RingHomClass F ℚ≥0 R] (f g : F) : f = g :=
--   MonoidWithZeroHom.ext_nnrat' <| RingHom.congr_fun <|
--       ((f : ℚ≥0 →+* R).comp (Nat.castRingHom ℚ≥0)).ext_nat ((g : ℚ≥0 →+* R).comp (Nat.castRingHom ℚ≥0))

-- instance NNRat.subsingleton_ringHom {R : Type*} [Semiring R] : Subsingleton (ℚ≥0 →+* R) :=
--   ⟨RingHom.ext_rat⟩

section SMul
namespace NNRat
variable {α : Type*} [DivisionSemiring α] [SMul ℚ≥0 α] [CompAction α]

instance (priority := 100) instDistribSMul : DistribSMul ℚ≥0 α where
  smul := (· • ·)
  smul_zero a := by rw [smul_def, mul_zero]
  smul_add a x y := by rw [smul_def, smul_def, smul_def, mul_add]

instance isScalarTower_right : IsScalarTower ℚ≥0 α α :=
  ⟨fun a x y ↦ by simp only [smul_def, smul_eq_mul, mul_assoc]⟩

end NNRat
end SMul
