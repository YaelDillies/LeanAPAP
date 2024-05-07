import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Real.NNReal
import LeanAPAP.Mathlib.Algebra.Field.Defs
import LeanAPAP.Prereqs.Expect.Basic
import LeanAPAP.Prereqs.Translate

open Finset Function
open Fintype (card)
open scoped BigOperators ComplexConjugate Pointwise NNRat

/-! ### Indicator -/

variable {ι α β γ : Type*} [DecidableEq α]

section Semiring
variable [Semiring β] [Semiring γ] {s : Finset α}

def indicate (s : Finset α) (a : α) : β := ite (a ∈ s) 1 0

notation "𝟭 " => indicate

notation "𝟭_[" β "] " => @indicate _ β _ _

lemma indicate_apply (x : α) : 𝟭_[β] s x = ite (x ∈ s) 1 0 := rfl

@[simp] lemma indicate_empty : (𝟭 ∅ : α → β) = 0 := by ext; simp [indicate]
@[simp] lemma indicate_univ [Fintype α] : (𝟭 Finset.univ : α → β) = 1 := by ext; simp [indicate]

lemma indicate_inter_apply (s t : Finset α) (x : α) : 𝟭_[β] (s ∩ t) x = 𝟭 s x * 𝟭 t x := by
  simp [indicate_apply, ←ite_and, and_comm]

lemma indicate_inter (s t : Finset α) : 𝟭_[β] (s ∩ t) = 𝟭 s * 𝟭 t :=
  funext $ indicate_inter_apply _ _

lemma map_indicate (f : β →+* γ) (s : Finset α) (x : α) : f (𝟭 s x) = 𝟭 s x :=
  RingHom.map_ite_one_zero _ _

variable (β)

@[simp] lemma indicate_image {α' : Type*} [DecidableEq α'] (e : α ≃ α') (s : Finset α) (a : α') :
    𝟭_[β] (s.image e) a = 𝟭 s (e.symm a) := by
  simp only [indicate, ←e.injective.mem_finset_image, Equiv.apply_symm_apply]

section Nontrivial
variable {β} [Nontrivial β] {a : α}

@[simp] lemma indicate_eq_zero : 𝟭_[β] s a = 0 ↔ a ∉ s := one_ne_zero.ite_eq_right_iff

lemma indicate_ne_zero : 𝟭_[β] s a ≠ 0 ↔ a ∈ s := one_ne_zero.ite_ne_right_iff

variable (β)

@[simp] lemma support_indicate : support (𝟭_[β] s) = s := by ext; exact indicate_ne_zero

end Nontrivial

lemma sum_indicate [Fintype α] (s : Finset α) : ∑ x, 𝟭_[β] s x = s.card := by simp [indicate_apply]

lemma card_eq_sum_indicate [Fintype α] (s : Finset α) : s.card = ∑ x, 𝟭_[ℕ] s x :=
  (sum_indicate _ _).symm

lemma translate_indicate [AddCommGroup α] (a : α) (s : Finset α) : τ a (𝟭_[β] s) = 𝟭 (a +ᵥ s) := by
  ext; simp [indicate_apply, ←neg_vadd_mem_iff, sub_eq_neg_add]

section AddGroup
variable {G : Type*} [AddGroup G] [AddAction G α]

@[simp]
lemma indicate_vadd (g : G) (s : Finset α) (a : α) : 𝟭_[β] (g +ᵥ s) a = 𝟭 s (-g +ᵥ a) :=
  if_congr neg_vadd_mem_iff.symm rfl rfl

end AddGroup

section Group
variable {G : Type*} [Group G] [MulAction G α]

@[to_additive existing, simp]
lemma indicate_smul (g : G) (s : Finset α) (a : α) : 𝟭_[β] (g • s) a = 𝟭 s (g⁻¹ • a) :=
  if_congr inv_smul_mem_iff.symm rfl rfl

end Group

section AddGroup
variable [AddGroup α]

@[simp]
lemma indicate_neg (s : Finset α) (a : α) : 𝟭_[β] (-s) a = 𝟭 s (-a) := if_congr mem_neg' rfl rfl

end AddGroup

section Group
variable [Group α]

@[to_additive existing, simp]
lemma indicate_inv (s : Finset α) (a : α) : 𝟭_[β] s⁻¹ a = 𝟭 s a⁻¹ := if_congr mem_inv' rfl rfl

end Group

variable {β}
variable [StarRing β]

lemma indicate_isSelfAdjoint (s : Finset α) : IsSelfAdjoint (𝟭_[β] s) :=
  Pi.isSelfAdjoint.2 fun g ↦ by rw [indicate]; split_ifs <;> simp

end Semiring

section CommSemiring
variable [CommSemiring β]

lemma indicate_inf_apply [Fintype α] (s : Finset ι) (t : ι → Finset α) (x : α) :
    𝟭_[β] (s.inf t) x = ∏ i in s, 𝟭 (t i) x := by simp [indicate_apply, mem_inf, prod_boole]

lemma indicate_inf [Fintype α] (s : Finset ι) (t : ι → Finset α) :
    𝟭_[β] (s.inf t) = ∏ i in s, 𝟭 (t i) :=
  funext fun x ↦ by rw [Finset.prod_apply, indicate_inf_apply]

variable [StarRing β]

@[simp] lemma conj_indicate_apply [AddCommGroup α] (s : Finset α) (a : α) :
    conj (𝟭_[β] s a) = 𝟭 s a := by simp [indicate_apply]

@[simp] lemma conj_indicate [AddCommGroup α] (s : Finset α) : conj (𝟭_[β] s) = 𝟭 s := by
  ext; simp

@[simp] lemma conjneg_indicate [AddCommGroup α] (s : Finset α) : conjneg (𝟭_[β] s) = 𝟭 (-s) := by
  ext; simp

end CommSemiring

section Semifield
variable [Fintype ι] [DecidableEq ι] [Semiring β] [Module ℚ≥0 β]

lemma expect_indicate (s : Finset ι) : 𝔼 x, 𝟭_[β] s x = s.card /ℚ Fintype.card ι := by
  simp only [expect_univ, indicate]
  rw [←sum_filter, filter_mem_eq_inter, univ_inter, sum_const, Nat.smul_one_eq_coe]

end Semifield

namespace NNReal
open scoped NNReal

@[simp, norm_cast] lemma coe_indicate (s : Finset α) (x : α) : ↑(𝟭_[ℝ≥0] s x) = 𝟭_[ℝ] s x :=
  map_indicate NNReal.toRealHom _ _

@[simp] lemma coe_comp_indicate (s : Finset α) : (↑) ∘ 𝟭_[ℝ≥0] s = 𝟭_[ℝ] s := by
  ext; exact coe_indicate _ _

end NNReal

namespace Complex

@[simp, norm_cast] lemma ofReal_indicate (s : Finset α) (x : α) : ↑(𝟭_[ℝ] s x) = 𝟭_[ℂ] s x :=
  map_indicate ofReal _ _

@[simp] lemma ofReal_comp_indicate (s : Finset α) : (↑) ∘ 𝟭_[ℝ] s = 𝟭_[ℂ] s := by
  ext; exact ofReal_indicate _ _

end Complex

section OrderedSemiring
variable [OrderedSemiring β] {s : Finset α}

@[simp] lemma indicate_nonneg : 0 ≤ 𝟭_[β] s := fun a ↦ by
  rw [indicate_apply]; split_ifs <;> norm_num

@[simp] lemma indicate_pos [Nontrivial β] : 0 < 𝟭_[β] s ↔ s.Nonempty := by
  simp [indicate_apply, Pi.lt_def, Function.funext_iff, lt_iff_le_and_ne, @eq_comm β 0,
    Finset.Nonempty]

protected alias ⟨_, Finset.Nonempty.indicate_pos⟩ := indicate_pos

end OrderedSemiring

/-! ### Normalised indicator -/

section DivisionSemiring
variable [DivisionSemiring β] [DivisionSemiring γ] {s : Finset α}

/-- The normalised indicate of a set. -/
def mu (s : Finset α) : α → β := (s.card : β)⁻¹ • 𝟭 s

notation "μ " => mu

notation "μ_[" β "] " => @mu _ β _ _

lemma mu_apply (x : α) : μ s x = (s.card : β)⁻¹ * ite (x ∈ s) 1 0 := rfl

@[simp] lemma mu_empty : (μ ∅ : α → β) = 0 := by ext; simp [mu]

lemma map_mu (f : β →+* γ) (s : Finset α) (x : α) : f (μ s x) = μ s x := by
  simp_rw [mu, Pi.smul_apply, smul_eq_mul, map_mul, map_indicate, map_inv₀, map_natCast]

section Nontrivial
variable [Nontrivial β] [CharZero β] {a : α}

@[simp] lemma mu_apply_eq_zero : μ_[β] s a = 0 ↔ a ∉ s := by
  simp only [mu_apply, mul_boole, ite_eq_right_iff, inv_eq_zero, Nat.cast_eq_zero, card_eq_zero]
  refine' imp_congr_right fun ha ↦ _
  simp only [ne_empty_of_mem ha]

lemma mu_apply_ne_zero : μ_[β] s a ≠ 0 ↔ a ∈ s := mu_apply_eq_zero.not_left

@[simp] lemma mu_eq_zero : μ_[β] s = 0 ↔ s = ∅ := by
  simp [Function.funext_iff, eq_empty_iff_forall_not_mem]

lemma mu_ne_zero : μ_[β] s ≠ 0 ↔ s.Nonempty := mu_eq_zero.not.trans nonempty_iff_ne_empty.symm

variable (β)

@[simp] lemma support_mu (s : Finset α) : support (μ_[β] s) = s := by
  ext; simpa [mu_apply, ne_empty_of_mem] using ne_empty_of_mem

end Nontrivial

variable (β)

lemma card_smul_mu [CharZero β] (s : Finset α) : s.card • μ_[β] s = 𝟭 s := by
  ext x : 1
  rw [Pi.smul_apply, mu_apply, indicate_apply, nsmul_eq_mul]
  split_ifs with h
  · rw [mul_one, mul_inv_cancel]
    rw [Nat.cast_ne_zero, ←pos_iff_ne_zero, Finset.card_pos]
    exact ⟨_, h⟩
  · rw [mul_zero, mul_zero]

lemma card_smul_mu_apply [CharZero β] (s : Finset α) (x : α) : s.card • μ_[β] s x = 𝟭 s x :=
  congr_fun (card_smul_mu β _) _

lemma sum_mu [CharZero β] [Fintype α] (hs : s.Nonempty) : ∑ x, μ_[β] s x = 1 := by
  simpa [mu_apply] using mul_inv_cancel (Nat.cast_ne_zero.2 hs.card_pos.ne')

lemma translate_mu [AddCommGroup α] (a : α) (s : Finset α) : τ a (μ_[β] s) = μ (a +ᵥ s) := by
  ext; simp [mu_apply, ←neg_vadd_mem_iff, sub_eq_neg_add]

section AddGroup
variable {G : Type*} [AddGroup G] [AddAction G α]

@[simp] lemma mu_vadd (g : G) (s : Finset α) (a : α) : μ_[β] (g +ᵥ s) a = μ s (-g +ᵥ a) := by
  simp [mu]

end AddGroup

section Group
variable {G : Type*} [Group G] [MulAction G α]

@[to_additive existing, simp]
lemma mu_smul (g : G) (s : Finset α) (a : α) : μ_[β] (g • s) a = μ s (g⁻¹ • a) := by simp [mu]

end Group

section AddGroup
variable [AddGroup α]

@[simp] lemma mu_neg (s : Finset α) (a : α) : μ_[β] (-s) a = μ s (-a) := by simp [mu]

end AddGroup

section Group
variable [Group α]

@[to_additive existing, simp]
lemma mu_inv (s : Finset α) (a : α) : μ_[β] s⁻¹ a = μ s a⁻¹ := by simp [mu]

end Group

end DivisionSemiring

section Semifield
variable (β) [Semifield β] {s : Finset α}

lemma expect_mu [CharZero β] [Fintype α] (hs : s.Nonempty) : 𝔼 x, μ_[β] s x = (↑(card α))⁻¹ := by
  rw [expect, card_univ, sum_mu _ hs, NNRat.smul_one_eq_cast, NNRat.cast_inv, NNRat.cast_natCast]

variable [StarRing β]

@[simp] lemma conj_mu_apply [AddCommGroup α] (s : Finset α) (a : α) :
    conj (μ_[β] s a) = μ s a := by simp [mu]

@[simp] lemma conj_mu [AddCommGroup α] (s : Finset α) : conj (μ_[β] s) = μ s := by
  ext; simp

@[simp] lemma conjneg_mu [AddCommGroup α] (s : Finset α) : conjneg (μ_[β] s) = μ (-s) := by
  ext; simp

end Semifield

namespace RCLike
variable {𝕜 : Type*} [RCLike 𝕜] [Fintype α] (s : Finset α) (a : α)

@[simp, norm_cast] lemma coe_mu : ↑(μ_[ℝ] s a) = μ_[𝕜] s a := map_mu (algebraMap ℝ 𝕜) _ _
@[simp] lemma coe_comp_mu : (↑) ∘ μ_[ℝ] s = μ_[𝕜] s := funext $ coe_mu _

end RCLike

namespace NNReal
open scoped NNReal

@[simp, norm_cast]
lemma coe_mu (s : Finset α) (x : α) : ↑(μ_[ℝ≥0] s x) = μ_[ℝ] s x := map_mu NNReal.toRealHom _ _

@[simp] lemma coe_comp_mu (s : Finset α) : (↑) ∘ μ_[ℝ≥0] s = μ_[ℝ] s := funext $ coe_mu _

end NNReal

section LinearOrderedSemifield
variable [LinearOrderedSemifield β] {s : Finset α}

@[simp] lemma mu_nonneg : 0 ≤ μ_[β] s := fun a ↦ by rw [mu_apply]; split_ifs <;> norm_num
@[simp] lemma mu_pos : 0 < μ_[β] s ↔ s.Nonempty := mu_nonneg.gt_iff_ne.trans mu_ne_zero

protected alias ⟨_, Finset.Nonempty.mu_pos⟩ := mu_pos

end LinearOrderedSemifield

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function

-- private abbrev TypeFunction (α β : Type*) := α → β

-- private alias ⟨_, mu_pos_of_nonempty⟩ := mu_pos
-- #check indicate
-- /-- Extension for the `positivity` tactic: an indicator is nonnegative, and positive if its support
-- is nonempty. -/
-- @[positivity indicate _]
-- def evalIndicate : PositivityExt where eval {u π} zπ pπ e := do
--   let u1 ← mkFreshLevelMVar
--   let u2 ← mkFreshLevelMVar
--   let _ : u =QL max u1 u2 := ⟨⟩
--   match π, e with
--   | ~q(TypeFunction.{u2, u1} $α $β), ~q(@indicate _ _ $instα $instβ $s) =>
--     let so : Option Q(Finset.Nonempty $s) ← do -- TODO: It doesn't complain if we make a typo?
--       try
--         let _fi ← synthInstanceQ q(Fintype $α)
--         let _no ← synthInstanceQ q(Nonempty $α)
--         match s with
--         | ~q(@univ _ $fi) => pure (some q(Finset.univ_nonempty (α := $α)))
--         | _ => pure none
--       catch _ => do
--         let .some fv ← findLocalDeclWithType? q(Finset.Nonempty $s) | pure none
--         pure (some (.fvar fv))
--     assumeInstancesCommute
--     match so with
--     | .some (fi : Q(Finset.Nonempty $s)) =>
--       try
--         let instβnontriv ← synthInstanceQ q(Nontrivial $β)
--         assumeInstancesCommute
--         return .positive q(Finset.Nonempty.indicate_pos $fi)
--       catch _ => return .nonnegative q(indicate_nonneg.{u, u_1})

--     | none => return .nonnegative q(indicate_nonneg.{u, u_1})
--   | _ => throwError "not Finset.indicate"

-- TODO: Fix

-- /-- Extension for the `positivity` tactic: multiplication is nonnegative/positive/nonzero if both
-- multiplicands are. -/
-- @[positivity]
-- unsafe def positivity_indicate : expr → tactic strictness
--   | e@q(@indicate $(α) $(β) $(hα) $(hβ) $(s)) ↦
--     (do
--         let p ←to_expr ``(Finset.Nonempty $(s)) >>= find_assumption
--         positive <$> mk_mapp `` indicate_pos_of_nonempty [α, β, none, none, none, none, p]) $>
--       do
--       nonnegative <$> mk_mapp `` indicate_nonneg [α, β, none, none, s]
--   | e@q(@mu $(α) $(β) $(hβ) $(hα) $(s)) ↦
--     (do
--         let p ←to_expr ``(Finset.Nonempty $(s)) >>= find_assumption
--         positive <$> mk_app `` mu_pos_of_nonempty [p]) $>
--       nonnegative <$> mk_mapp `` mu_nonneg [α, β, none, none, s]
--   | e ↦ pp e >>= fail ∘ format.bracket "The expression `"
--       "` isn't of the form `𝟭_[β] s` or `μ_[β] s`"

variable [LinearOrderedField β] {s : Finset α}

-- example : 0 ≤ 𝟭_[β] s := by positivity
-- example : 0 ≤ μ_[β] s := by positivity
-- example (hs : s.Nonempty) : 0 < 𝟭_[β] s := by positivity
-- example (hs : s.Nonempty) : 0 < μ_[β] s := by positivity

end Mathlib.Meta.Positivity
