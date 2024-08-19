import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Tactic.Nontriviality

variable {α M₀ G₀ : Type*}

section MulOneClass
variable [Zero M₀] [MulOneClass M₀] [Preorder M₀] {a b : M₀}

lemma one_lt_of_lt_mul_left₀ [PosMulReflectLT M₀] (ha : 0 ≤ a) (h : a < a * b) : 1 < b :=
  lt_of_mul_lt_mul_left (by simpa) ha

lemma one_lt_of_lt_mul_right₀ [MulPosReflectLT M₀] (hb : 0 ≤ b) (h : b < a * b) : 1 < a :=
  lt_of_mul_lt_mul_right (by simpa) hb

lemma one_le_of_le_mul_left₀ [PosMulReflectLE M₀] (ha : 0 < a) (h : a ≤ a * b) : 1 ≤ b :=
  le_of_mul_le_mul_left (by simpa) ha

lemma one_le_of_le_mul_right₀ [MulPosReflectLE M₀] (hb : 0 < b) (h : b ≤ a * b) : 1 ≤ a :=
  le_of_mul_le_mul_right (by simpa) hb

end MulOneClass

section MonoidWithZero
variable [MonoidWithZero M₀]

section Preorder
variable [Preorder M₀] {a b c d : M₀}

@[simp] lemma pow_nonneg' [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 0 ≤ a) : ∀ n, 0 ≤ a ^ n
  | 0 => pow_zero a ▸ zero_le_one
  | n + 1 => pow_succ a n ▸ mul_nonneg (pow_nonneg' ha _) ha

lemma pow_le_pow_of_le_one'' [ZeroLEOneClass M₀] [PosMulMono M₀] [MulPosMono M₀] (ha₀ : 0 ≤ a)
    (ha₁ : a ≤ 1) : ∀ {m n : ℕ}, m ≤ n → a ^ n ≤ a ^ m
  | _, _, Nat.le.refl => le_rfl
  | _, _, Nat.le.step h => by
    rw [pow_succ']
    exact (mul_le_of_le_one_left (pow_nonneg' ha₀ _) ha₁).trans <| pow_le_pow_of_le_one'' ha₀ ha₁ h

lemma pow_le_of_le_one' [ZeroLEOneClass M₀] [PosMulMono M₀] [MulPosMono M₀]
    (h₀ : 0 ≤ a) (h₁ : a ≤ 1) {n : ℕ} (hn : n ≠ 0) : a ^ n ≤ a :=
  (pow_one a).subst (pow_le_pow_of_le_one'' h₀ h₁ (Nat.pos_of_ne_zero hn))

lemma sq_le' [ZeroLEOneClass M₀] [PosMulMono M₀] [MulPosMono M₀] (h₀ : 0 ≤ a) (h₁ : a ≤ 1) :
    a ^ 2 ≤ a := pow_le_of_le_one' h₀ h₁ two_ne_zero

lemma one_le_mul_of_one_le_of_one_le' [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 ≤ a)
    (hb : 1 ≤ b) : (1 : M₀) ≤ a * b :=
  Left.one_le_mul_of_le_of_le ha hb <| zero_le_one.trans ha

lemma mul_le_one'' [ZeroLEOneClass M₀] [PosMulMono M₀] [MulPosMono M₀] (ha : a ≤ 1) (hb' : 0 ≤ b)
    (hb : b ≤ 1) : a * b ≤ 1 := one_mul (1 : M₀) ▸ mul_le_mul ha hb hb' zero_le_one

lemma one_lt_mul_of_le_of_lt'' [ZeroLEOneClass M₀] [MulPosMono M₀] (ha : 1 ≤ a) (hb : 1 < b) :
    1 < a * b := hb.trans_le <| le_mul_of_one_le_left (zero_le_one.trans hb.le) ha

lemma one_lt_mul_of_lt_of_le'' [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 < a) (hb : 1 ≤ b) :
    1 < a * b := ha.trans_le <| le_mul_of_one_le_right (zero_le_one.trans ha.le) hb

alias one_lt_mul''' := one_lt_mul_of_le_of_lt''

lemma mul_lt_one_of_nonneg_of_lt_one_left' [PosMulMono M₀] (ha₀ : 0 ≤ a) (ha : a < 1) (hb : b ≤ 1) :
    a * b < 1 := (mul_le_of_le_one_right ha₀ hb).trans_lt ha

lemma mul_lt_one_of_nonneg_of_lt_one_right' [MulPosMono M₀] (ha : a ≤ 1) (hb₀ : 0 ≤ b) (hb : b < 1) :
    a * b < 1 := (mul_le_of_le_one_left hb₀ ha).trans_lt hb

variable [Preorder α] {f g : α → M₀}

lemma monotone_mul_left_of_nonneg' [PosMulMono M₀] (ha : 0 ≤ a) : Monotone fun x ↦ a * x :=
  fun _ _ h ↦ mul_le_mul_of_nonneg_left h ha

lemma monotone_mul_right_of_nonneg' [MulPosMono M₀] (ha : 0 ≤ a) : Monotone fun x ↦ x * a :=
  fun _ _ h ↦ mul_le_mul_of_nonneg_right h ha

lemma Monotone.mul_const'' [MulPosMono M₀] (hf : Monotone f) (ha : 0 ≤ a) :
    Monotone fun x ↦ f x * a := (monotone_mul_right_of_nonneg' ha).comp hf

lemma Monotone.const_mul'' [PosMulMono M₀] (hf : Monotone f) (ha : 0 ≤ a) :
    Monotone fun x ↦ a * f x := (monotone_mul_left_of_nonneg' ha).comp hf

lemma Antitone.mul_const'' [MulPosMono M₀] (hf : Antitone f) (ha : 0 ≤ a) :
    Antitone fun x ↦ f x * a := (monotone_mul_right_of_nonneg' ha).comp_antitone hf

lemma Antitone.const_mul'' [PosMulMono M₀] (hf : Antitone f) (ha : 0 ≤ a) :
    Antitone fun x ↦ a * f x := (monotone_mul_left_of_nonneg' ha).comp_antitone hf

lemma Monotone.mul'' [PosMulMono M₀] [MulPosMono M₀] (hf : Monotone f) (hg : Monotone g)
    (hf₀ : ∀ x, 0 ≤ f x) (hg₀ : ∀ x, 0 ≤ g x) : Monotone (f * g) :=
  fun _ _ h ↦ mul_le_mul (hf h) (hg h) (hg₀ _) (hf₀ _)

end Preorder


section PartialOrder
variable [PartialOrder M₀] {a b c d : M₀}

@[simp] lemma pow_pos' [ZeroLEOneClass M₀] [PosMulStrictMono M₀] (ha : 0 < a) : ∀ n, 0 < a ^ n
  | 0 => by nontriviality; rw [pow_zero]; exact zero_lt_one
  | n + 1 => pow_succ a _ ▸ mul_pos (pow_pos' ha _) ha

lemma mul_self_lt_mul_self' [PosMulStrictMono M₀] [MulPosMono M₀] (ha : 0 ≤ a) (hab : a < b) :
    a * a < b * b := mul_lt_mul' hab.le hab ha <| ha.trans_lt hab

-- In the next lemma, we used to write `Set.Ici 0` instead of `{x | 0 ≤ x}`.
-- As this lemma is not used outside this file,
-- and the import for `Set.Ici` is not otherwise needed until later,
-- we choose not to use it here.
lemma strictMonoOn_mul_self' [PosMulStrictMono M₀] [MulPosMono M₀] :
    StrictMonoOn (fun x ↦ x * x) {x : M₀ | 0 ≤ x} := fun _ hx _ _ hxy ↦ mul_self_lt_mul_self' hx hxy

-- See Note [decidable namespace]
protected lemma Decidable.mul_lt_mul''' [PosMulMono M₀] [PosMulStrictMono M₀] [MulPosStrictMono M₀]
    [@DecidableRel M₀ (· ≤ ·)] (h1 : a < c) (h2 : b < d)
    (h3 : 0 ≤ a) (h4 : 0 ≤ b) : a * b < c * d :=
  h4.lt_or_eq_dec.elim (fun b0 ↦ mul_lt_mul h1 h2.le b0 <| h3.trans h1.le) fun b0 ↦ by
    rw [← b0, mul_zero]; exact mul_pos (h3.trans_lt h1) (h4.trans_lt h2)

lemma lt_mul_left' [MulPosStrictMono M₀] (ha : 0 < a) (hb : 1 < b) : a < b * a := by
  simpa using mul_lt_mul_of_pos_right hb ha

lemma lt_mul_right' [PosMulStrictMono M₀] (ha : 0 < a) (hb : 1 < b) : a < a * b := by
  simpa using mul_lt_mul_of_pos_left hb ha

lemma lt_mul_self' [ZeroLEOneClass M₀] [MulPosStrictMono M₀] (ha : 1 < a) : a < a * a :=
  lt_mul_left' (ha.trans_le' zero_le_one) ha

variable [Preorder α] {f g : α → M₀}

lemma strictMono_mul_left_of_pos' [PosMulStrictMono M₀] (ha : 0 < a) :
    StrictMono fun x ↦ a * x := fun _ _ b_lt_c ↦ mul_lt_mul_of_pos_left b_lt_c ha

lemma strictMono_mul_right_of_pos' [MulPosStrictMono M₀] (ha : 0 < a) :
    StrictMono fun x ↦ x * a := fun _ _ b_lt_c ↦ mul_lt_mul_of_pos_right b_lt_c ha

lemma StrictMono.mul_const'' [MulPosStrictMono M₀] (hf : StrictMono f) (ha : 0 < a) :
    StrictMono fun x ↦ f x * a := (strictMono_mul_right_of_pos' ha).comp hf

lemma StrictMono.const_mul'' [PosMulStrictMono M₀] (hf : StrictMono f) (ha : 0 < a) :
    StrictMono fun x ↦ a * f x := (strictMono_mul_left_of_pos' ha).comp hf

lemma StrictAnti.mul_const'' [MulPosStrictMono M₀] (hf : StrictAnti f) (ha : 0 < a) :
    StrictAnti fun x ↦ f x * a := (strictMono_mul_right_of_pos' ha).comp_strictAnti hf

lemma StrictAnti.const_mul'' [PosMulStrictMono M₀] (hf : StrictAnti f) (ha : 0 < a) :
    StrictAnti fun x ↦ a * f x := (strictMono_mul_left_of_pos' ha).comp_strictAnti hf

lemma StrictMono.mul_monotone'' [PosMulMono M₀] [MulPosStrictMono M₀] (hf : StrictMono f)
    (hg : Monotone g) (hf₀ : ∀ x, 0 ≤ f x) (hg₀ : ∀ x, 0 < g x) :
    StrictMono (f * g) := fun _ _ h ↦ mul_lt_mul (hf h) (hg h.le) (hg₀ _) (hf₀ _)

lemma Monotone.mul_strictMono'' [PosMulStrictMono M₀] [MulPosMono M₀] (hf : Monotone f)
    (hg : StrictMono g) (hf₀ : ∀ x, 0 < f x) (hg₀ : ∀ x, 0 ≤ g x) :
    StrictMono (f * g) := fun _ _ h ↦ mul_lt_mul' (hf h.le) (hg h) (hg₀ _) (hf₀ _)

lemma StrictMono.mul'' [PosMulStrictMono M₀] [MulPosStrictMono M₀] (hf : StrictMono f)
    (hg : StrictMono g) (hf₀ : ∀ x, 0 ≤ f x) (hg₀ : ∀ x, 0 ≤ g x) :
    StrictMono (f * g) := fun _ _ h ↦ mul_lt_mul'' (hf h) (hg h) (hf₀ _) (hg₀ _)

end MonoidWithZero.PartialOrder

section GroupWithZero
variable {G₀ : Type*} [GroupWithZero G₀]

section PartialOrder
variable [PartialOrder G₀] [ZeroLEOneClass G₀] [PosMulReflectLT G₀] {a b c : G₀}

-- TODO: Replace `inv_pos`
@[simp] lemma inv_pos' : 0 < a⁻¹ ↔ 0 < a :=
  suffices ∀ a : G₀, 0 < a → 0 < a⁻¹ from ⟨fun h ↦ inv_inv a ▸ this _ h, this a⟩
  fun a ha ↦ flip lt_of_mul_lt_mul_left ha.le <| by simp [ne_of_gt ha, zero_lt_one]

alias ⟨_, inv_pos_of_pos'⟩ := inv_pos'

@[simp] lemma inv_nonneg' : 0 ≤ a⁻¹ ↔ 0 ≤ a := by simp only [le_iff_eq_or_lt, inv_pos', zero_eq_inv]

alias ⟨_, inv_nonneg_of_nonneg'⟩ := inv_nonneg'

lemma one_div_pos' : 0 < 1 / a ↔ 0 < a := one_div a ▸ inv_pos'
lemma one_div_nonneg' : 0 ≤ 1 / a ↔ 0 ≤ a := one_div a ▸ inv_nonneg'

lemma div_pos' [PosMulStrictMono G₀] (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  rw [div_eq_mul_inv]; exact mul_pos ha (inv_pos'.2 hb)

lemma div_nonneg' [PosMulMono G₀] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b := by
  rw [div_eq_mul_inv]; exact mul_nonneg ha (inv_nonneg'.2 hb)

lemma div_nonpos_of_nonpos_of_nonneg' [MulPosMono G₀] (ha : a ≤ 0) (hb : 0 ≤ b) : a / b ≤ 0 := by
  rw [div_eq_mul_inv]; exact mul_nonpos_of_nonpos_of_nonneg ha (inv_nonneg'.2 hb)

lemma zpow_nonneg' [PosMulMono G₀] (ha : 0 ≤ a) : ∀ n : ℤ, 0 ≤ a ^ n
  | (n : ℕ) => by rw [zpow_natCast]; exact pow_nonneg' ha _
  |-(n + 1 : ℕ) => by rw [zpow_neg, inv_nonneg', zpow_natCast]; exact pow_nonneg' ha _

lemma zpow_pos_of_pos' [PosMulStrictMono G₀] (ha : 0 < a) : ∀ n : ℤ, 0 < a ^ n
  | (n : ℕ) => by rw [zpow_natCast]; exact pow_pos' ha _
  |-(n + 1 : ℕ) => by rw [zpow_neg, inv_pos', zpow_natCast]; exact pow_pos' ha _

lemma le_inv_mul_iff₀' [PosMulMono G₀] [MulPosMono G₀] (hc : 0 < c) : a ≤ c⁻¹ * b ↔ c * a ≤ b where
  mp h := by simpa [hc.ne'] using mul_le_mul_of_nonneg_left h hc.le
  mpr h := by simpa [hc.ne'] using mul_le_mul_of_nonneg_left h (inv_nonneg'.2 hc.le)

-- TODO: Replace `le_mul_inv_iff₀`
lemma le_mul_inv_iff₀' [PosMulMono G₀] [MulPosMono G₀] (hc : 0 < c) : a ≤ b * c⁻¹ ↔ a * c ≤ b where
  mp h := by simpa [hc.ne'] using mul_le_mul_of_nonneg_right h hc.le
  mpr h := by simpa [hc.ne'] using mul_le_mul_of_nonneg_right h (inv_nonneg'.2 hc.le)

lemma inv_mul_le_iff₀' [PosMulMono G₀] [MulPosMono G₀] (hc : 0 < c) : c⁻¹ * b ≤ a ↔ b ≤ c * a where
  mp h := by simpa [hc.ne'] using mul_le_mul_of_nonneg_left h hc.le
  mpr h := by simpa [hc.ne'] using mul_le_mul_of_nonneg_left h (inv_nonneg'.2 hc.le)

-- TODO: Replace `le_mul_inv_iff₀`
lemma mul_inv_le_iff₀' [PosMulMono G₀] [MulPosMono G₀] (hc : 0 < c) : b * c⁻¹ ≤ a ↔ b ≤ a * c where
  mp h := by simpa [hc.ne'] using mul_le_mul_of_nonneg_right h hc.le
  mpr h := by simpa [hc.ne'] using mul_le_mul_of_nonneg_right h (inv_nonneg'.2 hc.le)

end PartialOrder

section LinearOrder
variable [LinearOrder G₀] [ZeroLEOneClass G₀] [PosMulReflectLT G₀] {a b c : G₀}

@[simp] lemma inv_neg'' : a⁻¹ < 0 ↔ a < 0 := by simp only [← not_le, inv_nonneg']

@[simp] lemma inv_nonpos' : a⁻¹ ≤ 0 ↔ a ≤ 0 := by simp only [← not_lt, inv_pos']

lemma one_div_neg' : 1 / a < 0 ↔ a < 0 := one_div a ▸ inv_neg''
lemma one_div_nonpos' : 1 / a ≤ 0 ↔ a ≤ 0 := one_div a ▸ inv_nonpos'

lemma div_nonpos_of_nonneg_of_nonpos' [PosMulMono G₀] (ha : 0 ≤ a) (hb : b ≤ 0) : a / b ≤ 0 := by
  rw [div_eq_mul_inv]; exact mul_nonpos_of_nonneg_of_nonpos ha (inv_nonpos'.2 hb)

end GroupWithZero.LinearOrder
