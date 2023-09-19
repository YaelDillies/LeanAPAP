import Mathlib.Algebra.Group.Pi
import Mathlib.Algebra.Order.LatticeGroup

namespace Pi
variable {ι : Type*} {α : ι → Type*}

@[simp]
lemma abs_apply [∀ i, Neg (α i)] [∀ i, Sup (α i)] (f : ∀ i, α i) (i : ι) : |f| i = |f i| := rfl

@[simp]
lemma posPart_apply [∀ i, Lattice (α i)] [∀ i, AddCommGroup (α i)] (f : ∀ i, α i) (i : ι) :
    f⁺ i = (f i)⁺ := rfl

@[simp]
lemma negPart_apply [∀ i, Lattice (α i)] [∀ i, AddCommGroup (α i)] (f : ∀ i, α i) (i : ι) :
    f⁻ i = (f i)⁻ := rfl

lemma abs_def [∀ i, Neg (α i)] [∀ i, Sup (α i)] (f : ∀ i, α i) : |f| = λ i ↦ |f i| := rfl

lemma posPart_def [∀ i, Lattice (α i)] [∀ i, AddCommGroup (α i)] (f : ∀ i, α i) :
    f⁺ = λ i ↦ (f i)⁺ := rfl

lemma negPart_def [∀ i, Lattice (α i)] [∀ i, AddCommGroup (α i)] (f : ∀ i, α i) :
    f⁻ = λ i ↦ (f i)⁻ := rfl

end Pi

section Lattice
variable {α : Type*} [Lattice α] [AddCommGroup α] [CovariantClass α α (· + ·) (· ≤ ·)] {a : α}

open LatticeOrderedGroup

--TODO: Make `posPart` and `negPart` bind stronger than function application
--TODO: Strip off the notation typeclasses
--TODO: Fix the names
alias neg_sup := neg_sup_eq_neg_inf_neg
alias neg_inf := neg_inf_eq_sup_neg
alias posPart_def := pos_part_def
alias negPart_def := neg_part_def

@[simp] lemma posPart_of_nonneg (ha : 0 ≤ a) : a⁺ = a := pos_of_nonneg _ ha
@[simp] lemma posPart_of_nonpos (ha : a ≤ 0) : a⁺ = 0 := pos_of_nonpos _ ha
@[simp] lemma negPart_of_nonneg (ha : 0 ≤ a) : a⁻ = 0 := neg_of_nonneg _ ha
@[simp] lemma negPart_of_nonpos (ha : a ≤ 0) : a⁻ = -a := neg_of_nonpos _ ha

--TODO: Those lemmas already exist, but with shit names
@[simp] lemma posPart_neg (a : α) : (-a)⁺ = a⁻ := rfl
@[simp] lemma negPart_neg (a : α) : (-a)⁻ = a⁺ := by rw [posPart_def, negPart_def, neg_neg]
@[simp] lemma posPart_add_negPart (a : α) : a⁺ + a⁻ = |a| := (pos_add_neg _).symm
@[simp] lemma negPart_add_posPart (a : α) : a⁻ + a⁺ = |a| := by
  rw [add_comm, posPart_add_negPart]
@[simp] lemma posPart_sub_negPart (a : α) : a⁺ - a⁻ = a := pos_sub_neg _
@[simp] lemma negPart_sub_posPart (a : α) : a⁻ - a⁺ = -a := by
  rw [←neg_sub, posPart_sub_negPart]

lemma abs_add_eq_two_nsmul_posPart (a : α) : |a| + a = 2 • a⁺ := by
  rw [two_nsmul, ←add_add_sub_cancel (a⁺), posPart_add_negPart, posPart_sub_negPart]

lemma add_abs_eq_two_nsmul_posPart (a : α) : a + |a| = 2 • a⁺ := by
  rw [add_comm, abs_add_eq_two_nsmul_posPart]

lemma abs_sub_eq_two_nsmul_negPart (a : α) : |a| - a = 2 • a⁻ := by
  rw [two_nsmul, ←add_sub_sub_cancel, posPart_add_negPart, posPart_sub_negPart]

lemma sub_abs_eq_neg_two_nsmul_negPart (a : α) : a - |a| = -(2 • a⁻) := by
  rw [←abs_sub_eq_two_nsmul_negPart, neg_sub]

end Lattice

section LinearOrder
variable {α : Type*} [LinearOrder α] [AddCommGroup α] {a : α}

lemma posPart_eq_ite : a⁺ = ite (0 ≤ a) a 0 := by
  rw [←maxDefault, ←sup_eq_maxDefault]; simp_rw [sup_comm]; rfl

variable [CovariantClass α α (· + ·) (· ≤ ·)]

lemma negPart_eq_ite : a⁻ = ite (a ≤ 0) (-a) 0 := by
  simp_rw [←neg_nonneg]; rw [←maxDefault, ←sup_eq_maxDefault]; simp_rw [sup_comm]; rfl

end LinearOrder
