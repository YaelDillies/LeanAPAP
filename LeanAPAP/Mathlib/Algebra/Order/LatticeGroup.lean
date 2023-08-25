import Mathlib.Algebra.Group.Pi
import Mathlib.Algebra.Order.LatticeGroup

#align_import mathlib.algebra.order.lattice_group

namespace Pi
variable {ι : Type*} {α : ι → Type*}

@[simp]
lemma abs_apply [∀ i, Neg (α i)] [∀ i, Sup (α i)] (f : ∀ i, α i) (i : ι) : |f| i = |f i| := rfl

@[simp]
lemma pos_part_apply [∀ i, Lattice (α i)] [∀ i, AddCommGroup (α i)] (f : ∀ i, α i) (i : ι) :
    (f⁺) i = f i⁺ := rfl

@[simp]
lemma neg_part_apply [∀ i, Lattice (α i)] [∀ i, AddCommGroup (α i)] (f : ∀ i, α i) (i : ι) :
    (f⁻) i = f i⁻ := rfl

lemma abs_def [∀ i, Neg (α i)] [∀ i, Sup (α i)] (f : ∀ i, α i) : |f| = λ i => |f i| := rfl

lemma pos_part_def [∀ i, Lattice (α i)] [∀ i, AddCommGroup (α i)] (f : ∀ i, α i) :
    f⁺ = λ i => f i⁺ := rfl

lemma neg_part_def [∀ i, Lattice (α i)] [∀ i, AddCommGroup (α i)] (f : ∀ i, α i) :
    f⁻ = λ i => f i⁻ := rfl

end Pi

section Lattice
variable {α : Type*} [Lattice α] [AddCommGroup α] [CovariantClass α α (· + ·) (· ≤ ·)] {a : α}

open LatticeOrderedCommGroup

--TODO: Make `pos_part` and `neg_part` bind stronger than function application
--TODO: Strip off the notation typeclasses
--TODO: Fix the names
alias neg_sup := neg_sup_eq_neg_inf_neg

alias neg_inf := neg_inf_eq_sup_neg

@[simp]
lemma pos_part_of_nonneg (ha : 0 ≤ a) : a⁺ = a :=
  pos_of_nonneg _ ha

@[simp]
lemma pos_part_of_nonpos (ha : a ≤ 0) : a⁺ = 0 :=
  pos_of_nonpos _ ha

@[simp]
lemma neg_part_of_nonneg (ha : 0 ≤ a) : a⁻ = 0 :=
  neg_of_nonneg _ ha

@[simp]
lemma neg_part_of_nonpos (ha : a ≤ 0) : a⁻ = -a :=
  neg_of_nonpos _ ha

--TODO: Those lemmas already exist, but with shit names
@[simp]
lemma pos_part_neg (a : α) : (-a)⁺ = a⁻ := rfl

@[simp]
lemma neg_part_neg (a : α) : (-a)⁻ = a⁺ := by rw [pos_part_def, neg_part_def, neg_neg]

@[simp]
lemma pos_part_add_neg_part (a : α) : a⁺ + a⁻ = |a| :=
  (pos_add_neg _).symm

@[simp]
lemma neg_part_add_pos_part (a : α) : a⁻ + a⁺ = |a| := by rw [add_comm, pos_part_add_neg_part]

@[simp]
lemma pos_part_sub_neg_part (a : α) : a⁺ - a⁻ = a :=
  pos_sub_neg _

@[simp]
lemma neg_part_sub_pos_part (a : α) : a⁻ - a⁺ = -a := by rw [← neg_sub, pos_part_sub_neg_part]

lemma abs_add_eq_two_nsmul_pos_part (a : α) : |a| + a = 2 • a⁺ := by
  rw [two_nsmul, ← add_add_sub_cancel (a⁺), pos_part_add_neg_part, pos_part_sub_neg_part]

lemma add_abs_eq_two_nsmul_pos_part (a : α) : a + |a| = 2 • a⁺ := by
  rw [add_comm, abs_add_eq_two_nsmul_pos_part]

lemma abs_sub_eq_two_nsmul_neg_part (a : α) : |a| - a = 2 • a⁻ := by
  rw [two_nsmul, ← add_sub_sub_cancel, pos_part_add_neg_part, pos_part_sub_neg_part]

lemma sub_abs_eq_neg_two_nsmul_neg_part (a : α) : a - |a| = -(2 • a⁻) := by
  rw [← abs_sub_eq_two_nsmul_neg_part, neg_sub]

end Lattice

section LinearOrder
variable {α : Type*} [LinearOrder α] [AddCommGroup α] {a : α}

lemma pos_part_eq_ite : a⁺ = ite (0 ≤ a) a 0 := by
  rw [← maxDefault, ← sup_eq_maxDefault, sup_comm] <;> rfl

variable [CovariantClass α α (· + ·) (· ≤ ·)]

lemma neg_part_eq_ite : a⁻ = ite (a ≤ 0) (-a) 0 := by
  simp_rw [← neg_nonneg] <;> rw [← maxDefault, ← sup_eq_maxDefault, sup_comm] <;> rfl

end LinearOrder
