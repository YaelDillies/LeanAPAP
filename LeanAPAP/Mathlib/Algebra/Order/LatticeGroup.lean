import Mathbin.Algebra.Group.Pi
import Mathbin.Algebra.Order.LatticeGroup

#align_import mathlib.algebra.order.lattice_group

namespace Pi

variable {ι : Type _} {α : ι → Type _}

@[simp]
theorem abs_apply [∀ i, Neg (α i)] [∀ i, Sup (α i)] (f : ∀ i, α i) (i : ι) : |f| i = |f i| :=
  rfl

@[simp]
theorem pos_part_apply [∀ i, Lattice (α i)] [∀ i, AddCommGroup (α i)] (f : ∀ i, α i) (i : ι) :
    (f⁺) i = f i⁺ :=
  rfl

@[simp]
theorem neg_part_apply [∀ i, Lattice (α i)] [∀ i, AddCommGroup (α i)] (f : ∀ i, α i) (i : ι) :
    (f⁻) i = f i⁻ :=
  rfl

theorem abs_def [∀ i, Neg (α i)] [∀ i, Sup (α i)] (f : ∀ i, α i) : |f| = fun i => |f i| :=
  rfl

theorem pos_part_def [∀ i, Lattice (α i)] [∀ i, AddCommGroup (α i)] (f : ∀ i, α i) :
    f⁺ = fun i => f i⁺ :=
  rfl

theorem neg_part_def [∀ i, Lattice (α i)] [∀ i, AddCommGroup (α i)] (f : ∀ i, α i) :
    f⁻ = fun i => f i⁻ :=
  rfl

end Pi

section Lattice

variable {α : Type _} [Lattice α] [AddCommGroup α] [CovariantClass α α (· + ·) (· ≤ ·)] {a : α}

open LatticeOrderedCommGroup

--TODO: Make `pos_part` and `neg_part` bind stronger than function application
--TODO: Strip off the notation typeclasses
--TODO: Fix the names
alias neg_sup := neg_sup_eq_neg_inf_neg

alias neg_inf := neg_inf_eq_sup_neg

@[simp]
theorem pos_part_of_nonneg (ha : 0 ≤ a) : a⁺ = a :=
  pos_of_nonneg _ ha

@[simp]
theorem pos_part_of_nonpos (ha : a ≤ 0) : a⁺ = 0 :=
  pos_of_nonpos _ ha

@[simp]
theorem neg_part_of_nonneg (ha : 0 ≤ a) : a⁻ = 0 :=
  neg_of_nonneg _ ha

@[simp]
theorem neg_part_of_nonpos (ha : a ≤ 0) : a⁻ = -a :=
  neg_of_nonpos _ ha

--TODO: Those lemmas already exist, but with shit names
@[simp]
theorem pos_part_neg (a : α) : (-a)⁺ = a⁻ :=
  rfl

@[simp]
theorem neg_part_neg (a : α) : (-a)⁻ = a⁺ := by rw [pos_part_def, neg_part_def, neg_neg]

@[simp]
theorem pos_part_add_neg_part (a : α) : a⁺ + a⁻ = |a| :=
  (pos_add_neg _).symm

@[simp]
theorem neg_part_add_pos_part (a : α) : a⁻ + a⁺ = |a| := by rw [add_comm, pos_part_add_neg_part]

@[simp]
theorem pos_part_sub_neg_part (a : α) : a⁺ - a⁻ = a :=
  pos_sub_neg _

@[simp]
theorem neg_part_sub_pos_part (a : α) : a⁻ - a⁺ = -a := by rw [← neg_sub, pos_part_sub_neg_part]

theorem abs_add_eq_two_nsmul_pos_part (a : α) : |a| + a = 2 • a⁺ := by
  rw [two_nsmul, ← add_add_sub_cancel (a⁺), pos_part_add_neg_part, pos_part_sub_neg_part]

theorem add_abs_eq_two_nsmul_pos_part (a : α) : a + |a| = 2 • a⁺ := by
  rw [add_comm, abs_add_eq_two_nsmul_pos_part]

theorem abs_sub_eq_two_nsmul_neg_part (a : α) : |a| - a = 2 • a⁻ := by
  rw [two_nsmul, ← add_sub_sub_cancel, pos_part_add_neg_part, pos_part_sub_neg_part]

theorem sub_abs_eq_neg_two_nsmul_neg_part (a : α) : a - |a| = -(2 • a⁻) := by
  rw [← abs_sub_eq_two_nsmul_neg_part, neg_sub]

end Lattice

section LinearOrder

variable {α : Type _} [LinearOrder α] [AddCommGroup α] {a : α}

theorem pos_part_eq_ite : a⁺ = ite (0 ≤ a) a 0 := by
  rw [← maxDefault, ← sup_eq_maxDefault, sup_comm] <;> rfl

variable [CovariantClass α α (· + ·) (· ≤ ·)]

theorem neg_part_eq_ite : a⁻ = ite (a ≤ 0) (-a) 0 := by
  simp_rw [← neg_nonneg] <;> rw [← maxDefault, ← sup_eq_maxDefault, sup_comm] <;> rfl

end LinearOrder

