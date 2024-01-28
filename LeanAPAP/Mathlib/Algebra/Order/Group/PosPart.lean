import Mathlib.Algebra.Group.Pi
import Mathlib.Algebra.Order.Group.PosPart

namespace Pi
variable {ι : Type*} {α : ι → Type*}

@[simp]
lemma posPart_apply [∀ i, Lattice (α i)] [∀ i, AddCommGroup (α i)] (f : ∀ i, α i) (i : ι) :
    f⁺ i = (f i)⁺ := rfl

@[simp]
lemma negPart_apply [∀ i, Lattice (α i)] [∀ i, AddCommGroup (α i)] (f : ∀ i, α i) (i : ι) :
    f⁻ i = (f i)⁻ := rfl

lemma posPart_def [∀ i, Lattice (α i)] [∀ i, AddCommGroup (α i)] (f : ∀ i, α i) :
    f⁺ = fun i ↦ (f i)⁺ := rfl

lemma negPart_def [∀ i, Lattice (α i)] [∀ i, AddCommGroup (α i)] (f : ∀ i, α i) :
    f⁻ = fun i ↦ (f i)⁻ := rfl

end Pi

section Lattice
variable {α : Type*} [Lattice α] [AddCommGroup α] [CovariantClass α α (· + ·) (· ≤ ·)] {a : α}

attribute [simp] posPart_eq_self posPart_eq_zero negPart_eq_neg negPart_eq_zero

@[simp] lemma negPart_add_posPart (a : α) : a⁻ + a⁺ = |a| := by rw [add_comm, posPart_add_negPart]
@[simp] lemma negPart_sub_posPart (a : α) : a⁻ - a⁺ = -a := by rw [←neg_sub, posPart_sub_negPart]

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
