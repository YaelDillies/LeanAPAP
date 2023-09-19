import Mathlib.Analysis.NormedSpace.PiLp

open scoped ENNReal

namespace PiLp
variable {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, NormedAddCommGroup (β i)] {p : ℝ≥0∞}
  {x y : ∀ i, β i}

instance addCommGroup [∀ i, AddCommGroup (β i)] : AddCommGroup (PiLp p β) :=
  { Pi.addCommGroup with }

@[simp] lemma equiv_zero' : WithLp.equiv p (∀ i, β i) 0 = 0 := rfl
@[simp] lemma equiv_symm_zero' : (WithLp.equiv p (∀ i, β i)).symm 0 = 0 := rfl

@[simp] lemma equiv_add' :
    WithLp.equiv p (∀ i, β i) (x + y) = WithLp.equiv p _ x + WithLp.equiv p _ y := rfl

@[simp] lemma equiv_symm_add' :
    (WithLp.equiv p (∀ i, β i)).symm (x + y) =
      (WithLp.equiv p _).symm x + (WithLp.equiv p _).symm y := rfl

@[simp] lemma equiv_sub' :
  WithLp.equiv p (∀ i, β i) (x - y) = WithLp.equiv p _ x - WithLp.equiv p _ y := rfl

@[simp] lemma equiv_symm_sub' :
    (WithLp.equiv p (∀ i, β i)).symm (x - y) =
      (WithLp.equiv p _).symm x - (WithLp.equiv p _).symm y := rfl

@[simp] lemma equiv_neg' : WithLp.equiv p (∀ i, β i) (-x) = -WithLp.equiv p _ x := rfl

@[simp]
lemma equiv_symm_neg' : (WithLp.equiv p (∀ i, β i)).symm (-x) = -(WithLp.equiv p _).symm x := rfl

end PiLp
