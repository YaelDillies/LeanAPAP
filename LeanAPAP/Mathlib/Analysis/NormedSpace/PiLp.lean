import Mathlib.Analysis.NormedSpace.PiLp

#align_import mathlib.analysis.normed_space.pi_Lp

open scoped ENNReal

namespace PiLp
variable {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, NormedAddCommGroup (β i)] {p : ℝ≥0∞}
  {x y : ∀ i, β i}

instance addCommGroup [∀ i, AddCommGroup (β i)] : AddCommGroup (PiLp p β) :=
  { Pi.addCommGroup with }

@[simp]
lemma equiv_zero' : PiLp.equiv p β 0 = 0 := rfl

@[simp]
lemma equiv_symm_zero' : (PiLp.equiv p β).symm 0 = 0 := rfl

@[simp]
lemma equiv_add' : PiLp.equiv p β (x + y) = PiLp.equiv p β x + PiLp.equiv p β y := rfl

@[simp]
lemma equiv_symm_add' :
    (PiLp.equiv p β).symm (x + y) = (PiLp.equiv p β).symm x + (PiLp.equiv p β).symm y := rfl

@[simp]
lemma equiv_sub' : PiLp.equiv p β (x - y) = PiLp.equiv p β x - PiLp.equiv p β y := rfl

@[simp]
lemma equiv_symm_sub' :
    (PiLp.equiv p β).symm (x - y) = (PiLp.equiv p β).symm x - (PiLp.equiv p β).symm y := rfl

@[simp]
lemma equiv_neg' : PiLp.equiv p β (-x) = -PiLp.equiv p β x := rfl

@[simp]
lemma equiv_symm_neg' : (PiLp.equiv p β).symm (-x) = -(PiLp.equiv p β).symm x := rfl

end PiLp
