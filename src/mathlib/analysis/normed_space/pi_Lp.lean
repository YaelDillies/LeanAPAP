import analysis.normed_space.pi_Lp

open_locale ennreal

namespace pi_Lp
variables {ι : Type*} [fintype ι] {β : ι → Type*} [Π i, normed_add_comm_group (β i)] {p : ℝ≥0∞}
  {x y : Π i, β i}


instance add_comm_group [Π i, add_comm_group (β i)] : add_comm_group (pi_Lp p β) :=
{ ..pi.add_comm_group }

@[simp] lemma equiv_zero' : pi_Lp.equiv p β 0 = 0 := rfl
@[simp] lemma equiv_symm_zero' : (pi_Lp.equiv p β).symm 0 = 0 := rfl

@[simp] lemma equiv_add' :
  pi_Lp.equiv p β (x + y) = pi_Lp.equiv p β x + pi_Lp.equiv p β y := rfl
@[simp] lemma equiv_symm_add' :
  (pi_Lp.equiv p β).symm (x + y) = (pi_Lp.equiv p β).symm x + (pi_Lp.equiv p β).symm y := rfl

@[simp] lemma equiv_sub' : pi_Lp.equiv p β (x - y) = pi_Lp.equiv p β x - pi_Lp.equiv p β y := rfl
@[simp] lemma equiv_symm_sub' :
  (pi_Lp.equiv p β).symm (x - y) = (pi_Lp.equiv p β).symm x - (pi_Lp.equiv p β).symm y := rfl

@[simp] lemma equiv_neg' : pi_Lp.equiv p β (-x) = -pi_Lp.equiv p β x := rfl
@[simp] lemma equiv_symm_neg' : (pi_Lp.equiv p β).symm (-x) = -(pi_Lp.equiv p β).symm x := rfl

end pi_Lp
