import Mathlib.Analysis.Normed.Group.Basic

section NormedAddCommGroup
variable {α : Type*} [NormedAddCommGroup α] {a b c : α}

lemma norm_sub_le_norm_sub_add_norm_sub : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ :=
  (norm_add_le _ _).trans_eq' $ by simp

end NormedAddCommGroup
