import Mathbin.Analysis.Normed.Group.Basic

#align_import mathlib.analysis.normed.group.basic

section NormedAddCommGroup

variable {α : Type _} [NormedAddCommGroup α] {a b c : α}

theorem norm_sub_le_norm_sub_add_norm_sub : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ :=
  (norm_add_le _ _).trans_eq' <| by simp

end NormedAddCommGroup

