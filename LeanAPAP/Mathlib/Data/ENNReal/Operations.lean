import Mathlib.Data.ENNReal.Operations

namespace ENNReal
variable {a b c : ℝ≥0∞}

protected lemma sub_eq_of_eq_add' (ha : a ≠ ∞) (h : a = c + b) : a - b = c :=
  ENNReal.sub_eq_of_eq_add (mt (by rintro rfl; simpa using h) ha) h

protected lemma eq_sub_of_add_eq' (hb : b ≠ ∞) (h : a + c = b) : a = b - c :=
  ENNReal.eq_sub_of_add_eq (mt (by rintro rfl; simpa [eq_comm] using h) hb) h

protected lemma sub_eq_of_eq_add_rev' (ha : a ≠ ∞) (h : a = b + c) : a - b = c :=
  ENNReal.sub_eq_of_eq_add_rev (mt (by rintro rfl; simpa using h) ha) h

end ENNReal
